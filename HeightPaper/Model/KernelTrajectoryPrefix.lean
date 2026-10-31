module

public import HeightPaper.Probability.KernelTrajectory
public import HeightPaper.Model.KernelPath

/-! # Complete finite-prefix marginals of the infinite tree process -/

@[expose] public section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace HeightPaper.Model

private def treeCode : {n : ℕ} → Tree n → List ℕ
  | _, .root => []
  | _, .attach t p => p.val :: treeCode t

private theorem treeCode_injective {n : ℕ} : Function.Injective (@treeCode n) := by
  intro a b h
  induction a with
  | root =>
      cases b with
      | root => rfl
      | attach t p => exact Fin.elim0 p
  | @attach n t p ih =>
      cases b with
      | root => exact Fin.elim0 p
      | attach u q =>
          have hh : p.val = q.val ∧ treeCode t = treeCode u := List.cons.inj h
          have ht : t = u := ih hh.2
          have hp : p = q := Fin.ext hh.1
          rw [ht, hp]

instance countable_tree (n : ℕ) : Countable (Tree n) := treeCode_injective.countable

instance countable_state : Countable State := by
  let f : State → Σ n : ℕ, Tree n × Finset (Fin n) × ℕ :=
    fun s ↦ ⟨s.vertices, s.tree, s.active, s.susceptible⟩
  let g : (Σ n : ℕ, Tree n × Finset (Fin n) × ℕ) → State :=
    fun s ↦ ⟨s.1, s.2.1, s.2.2.1, s.2.2.2⟩
  exact (show Function.LeftInverse g f from fun _ ↦ rfl).injective.countable

instance countable_finitePath (N : ℕ) : Countable (FinitePath N) :=
  (show Function.Injective (FinitePath.state (steps := N)) from
    fun _p _q h ↦ FinitePath.ext (fun i ↦ congrFun h i)).countable

/-- The complete prefix, including time zero. -/
def trajectoryPrefix (N : ℕ) (ω : ℕ → State) : FinitePath N :=
  ⟨fun i ↦ ω i.val⟩

def pathFromIic (N : ℕ) (x : Finset.Iic N → State) : FinitePath N :=
  ⟨fun i ↦ x ⟨i.val, Finset.mem_Iic.mpr (by have := i.isLt; omega)⟩⟩

theorem measurable_trajectoryPrefix (N : ℕ) : Measurable (trajectoryPrefix N) :=
  (measurable_of_countable (pathFromIic N)).comp
    (measurable_frestrictLe (X := fun _ : ℕ ↦ State) N)

@[simp] theorem trajectoryPrefix_eval (N : ℕ) (ω : ℕ → State) (k : ℕ) (hk : k ≤ N) :
    (trajectoryPrefix N ω).eval k = ω k := by
  simp only [trajectoryPrefix, FinitePath.eval, Nat.min_eq_left hk]

@[simp] theorem trajectoryPrefix_last (N : ℕ) (ω : ℕ → State) :
    (trajectoryPrefix N ω).last = ω N := rfl

theorem trajectoryPrefix_succ (N : ℕ) (ω : ℕ → State) :
    trajectoryPrefix (N + 1) ω = (trajectoryPrefix N ω).append (ω (N + 1)) := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [trajectoryPrefix, FinitePath.append]
  · simp [trajectoryPrefix, FinitePath.append]

/-- All finite histories have the existing finite-kernel law, not merely the
correct one-time marginals. -/
theorem kernelTrajectoryMeasure_map_prefix (K : ℕ → State → PMF State)
    (s₀ : State) (N : ℕ) :
    (FinitePMF.kernelTrajectoryMeasure K (fun _ ↦ measurable_state _) s₀).map
      (trajectoryPrefix N) = kernelPathMeasure K s₀ N := by
  let hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure) := fun _ ↦ measurable_state _
  let κ := FinitePMF.trajectoryStep K hm
  let μ := FinitePMF.kernelTrajectoryMeasure K hm s₀
  change μ.map (trajectoryPrefix N) = _
  induction N with
  | zero =>
      have he : trajectoryPrefix 0 =
          (fun s : State ↦ (⟨fun _ ↦ s⟩ : FinitePath 0)) ∘ (fun ω ↦ ω 0) := by
        funext ω
        ext i
        have hi : i.val = 0 := by omega
        simp [trajectoryPrefix]
      rw [he, ← Measure.map_map (measurable_state _) (measurable_pi_apply _)]
      rw [show μ.map (fun ω ↦ ω 0) = (PMF.pure s₀).toMeasure from
        FinitePMF.kernelTrajectoryMeasure_map_eval K hm s₀ 0]
      simp only [kernelPathMeasure, kernelPathLaw, PMF.toMeasure_pure,
        Measure.map_dirac' (measurable_state _)]
  | succ N ih =>
      let a : (Finset.Iic N → State) × State → FinitePath (N + 1) :=
        fun z ↦ (pathFromIic N z.1).append z.2
      have ha : Measurable a := measurable_of_countable _
      have hpair : (μ.map (frestrictLe N)) ⊗ₘ κ N =
          μ.map (fun ω ↦ (frestrictLe N ω, ω (N + 1))) := by
        rw [show μ.map (frestrictLe N) =
            Kernel.partialTraj (X := fun _ : ℕ ↦ State) κ 0 N (fun _ ↦ s₀) from
          Kernel.traj_map_frestrictLe_apply (X := fun _ : ℕ ↦ State) (κ := κ) 0 N (fun _ ↦ s₀)]
        exact Kernel.partialTraj_compProd_eq_map_traj (X := fun _ : ℕ ↦ State)
          (κ := κ) (Nat.zero_le N)
      calc
        μ.map (trajectoryPrefix (N + 1)) =
            (μ.map (fun ω ↦ (frestrictLe N ω, ω (N + 1)))).map a := by
          rw [Measure.map_map ha ((measurable_frestrictLe N).prodMk (measurable_pi_apply _))]
          congr 1
          funext ω
          exact trajectoryPrefix_succ N ω
        _ = ((μ.map (frestrictLe N)) ⊗ₘ κ N).map a := by rw [hpair]
        _ = (μ.map (trajectoryPrefix N)).bind
            (fun p ↦ ((K N p.last).map p.append).toMeasure) := by
          rw [show trajectoryPrefix N = pathFromIic N ∘ frestrictLe N from rfl,
            ← Measure.map_map (f := frestrictLe (π := fun _ : ℕ ↦ State) N)
              (g := pathFromIic N) (measurable_of_countable _) (measurable_frestrictLe _),
            Measure.bind_map (measurable_of_countable _).aemeasurable
              (FinitePath.measurable _).aemeasurable]
          ext A hA
          rw [Measure.map_apply ha hA, Measure.compProd_apply (ha hA),
            Measure.bind_apply hA (measurable_of_countable
              (fun x : Finset.Iic N → State ↦
                ((K N (pathFromIic N x).last).map (pathFromIic N x).append).toMeasure)).aemeasurable]
          apply lintegral_congr
          intro x
          rw [← PMF.toMeasure_map _ _ (measurable_state _),
            Measure.map_apply (measurable_state _) hA]
          rfl
        _ = kernelPathMeasure K s₀ (N + 1) := by
          rw [ih]
          exact FinitePMF.toKernel_comp (kernelPathLaw K s₀ N)
            (fun p ↦ (K N p.last).map p.append) (FinitePath.measurable _)

/-- Prefix observables, including differences between two times, transfer
without changing their joint law. -/
theorem kernelTrajectory_integral_prefix {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (K : ℕ → State → PMF State) (s₀ : State) (N : ℕ) (f : FinitePath N → E) :
    (∫ ω, f (trajectoryPrefix N ω)
      ∂FinitePMF.kernelTrajectoryMeasure K (fun _ ↦ measurable_state _) s₀) =
      ∫ p, f p ∂kernelPathMeasure K s₀ N := by
  rw [← kernelTrajectoryMeasure_map_prefix K s₀ N]
  exact (integral_map (measurable_trajectoryPrefix N).aemeasurable
    (FinitePath.measurable f).aestronglyMeasurable).symm

end HeightPaper.Model
