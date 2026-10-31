module

public import HeightPaper.Probability.KernelIteration
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Martingale.Basic

/-!
# Infinite trajectories of the finite-support kernels

Ionescu--Tulcea supplies a single probability space carrying all times. Its
coordinate marginals are the existing PMF iterations, and its natural
filtration has the expected one-step conditional expectation. Thus infinite
martingale arguments can use the concrete finite kernels without a new law
being assumed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace HeightPaper.FinitePMF

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable def trajectoryStep (K : ℕ → α → PMF α)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure)) (k : ℕ) :
    Kernel (Finset.Iic k → α) α :=
  (toKernel (K k) (hm k)).comap (fun x ↦ x ⟨k, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance trajectoryStep_isMarkov (K : ℕ → α → PMF α)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure)) (k : ℕ) :
    IsMarkovKernel (trajectoryStep K hm k) := by
  constructor
  intro x
  change IsProbabilityMeasure (K k (x ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure
  infer_instance

noncomputable def kernelTrajectoryMeasure (K : ℕ → α → PMF α)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure)) (s₀ : α) :
    Measure (ℕ → α) := Kernel.traj (X := fun _ : ℕ ↦ α) (trajectoryStep K hm) 0 (fun _ ↦ s₀)

instance kernelTrajectoryMeasure_isProbability (K : ℕ → α → PMF α)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure)) (s₀ : α) :
    IsProbabilityMeasure (kernelTrajectoryMeasure K hm s₀) := by
  unfold kernelTrajectoryMeasure
  infer_instance

theorem kernelTrajectoryMeasure_map_eval (K : ℕ → α → PMF α)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure)) (s₀ : α) (k : ℕ) :
    (kernelTrajectoryMeasure K hm s₀).map (fun ω ↦ ω k) =
      (kernelEvolve (PMF.pure s₀) K k).toMeasure := by
  let κ := trajectoryStep K hm
  let μ := kernelTrajectoryMeasure K hm s₀
  have hprefix (j : ℕ) : μ.map (frestrictLe j) =
      Kernel.partialTraj (X := fun _ : ℕ ↦ α) κ 0 j (fun _ ↦ s₀) :=
    Kernel.traj_map_frestrictLe_apply (X := fun _ : ℕ ↦ α) (κ := κ) 0 j (fun _ ↦ s₀)
  induction k with
  | zero =>
      change μ.map (fun ω ↦ ω 0) = (PMF.pure s₀).toMeasure
      rw [PMF.toMeasure_pure]
      have he : (fun ω : ℕ → α ↦ ω 0) =
          (fun x : Finset.Iic 0 → α ↦ x ⟨0, by simp⟩) ∘ frestrictLe 0 := rfl
      rw [he, ← Measure.map_map
        (f := frestrictLe (π := fun _ : ℕ ↦ α) 0)
        (g := fun x : Finset.Iic 0 → α ↦ x ⟨0, by simp⟩)
        (measurable_pi_apply _) (measurable_frestrictLe _),
        hprefix, Kernel.partialTraj_self, Kernel.id_apply, Measure.map_dirac' (measurable_pi_apply _)]
  | succ k ih =>
      have hcompose : μ = Kernel.traj (X := fun _ : ℕ ↦ α) κ k ∘ₘ (μ.map (frestrictLe k)) := by
        rw [hprefix]
        exact (congrArg (fun η ↦ η (fun _ ↦ s₀))
          (Kernel.traj_comp_partialTraj (X := fun _ : ℕ ↦ α) (κ := κ) (Nat.zero_le k))).symm
      change μ.map (fun ω ↦ ω (k + 1)) = _
      calc
        _ = (Kernel.traj (X := fun _ : ℕ ↦ α) κ k).map (fun ω ↦ ω (k + 1)) ∘ₘ
            (μ.map (frestrictLe k)) := by
          conv_lhs => rw [hcompose]
          exact Measure.map_comp _ _ (measurable_pi_apply _)
        _ = κ k ∘ₘ (μ.map (frestrictLe k)) := by rw [Kernel.map_traj_succ_self (X := fun _ : ℕ ↦ α)]
        _ = toKernel (K k) (hm k) ∘ₘ (μ.map (fun ω ↦ ω k)) := by
          change (μ.map (frestrictLe k)).bind
              (fun x ↦ (K k (x ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure) =
            (μ.map (fun ω ↦ ω k)).bind (fun x ↦ (K k x).toMeasure)
          rw [Measure.bind_map (f := frestrictLe (π := fun _ : ℕ ↦ α) k)
              (g := fun x : Finset.Iic k → α ↦ (K k (x ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure)
              (measurable_frestrictLe _).aemeasurable
              ((hm k).comp (measurable_pi_apply _)).aemeasurable,
            Measure.bind_map (f := fun ω : ℕ → α ↦ ω k)
              (g := fun x ↦ (K k x).toMeasure)
              (measurable_pi_apply _).aemeasurable (hm k).aemeasurable]
          rfl
        _ = _ := by rw [ih, toKernel_comp]; rfl

theorem kernelTrajectory_integrable_eval {E : Type*} [NormedAddCommGroup E]
    (K : ℕ → α → PMF α)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure))
    (hK : ∀ k s, (K k s).support.Finite) (s₀ : α) (k : ℕ) (f : α → E) :
    Integrable (fun ω ↦ f (ω k)) (kernelTrajectoryMeasure K hm s₀) := by
  have hf := integrable_of_finite_support (kernelEvolve (PMF.pure s₀) K k)
    (kernelEvolve_support_finite _ K (by simp) hK k) f
  rw [← kernelTrajectoryMeasure_map_eval K hm s₀ k] at hf
  exact hf.comp_aemeasurable (measurable_pi_apply k).aemeasurable

theorem kernelTrajectory_ae_support_eval (K : ℕ → α → PMF α)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure)) (s₀ : α) (k : ℕ) :
    ∀ᵐ ω ∂kernelTrajectoryMeasure K hm s₀,
      ω k ∈ (kernelEvolve (PMF.pure s₀) K k).support := by
  have h := ae_of_forall_mem_support (kernelEvolve (PMF.pure s₀) K k)
    (fun _ hs ↦ hs)
  rw [← kernelTrajectoryMeasure_map_eval K hm s₀ k] at h
  exact ae_of_ae_map (measurable_pi_apply k).aemeasurable h

omit [MeasurableSingletonClass α] in
theorem measurable_piLE_eval (k : ℕ) :
    @Measurable (ℕ → α) α (Filtration.piLE k) _ (fun ω ↦ ω k) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_pi_apply (⟨k, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).comp
    (comap_measurable (frestrictLe k))

/-- The full trajectory filtration, reindexed after a fixed cutoff. -/
def trajectoryFiltrationFrom (J : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → α)) where
  seq k := Filtration.piLE (J + k)
  mono' := fun _ _ h ↦ Filtration.piLE.mono (Nat.add_le_add_left h J)
  le' := fun k ↦ Filtration.piLE.le (J + k)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The actual infinite-history conditional expectation of the next state. -/
theorem kernelTrajectory_condExp (K : ℕ → α → PMF α)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure))
    (hK : ∀ k s, (K k s).support.Finite) (s₀ : α) (k : ℕ)
    (f : α → E) (hf : Measurable f) :
    (kernelTrajectoryMeasure K hm s₀)[(fun ω ↦ f (ω (k + 1))) | Filtration.piLE k]
      =ᵐ[kernelTrajectoryMeasure K hm s₀]
      (fun ω ↦ ∫ s, f s ∂(K k (ω k)).toMeasure) := by
  have h := Kernel.condExp_traj (X := fun _ : ℕ ↦ α) (κ := trajectoryStep K hm) (x₀ := fun _ ↦ s₀) (Nat.zero_le k)
    (kernelTrajectory_integrable_eval K hm hK s₀ (k + 1) f)
  refine h.trans (Filter.Eventually.of_forall fun ω ↦ ?_)
  have he := congrArg (fun η ↦ η (frestrictLe k ω))
    (Kernel.map_traj_succ_self (X := fun _ : ℕ ↦ α) (κ := trajectoryStep K hm) (a := k))
  rw [Kernel.map_apply _ (measurable_pi_apply _)] at he
  change (∫ p, f (p (k + 1)) ∂Kernel.traj (X := fun _ : ℕ ↦ α) (trajectoryStep K hm) k (frestrictLe k ω)) = _
  rw [← integral_map (measurable_pi_apply _).aemeasurable hf.aestronglyMeasurable, he]
  rfl

/-- A one-step mean identity on the reachable support produces an infinite
martingale on the concrete trajectory space. -/
theorem kernelTrajectory_martingale (K : ℕ → α → PMF α)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure))
    (hK : ∀ k s, (K k s).support.Finite) (s₀ : α) (F : ℕ → α → E)
    (hFm : ∀ k, Measurable (F k))
    (hmean : ∀ k s, s ∈ (kernelEvolve (PMF.pure s₀) K k).support →
      (∫ t, F (k + 1) t ∂(K k s).toMeasure) = F k s) :
    Martingale (fun k ω ↦ F k (ω k)) Filtration.piLE (kernelTrajectoryMeasure K hm s₀) := by
  apply martingale_nat
  · intro k
    exact ((hFm k).comp (measurable_piLE_eval k)).stronglyMeasurable
  · intro k
    exact kernelTrajectory_integrable_eval K hm hK s₀ k (F k)
  · intro k
    apply Filter.EventuallyEq.symm
    apply (kernelTrajectory_condExp K hm hK s₀ k (F (k + 1)) (hFm (k + 1))).trans
    filter_upwards [kernelTrajectory_ae_support_eval K hm s₀ k] with ω hω
    exact hmean k (ω k) hω

/-- Starting after a cutoff preserves the original random prefix. -/
theorem kernelTrajectory_martingale_from (K : ℕ → α → PMF α)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure))
    (hK : ∀ k s, (K k s).support.Finite) (s₀ : α) (J : ℕ) (F : ℕ → α → E)
    (hFm : ∀ k, Measurable (F k))
    (hmean : ∀ k, J ≤ k → ∀ s, s ∈ (kernelEvolve (PMF.pure s₀) K k).support →
      (∫ t, F (k + 1) t ∂(K k s).toMeasure) = F k s) :
    Martingale (fun k ω ↦ F (J + k) (ω (J + k))) (trajectoryFiltrationFrom J)
      (kernelTrajectoryMeasure K hm s₀) := by
  apply martingale_nat
  · intro k
    exact ((hFm (J + k)).comp (measurable_piLE_eval (J + k))).stronglyMeasurable
  · intro k
    exact kernelTrajectory_integrable_eval K hm hK s₀ (J + k) (F (J + k))
  · intro k
    apply Filter.EventuallyEq.symm
    have h := kernelTrajectory_condExp K hm hK s₀ (J + k) (F (J + k + 1)) (hFm (J + k + 1))
    simp only [Nat.add_assoc] at h
    apply h.trans
    filter_upwards [kernelTrajectory_ae_support_eval K hm s₀ (J + k)] with ω hω
    exact hmean (J + k) (Nat.le_add_right J k) (ω (J + k)) hω

omit [CompleteSpace E] in
theorem kernelTrajectory_integral_eval (K : ℕ → α → PMF α)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure)) (s₀ : α) (k : ℕ)
    (f : α → E) (hf : Measurable f) :
    (∫ ω, f (ω k) ∂kernelTrajectoryMeasure K hm s₀) =
      ∫ s, f s ∂(kernelEvolve (PMF.pure s₀) K k).toMeasure := by
  rw [← kernelTrajectoryMeasure_map_eval K hm s₀ k]
  exact (integral_map (measurable_pi_apply k).aemeasurable hf.aestronglyMeasurable).symm

end HeightPaper.FinitePMF
