module

public import HeightPaper.Model.PathMeasure
public import HeightPaper.Probability.FinitePMF
public import Mathlib.Probability.Martingale.Basic

/-!
# Finite histories for time-dependent state kernels

This construction supports prescribed infection/recovery events on one fixed
finite-horizon probability space, with the filtration of complete past histories.
-/

@[expose] public section

open MeasureTheory

namespace HeightPaper.Model

namespace FinitePath

/-- The history seen up to `k`, using the terminal state after the fixed horizon. -/
def prefixAt {N : ℕ} (p : FinitePath N) (k : ℕ) : FinitePath k :=
  ⟨fun i ↦ p.eval i.val⟩

@[simp] theorem prefixAt_last {N : ℕ} (p : FinitePath N) (k : ℕ) :
    (p.prefixAt k).last = p.eval k := rfl

theorem prefixAt_eval {N k i : ℕ} (p : FinitePath N) (hi : i ≤ k) :
    (p.prefixAt k).eval i = p.eval i := by
  simp only [eval, prefixAt, Nat.min_eq_left hi]

@[simp] theorem prefixAt_self {N : ℕ} (p : FinitePath N) : p.prefixAt N = p := by
  ext i
  change p.eval i.val = p.state i
  unfold eval
  congr 1
  exact Fin.ext (Nat.min_eq_left (by have := i.isLt; omega))

theorem prefixAt_comp {N i j : ℕ} (p : FinitePath N) (hij : i ≤ j) :
    (p.prefixAt j).prefixAt i = p.prefixAt i := by
  ext a
  exact p.prefixAt_eval (by have := a.isLt; omega)

@[simp] theorem prefixAt_succ_prefix {N : ℕ} (p : FinitePath N) (k : ℕ) :
    (p.prefixAt (k + 1)).prefixPath = p.prefixAt k := rfl

theorem prefixAt_append {N k : ℕ} (p : FinitePath N) (s : State) (hk : k ≤ N) :
    (p.append s).prefixAt k = p.prefixAt k := by
  ext i
  exact p.append_eval_of_le s (by have := i.isLt; omega)

theorem eval_of_ge {N k : ℕ} (p : FinitePath N) (hk : N ≤ k) : p.eval k = p.last := by
  unfold eval last
  congr 1
  exact Fin.ext (Nat.min_eq_right hk)

end FinitePath

/-- Joint history law for a time-dependent kernel. -/
noncomputable def kernelPathLaw (K : ℕ → State → PMF State) (s₀ : State) :
    (N : ℕ) → PMF (FinitePath N)
  | 0 => PMF.pure ⟨fun _ ↦ s₀⟩
  | k + 1 => (kernelPathLaw K s₀ k).bind fun p ↦ (K k p.last).map p.append

theorem finite_support_kernelPathLaw (K : ℕ → State → PMF State)
    (hK : ∀ k s, (K k s).support.Finite) (s₀ : State) (N : ℕ) :
    (kernelPathLaw K s₀ N).support.Finite := by
  induction N with
  | zero => rw [kernelPathLaw, PMF.support_pure]; exact Set.finite_singleton _
  | succ k ih =>
      exact FinitePMF.finite_support_bind _ _ ih fun p _ ↦
        FinitePMF.finite_support_map _ (hK k p.last) _

theorem kernelPathLaw_map_prefixAt (K : ℕ → State → PMF State) (s₀ : State)
    (N k : ℕ) (hk : k ≤ N) :
    (kernelPathLaw K s₀ N).map (fun p ↦ p.prefixAt k) = kernelPathLaw K s₀ k := by
  induction N with
  | zero =>
      have heq : k = 0 := by omega
      subst k
      rw [show (fun p : FinitePath 0 ↦ p.prefixAt 0) = id from funext (fun p ↦ p.prefixAt_self)]
      exact PMF.map_id _
  | succ N ih =>
      by_cases hkN : k ≤ N
      · rw [kernelPathLaw, PMF.map_bind]
        simp_rw [PMF.map_comp]
        have hf (p : FinitePath N) : (fun q : FinitePath (N + 1) ↦ q.prefixAt k) ∘ p.append =
            Function.const State (p.prefixAt k) := by
          funext s
          exact p.prefixAt_append s hkN
        simp_rw [hf, PMF.map_const]
        exact ih hkN
      · have heq : k = N + 1 := by omega
        subst k
        rw [show (fun p : FinitePath (N + 1) ↦ p.prefixAt (N + 1)) = id from
          funext (fun p ↦ p.prefixAt_self)]
        exact PMF.map_id _

noncomputable def kernelPathMeasure (K : ℕ → State → PMF State) (s₀ : State)
    (N : ℕ) : Measure (FinitePath N) := (kernelPathLaw K s₀ N).toMeasure

instance (K : ℕ → State → PMF State) (s₀ : State) (N : ℕ) :
    IsProbabilityMeasure (kernelPathMeasure K s₀ N) := by
  unfold kernelPathMeasure
  infer_instance

theorem kernelPathMeasure_map_prefixAt (K : ℕ → State → PMF State) (s₀ : State)
    (N k : ℕ) (hk : k ≤ N) :
    (kernelPathMeasure K s₀ N).map (fun p ↦ p.prefixAt k) = kernelPathMeasure K s₀ k := by
  rw [kernelPathMeasure, PMF.toMeasure_map _ _ (FinitePath.measurable _),
    kernelPathLaw_map_prefixAt K s₀ N k hk]
  rfl

theorem ae_mem_support_kernelPathLaw (K : ℕ → State → PMF State) (s₀ : State) (N : ℕ) :
    ∀ᵐ p ∂kernelPathMeasure K s₀ N, p ∈ (kernelPathLaw K s₀ N).support := by
  apply (ae_iff_prob_eq_one (FinitePath.measurable _)).mpr
  exact (PMF.toMeasure_apply_eq_one_iff _ (by trivial)).mpr (by intro p hp; exact hp)

section Integrals

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem integrable_kernelPathMeasure (K : ℕ → State → PMF State)
    (hK : ∀ k s, (K k s).support.Finite) (s₀ : State) (N : ℕ) (f : FinitePath N → E) :
    Integrable f (kernelPathMeasure K s₀ N) :=
  FinitePMF.integrable_of_finite_support _ (finite_support_kernelPathLaw K hK s₀ N) f

theorem kernelPathMeasure_integral_succ (K : ℕ → State → PMF State)
    (hK : ∀ k s, (K k s).support.Finite) (s₀ : State) (k : ℕ)
    (f : FinitePath (k + 1) → E) :
    ∫ p, f p ∂kernelPathMeasure K s₀ (k + 1) =
      ∫ p, ∫ s, f (p.append s) ∂(K k p.last).toMeasure ∂kernelPathMeasure K s₀ k := by
  rw [kernelPathMeasure, kernelPathLaw]
  rw [FinitePMF.integral_bind_of_finite_support _ _ (FinitePath.measurable _)
    (finite_support_kernelPathLaw K hK s₀ k)
    (fun p _ ↦ FinitePMF.finite_support_map _ (hK k p.last) _) f]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [← PMF.toMeasure_map _ _ (measurable_state _),
    integral_map_of_stronglyMeasurable (measurable_state _) (FinitePath.measurable f).stronglyMeasurable]

theorem kernelPathMeasure_integral_prefixAt (K : ℕ → State → PMF State) (s₀ : State)
    (N k : ℕ) (hk : k ≤ N) (f : FinitePath k → E) :
    ∫ p, f (p.prefixAt k) ∂kernelPathMeasure K s₀ N =
      ∫ p, f p ∂kernelPathMeasure K s₀ k := by
  rw [← integral_map_of_stronglyMeasurable (FinitePath.measurable _)
    (FinitePath.measurable f).stronglyMeasurable, kernelPathMeasure_map_prefixAt K s₀ N k hk]

end Integrals

/-- The canonical filtration generated by complete histories through each time. -/
def pathFiltration (N : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (FinitePath N)) where
  seq k := (inferInstance : MeasurableSpace (FinitePath k)).comap (fun p ↦ p.prefixAt k)
  mono' := by
    intro i j hij A hA
    obtain ⟨B, _, rfl⟩ := hA
    refine ⟨(fun p : FinitePath j ↦ p.prefixAt i) ⁻¹' B, trivial, ?_⟩
    ext p
    simp only [Set.mem_preimage, FinitePath.prefixAt_comp p hij]
  le' := fun _ ↦ le_top

section Martingale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The conditional expectation of the next observation, given the entire
past history, is its kernel expectation. The equality only needs verification
on reachable histories. -/
theorem kernelPath_condExp (K : ℕ → State → PMF State)
    (hK : ∀ k s, (K k s).support.Finite) (s₀ : State) (N k : ℕ) (hk : k < N)
    (F G : State → E)
    (hF : ∀ p ∈ (kernelPathLaw K s₀ k).support,
      (∫ s, F s ∂(K k p.last).toMeasure) = G p.last) :
    (fun p ↦ G (p.eval k)) =ᵐ[kernelPathMeasure K s₀ N]
      (kernelPathMeasure K s₀ N)[(fun p ↦ F (p.eval (k + 1))) | pathFiltration N k] := by
  classical
  apply ae_eq_condExp_of_forall_setIntegral_eq (pathFiltration N |>.le k)
    (integrable_kernelPathMeasure K hK s₀ N _)
  · intro A _ _
    exact (integrable_kernelPathMeasure K hK s₀ N (fun p ↦ G (p.eval k))).integrableOn
  · intro A hA _
    obtain ⟨B, _, rfl⟩ := hA
    rw [← integral_indicator (show MeasurableSet ((fun p : FinitePath N ↦ p.prefixAt k) ⁻¹' B)
        from trivial),
      ← integral_indicator (show MeasurableSet ((fun p : FinitePath N ↦ p.prefixAt k) ⁻¹' B)
        from trivial)]
    let G₀ : FinitePath (k + 1) → E := fun q ↦
      B.indicator (fun p : FinitePath k ↦ G p.last) q.prefixPath
    let G₁ : FinitePath (k + 1) → E := fun q ↦
      if q.prefixPath ∈ B then F q.last else 0
    have hleft :
        (fun p : FinitePath N ↦ ((fun p : FinitePath N ↦ p.prefixAt k) ⁻¹' B).indicator
          (fun p ↦ G (p.eval k)) p) = fun p ↦ G₀ (p.prefixAt (k + 1)) := by
      funext p
      simp only [G₀, Set.indicator, Set.mem_preimage,
        FinitePath.prefixAt_succ_prefix, FinitePath.prefixAt_last]
      split_ifs with h <;> simp [h]
    have hright :
        (fun p : FinitePath N ↦ ((fun p : FinitePath N ↦ p.prefixAt k) ⁻¹' B).indicator
          (fun p ↦ F (p.eval (k + 1))) p) = fun p ↦ G₁ (p.prefixAt (k + 1)) := by
      funext p
      simp only [G₁, Set.indicator, Set.mem_preimage,
        FinitePath.prefixAt_succ_prefix, FinitePath.prefixAt_last]
      split_ifs with h <;> simp [h]
    rw [hleft, hright, kernelPathMeasure_integral_prefixAt K s₀ N (k + 1) (by omega),
      kernelPathMeasure_integral_prefixAt K s₀ N (k + 1) (by omega),
      kernelPathMeasure_integral_succ K hK s₀ k G₀,
      kernelPathMeasure_integral_succ K hK s₀ k G₁]
    apply integral_congr_ae
    filter_upwards [ae_mem_support_kernelPathLaw K s₀ k] with p hp
    by_cases hpB : p ∈ B
    · simp only [G₀, G₁, FinitePath.prefix_append, FinitePath.append_last,
        Set.indicator_of_mem hpB, hpB, ↓reduceIte, integral_const, probReal_univ, one_smul]
      exact (hF p hp).symm
    · simp only [G₀, G₁, FinitePath.prefix_append,
        Set.indicator_of_notMem hpB, hpB, ↓reduceIte, integral_zero]
  · apply StronglyMeasurable.aestronglyMeasurable
    apply Measurable.stronglyMeasurable
    intro A hA
    refine ⟨(fun p : FinitePath k ↦ G p.last) ⁻¹' A, trivial, ?_⟩
    ext p
    simp only [Set.mem_preimage, FinitePath.prefixAt_last]

/-- A zero-drift state observable produces a genuine martingale on the fixed
finite-history probability space with its canonical past-history filtration.
After the finite horizon the process and filtration are kept constant. -/
theorem kernelPath_martingale (K : ℕ → State → PMF State)
    (hK : ∀ k s, (K k s).support.Finite) (s₀ : State) (N : ℕ) (F : ℕ → State → E)
    (hF : ∀ k < N, ∀ p ∈ (kernelPathLaw K s₀ k).support,
      (∫ s, F (k + 1) s ∂(K k p.last).toMeasure) = F k p.last) :
    Martingale (fun k p ↦ F (min k N) (p.eval k)) (pathFiltration N)
      (kernelPathMeasure K s₀ N) := by
  classical
  apply martingale_of_setIntegral_eq_succ
  · intro k
    apply Measurable.stronglyMeasurable
    intro A hA
    refine ⟨(fun p : FinitePath k ↦ F (min k N) p.last) ⁻¹' A, trivial, ?_⟩
    ext p
    simp only [Set.mem_preimage, FinitePath.prefixAt_last]
  · intro k
    exact integrable_kernelPathMeasure K hK s₀ N _
  · intro k A hA
    by_cases hk : k < N
    · obtain ⟨B, _, rfl⟩ := hA
      rw [← integral_indicator (show MeasurableSet ((fun p : FinitePath N ↦ p.prefixAt k) ⁻¹' B)
          from trivial),
        ← integral_indicator (show MeasurableSet ((fun p : FinitePath N ↦ p.prefixAt k) ⁻¹' B)
          from trivial)]
      let G₀ : FinitePath (k + 1) → E := fun q ↦
        B.indicator (fun p : FinitePath k ↦ F k p.last) q.prefixPath
      let G₁ : FinitePath (k + 1) → E := fun q ↦
        if q.prefixPath ∈ B then F (k + 1) q.last else 0
      have hleft :
          (fun p : FinitePath N ↦ ((fun p : FinitePath N ↦ p.prefixAt k) ⁻¹' B).indicator
            (fun p ↦ F (min k N) (p.eval k)) p) = fun p ↦ G₀ (p.prefixAt (k + 1)) := by
        funext p
        simp only [G₀, Set.indicator, Set.mem_preimage, Nat.min_eq_left hk.le,
          FinitePath.prefixAt_succ_prefix, FinitePath.prefixAt_last]
        split_ifs with h <;> simp [h]
      have hright :
          (fun p : FinitePath N ↦ ((fun p : FinitePath N ↦ p.prefixAt k) ⁻¹' B).indicator
            (fun p ↦ F (min (k + 1) N) (p.eval (k + 1))) p) =
            fun p ↦ G₁ (p.prefixAt (k + 1)) := by
        funext p
        simp only [G₁, Set.indicator, Set.mem_preimage, Nat.min_eq_left (show k + 1 ≤ N by omega),
          FinitePath.prefixAt_succ_prefix, FinitePath.prefixAt_last]
        split_ifs with h <;> simp [h]
      rw [hleft, hright, kernelPathMeasure_integral_prefixAt K s₀ N (k + 1) (by omega),
        kernelPathMeasure_integral_prefixAt K s₀ N (k + 1) (by omega),
        kernelPathMeasure_integral_succ K hK s₀ k G₀,
        kernelPathMeasure_integral_succ K hK s₀ k G₁]
      apply integral_congr_ae
      filter_upwards [ae_mem_support_kernelPathLaw K s₀ k] with p hp
      by_cases hpB : p ∈ B
      · simp only [G₀, G₁, FinitePath.prefix_append, FinitePath.append_last,
          Set.indicator_of_mem hpB, hpB, ↓reduceIte, integral_const, probReal_univ, one_smul]
        exact (hF k hk p hp).symm
      · simp only [G₀, G₁, FinitePath.prefix_append,
          Set.indicator_of_notMem hpB, hpB, ↓reduceIte, integral_zero]
    · have hkN : N ≤ k := by omega
      have hkN' : N ≤ k + 1 := by omega
      simp only [Nat.min_eq_right hkN, Nat.min_eq_right hkN',
        FinitePath.eval_of_ge _ hkN, FinitePath.eval_of_ge _ hkN']

end Martingale

end HeightPaper.Model
