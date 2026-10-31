module

public import HeightPaper.Probability.CorrectedCouplingAcceptanceCover
public import HeightPaper.Probability.FiniteTreeCouplingLaw

/-!
# Fresh coordinates for the corrected tree coupling

The two uniforms at physical time `k` are independent of any countable or
noncountable state determined by earlier pairs.  Moreover, the recovery
uniform is independent of both that state and the current parent-choice
uniform.  This supplies the independence premises of the stopping-time
rejection law for a causal coupled forest construction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HeightPaper.CountCoupling

/-- Fill in one omitted coordinate by zero.  A function invariant under
changes to that coordinate factors through this restriction. -/
def extendExcept (j : Fin 2 × ℕ)
    (v : {i : Fin 2 × ℕ // i ≠ j} → ℝ) :
    (Fin 2 × ℕ) → ℝ :=
  fun i ↦ if hi : i ≠ j then v ⟨i, hi⟩ else 0

theorem measurable_extendExcept (j : Fin 2 × ℕ) :
    Measurable (extendExcept j) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i ≠ j
  · simp only [extendExcept, dite_eq_left hi]
    exact measurable_pi_apply (⟨i, hi⟩ : {i : Fin 2 × ℕ // i ≠ j})
  · simp [extendExcept, hi]

/-- A measurable function of every coordinate except `j` is independent of
the fresh uniform at `j`. -/
theorem indep_of_invariant_except
    {α : Type*} [MeasurableSpace α]
    (j : Fin 2 × ℕ)
    (F : ((Fin 2 × ℕ) → ℝ) → α)
    (hF : Measurable F)
    (hcongr : ∀ w z,
      (∀ i, i ≠ j → w i = z i) → F w = F z) :
    IndepFun F (fun w : (Fin 2 × ℕ) → ℝ ↦ w j)
      pairedUniformLaw := by
  have hind := pairedUniformLaw_independent.indepFun_set
    {i : Fin 2 × ℕ | i ≠ j} {j}
    (by
      apply Set.disjoint_left.mpr
      intro i hi hj
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hi hj
      exact hi hj) (fun i ↦ measurable_pi_apply i)
  have hh := hind.comp
    (hF.comp (measurable_extendExcept j))
    (measurable_pi_apply
      (⟨j, by simp⟩ : {i : Fin 2 × ℕ // i ∈ ({j} : Set (Fin 2 × ℕ))}))
  have heq : (F ∘ extendExcept j) ∘
      (fun (w : (Fin 2 × ℕ) → ℝ)
        (i : {i : Fin 2 × ℕ // i ≠ j}) ↦ w i) = F := by
    funext w
    apply hcongr
    intro i hi
    simp [extendExcept, hi]
  convert hh using 1
  · exact heq.symm
  · rfl

/-- The current parent-choice coordinate is independent of any causal state
built from earlier pairs of uniforms. -/
theorem causal_state_indep_parent
    {α : Type*} [MeasurableSpace α]
    (k : ℕ) (C : ((Fin 2 × ℕ) → ℝ) → α)
    (hC : Measurable C)
    (hcausal : ∀ w z,
      (∀ i, i.2 < k → w i = z i) → C w = C z) :
    IndepFun C (fun w : (Fin 2 × ℕ) → ℝ ↦ w (0, k))
      pairedUniformLaw := by
  apply indep_of_invariant_except (0, k) C hC
  intro w z hagree
  apply hcausal
  intro i hi
  exact hagree i (by
    intro he
    have := congrArg Prod.snd he
    omega)

/-- The recovery coordinate is independent jointly of the causal state and
the parent-choice coordinate used for the current proposal. -/
theorem causal_state_parent_indep_recovery
    {α : Type*} [MeasurableSpace α]
    (k : ℕ) (C : ((Fin 2 × ℕ) → ℝ) → α)
    (hC : Measurable C)
    (hcausal : ∀ w z,
      (∀ i, i.2 < k → w i = z i) → C w = C z) :
    IndepFun (fun w : (Fin 2 × ℕ) → ℝ ↦
      (C w, w (0, k)))
      (fun w : (Fin 2 × ℕ) → ℝ ↦ w (1, k))
      pairedUniformLaw := by
  apply indep_of_invariant_except (1, k)
    (fun w ↦ (C w, w (0, k)))
    (hC.prodMk (measurable_pi_apply (0, k)))
  intro w z hagree
  apply Prod.ext
  · apply hcausal
    intro i hi
    exact hagree i (by
      intro he
      have := congrArg Prod.snd he
      omega)
  · exact hagree (0, k) (by simp)

theorem pairedUniformLaw_map_eval (i : Fin 2 × ℕ) :
    pairedUniformLaw.map (fun w ↦ w i) = unitUniform :=
  Measure.infinitePi_map_eval _ _

/-- The complete joint rejection law on the actual two-sequence product
space.  A causal code needs no separately postulated independence of fresh
coordinates.  The remaining hypotheses describe pathwise inclusion and
almost-sure extinction of the upper proposal process. -/
theorem paired_causal_first_accepted_label_recovery_probability
    (A : Finset ℕ) (hA : A.Nonempty)
    (C : ℕ → ((Fin 2 × ℕ) → ℝ) → Finset ℕ × Bool)
    (hC : ∀ k, Measurable (C k))
    (hcausal : ∀ k w z,
      (∀ i, i.2 < k → w i = z i) → C k w = C k z)
    (hstart : ∀ w, (C 0 w).2 = true)
    (hstep : ∀ k w, (C (k + 1) w).2 = true ↔
      (C k w).2 = true ∧
        selectFinite ((C k w).1 ∪ A)
          (hA.mono Finset.subset_union_right) (w (0, k)) ∉ A)
    (hsubset : ∀ k w, (C k w).2 = true → A ⊆ (C k w).1)
    (hext : ∀ᵐ w ∂pairedUniformLaw, ∃ k, (C k w).1 = ∅)
    {v : ℕ} (hv : v ∈ A) (D : Set ℝ) (hD : MeasurableSet D) :
    pairedUniformLaw
      (⋃ k : ℕ, {w | (C k w).2 = true ∧
        selectFinite ((C k w).1 ∪ A)
          (hA.mono Finset.subset_union_right) (w (0, k)) = v ∧
        w (1, k) ∈ D}) =
      (A.card : ℝ≥0∞)⁻¹ * unitUniform D := by
  exact coded_first_accepted_label_recovery_probability
    pairedUniformLaw A hA C
    (fun k w ↦ w (0, k)) (fun k w ↦ w (1, k))
    hC
    (fun k ↦ measurable_pi_apply (0, k))
    (fun k ↦ measurable_pi_apply (1, k))
    (fun k ↦ causal_state_indep_parent k (C k) (hC k) (hcausal k))
    (fun k ↦ causal_state_parent_indep_recovery k (C k) (hC k) (hcausal k))
    (fun k ↦ pairedUniformLaw_map_eval (0, k))
    (fun k ↦ pairedUniformLaw_map_eval (1, k))
    hstart hstep hsubset hext hv D hD

end HeightPaper.CountCoupling
