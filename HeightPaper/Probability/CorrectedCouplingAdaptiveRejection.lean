module

public import HeightPaper.Probability.CorrectedCouplingRejection
public import HeightPaper.Probability.CorrectedCouplingInfiniteWord

/-!
# Uniform acceptance from a changing proposal set

The paper's rejection step allows the upper active set to change after every
rejected draw.  The next lemma gives the exact one-step probability balance
for a proposal set determined by an arbitrary countable past state.  The
acceptance set is fixed during the rejected interval.  Summing this balance
over possible acceptance times is the stopping-time part of the proof.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HeightPaper.CountCoupling

/-- Draw a uniform label from a nonempty finite active set using one fresh
real uniform coordinate. -/
noncomputable def selectFinite (B : Finset ℕ) (hB : B.Nonempty)
    (u : ℝ) : ℕ :=
  (CouplingGenealogy.initial B).selectedActive hB u

theorem measurable_selectFinite (B : Finset ℕ) (hB : B.Nonempty) :
    Measurable (selectFinite B hB) :=
  (CouplingGenealogy.initial B).measurable_selectedActive hB

theorem selectFinite_mem (B : Finset ℕ) (hB : B.Nonempty) (u : ℝ) :
    selectFinite B hB u ∈ B :=
  (CouplingGenealogy.initial B).selectedActive_mem hB u

/-- The single-coordinate law behind the selected upper active label. -/
theorem selectFinite_law (B : Finset ℕ) (hB : B.Nonempty) :
    unitUniform.map (selectFinite B hB) = Measure.uniformOfFinset B := by
  have hm := measurable_selectFinite B hB
  calc
    unitUniform.map (selectFinite B hB) =
        (uniformLaw.map (fun u : ℕ → ℝ ↦ u 0)).map (selectFinite B hB) := by
      rw [uniformLaw_map_eval]
    _ = uniformLaw.map (fun u : ℕ → ℝ ↦ selectFinite B hB (u 0)) := by
      rw [Measure.map_map hm (measurable_pi_apply 0)]
      rfl
    _ = Measure.uniformOfFinset B :=
      (CouplingGenealogy.initial B).selectedActive_law hB 0

theorem selectFinite_probability_singleton
    (B : Finset ℕ) (hB : B.Nonempty) (v : ℕ) :
    unitUniform {u | selectFinite B hB u = v} =
      if v ∈ B then (B.card : ℝ≥0∞)⁻¹ else 0 := by
  change unitUniform ((selectFinite B hB) ⁻¹' {v}) = _
  rw [← Measure.map_apply (measurable_selectFinite B hB)
    (measurableSet_singleton v), selectFinite_law,
    Measure.uniformOfFinset_apply_singleton]
  by_cases hv : v ∈ B <;> simp [hv]

theorem selectFinite_probability_subset
    (A B : Finset ℕ) (hB : B.Nonempty) (hAB : A ⊆ B) :
    unitUniform {u | selectFinite B hB u ∈ A} =
      (A.card : ℝ≥0∞) / B.card := by
  classical
  change unitUniform ((selectFinite B hB) ⁻¹' (A : Set ℕ)) = _
  rw [← Measure.map_apply (measurable_selectFinite B hB) A.measurableSet,
    selectFinite_law, Measure.uniformOfFinset_apply]
  congr 1
  congr 1
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_coe]
  exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨hAB hx, hx⟩⟩

/-- Each accepted label has exactly the same mass, even when the current
proposal set is larger.  The cardinal factor avoids division by the
acceptance probability. -/
theorem selectFinite_acceptance_balance
    (A B : Finset ℕ) (hB : B.Nonempty) (hAB : A ⊆ B)
    {v : ℕ} (hv : v ∈ A) :
    (A.card : ℝ≥0∞) *
      unitUniform {u | selectFinite B hB u = v} =
      unitUniform {u | selectFinite B hB u ∈ A} := by
  rw [selectFinite_probability_singleton,
    selectFinite_probability_subset A B hB hAB]
  simp [hAB hv, div_eq_mul_inv]

/-- A changing proposal set may depend on any countable past state.  Fresh
uniform sampling still assigns equal mass to each accepted label.  This is
the probability identity needed when the upper forest changes during
rejected trials. -/
theorem adaptive_selectFinite_acceptance_balance
    {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α]
    (η : Measure α) (A : Finset ℕ)
    (B : α → Finset ℕ) (hB : ∀ a, (B a).Nonempty)
    (hAB : ∀ a, A ⊆ B a)
    (H : α → Prop) (hH : MeasurableSet {a | H a})
    {v : ℕ} (hv : v ∈ A) :
    (A.card : ℝ≥0∞) *
      (η.prod unitUniform) {z | H z.1 ∧
        selectFinite (B z.1) (hB z.1) z.2 = v} =
      (η.prod unitUniform) {z | H z.1 ∧
        selectFinite (B z.1) (hB z.1) z.2 ∈ A} := by
  let sel : α × ℝ → ℕ :=
    fun z ↦ selectFinite (B z.1) (hB z.1) z.2
  have hsel : Measurable sel :=
    measurable_from_prod_countable_right
      (fun a ↦ measurable_selectFinite (B a) (hB a))
  have hleft : MeasurableSet {z : α × ℝ | H z.1 ∧ sel z = v} :=
    (hH.preimage measurable_fst).inter
      (hsel (measurableSet_singleton v))
  have hright : MeasurableSet {z : α × ℝ | H z.1 ∧ sel z ∈ A} :=
    (hH.preimage measurable_fst).inter (hsel A.measurableSet)
  change (A.card : ℝ≥0∞) *
    (η.prod unitUniform) {z | H z.1 ∧ sel z = v} =
      (η.prod unitUniform) {z | H z.1 ∧ sel z ∈ A}
  rw [Measure.prod_apply hleft, Measure.prod_apply hright]
  rw [← lintegral_const_mul' (A.card : ℝ≥0∞) _ (by simp)]
  apply lintegral_congr
  intro a
  by_cases ha : H a
  · simpa only [ha, true_and, Set.preimage_ofPred_eq] using
      selectFinite_acceptance_balance A (B a) (hB a) (hAB a) hv
  · simp [ha]

/-- Probability balance on an arbitrary sample space.  The proposal set and
the pre-acceptance event may depend on the past state `X`; only the next
uniform `U` must be independent of that state. -/
theorem adaptive_selectFinite_acceptance_balance_of_indep
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → α) (U : Ω → ℝ)
    (hX : Measurable X) (hU : Measurable U)
    (hind : IndepFun X U μ) (hUlaw : μ.map U = unitUniform)
    (A : Finset ℕ) (B : α → Finset ℕ)
    (hB : ∀ a, (B a).Nonempty) (hAB : ∀ a, A ⊆ B a)
    (H : α → Prop) (hH : MeasurableSet {a | H a})
    {v : ℕ} (hv : v ∈ A) :
    (A.card : ℝ≥0∞) *
      μ {ω | H (X ω) ∧ selectFinite (B (X ω)) (hB (X ω)) (U ω) = v} =
      μ {ω | H (X ω) ∧ selectFinite (B (X ω)) (hB (X ω)) (U ω) ∈ A} := by
  let sel : α × ℝ → ℕ :=
    fun z ↦ selectFinite (B z.1) (hB z.1) z.2
  have hsel : Measurable sel :=
    measurable_from_prod_countable_right
      (fun a ↦ measurable_selectFinite (B a) (hB a))
  have hleft : MeasurableSet {z : α × ℝ | H z.1 ∧ sel z = v} :=
    (hH.preimage measurable_fst).inter
      (hsel (measurableSet_singleton v))
  have hright : MeasurableSet {z : α × ℝ | H z.1 ∧ sel z ∈ A} :=
    (hH.preimage measurable_fst).inter (hsel A.measurableSet)
  have hjoint : μ.map (fun ω ↦ (X ω, U ω)) =
      (μ.map X).prod unitUniform := by
    rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hU.aemeasurable, hUlaw]
  have hm : Measurable (fun ω ↦ (X ω, U ω)) := hX.prodMk hU
  change (A.card : ℝ≥0∞) *
    μ ((fun ω ↦ (X ω, U ω)) ⁻¹' {z | H z.1 ∧ sel z = v}) =
    μ ((fun ω ↦ (X ω, U ω)) ⁻¹' {z | H z.1 ∧ sel z ∈ A})
  rw [← Measure.map_apply hm hleft, ← Measure.map_apply hm hright,
    hjoint]
  exact adaptive_selectFinite_acceptance_balance
    (μ.map X) A B hB hAB H hH hv

/-- Only the proposed finite active set and a Boolean past-event flag need
to be encoded.  The entire genealogy may live in a non-countable space.
Taking the union with `A` totalizes the proposal set off the event where
the actual inclusion `A ⊆ B` is known. -/
theorem coded_proposal_acceptance_balance
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Finset ℕ) (hA : A.Nonempty)
    (C : Ω → Finset ℕ × Bool) (U : Ω → ℝ)
    (hC : Measurable C) (hU : Measurable U)
    (hind : IndepFun C U μ) (hUlaw : μ.map U = unitUniform)
    {v : ℕ} (hv : v ∈ A) :
    (A.card : ℝ≥0∞) *
      μ {ω | (C ω).2 = true ∧
        selectFinite ((C ω).1 ∪ A)
          (hA.mono Finset.subset_union_right) (U ω) = v} =
      μ {ω | (C ω).2 = true ∧
        selectFinite ((C ω).1 ∪ A)
          (hA.mono Finset.subset_union_right) (U ω) ∈ A} := by
  let B : (Finset ℕ × Bool) → Finset ℕ := fun c ↦ c.1 ∪ A
  have hB (c : Finset ℕ × Bool) : (B c).Nonempty :=
    hA.mono Finset.subset_union_right
  have hAB (c : Finset ℕ × Bool) : A ⊆ B c :=
    Finset.subset_union_right
  let H : (Finset ℕ × Bool) → Prop := fun c ↦ c.2 = true
  have hH : MeasurableSet {c : Finset ℕ × Bool | H c} :=
    (measurableSet_singleton true).preimage measurable_snd
  change (A.card : ℝ≥0∞) *
    μ {ω | H (C ω) ∧ selectFinite (B (C ω)) (hB (C ω)) (U ω) = v} =
      μ {ω | H (C ω) ∧ selectFinite (B (C ω)) (hB (C ω)) (U ω) ∈ A}
  exact adaptive_selectFinite_acceptance_balance_of_indep
    μ C U hC hU hind hUlaw A B hB hAB H hH hv

end HeightPaper.CountCoupling
