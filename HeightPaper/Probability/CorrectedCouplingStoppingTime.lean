module

public import HeightPaper.Probability.CorrectedCouplingAdaptiveRejection

/-!
# Summing adaptive rejection over possible acceptance times

For each possible stopping time, the proposed finite set may depend on the
entire past.  Fresh uniformity gives the same cardinal balance at that time.
When the acceptance events are disjoint, countable additivity gives the
balance for the first accepted label.  Almost-sure eventual acceptance is a
separate property of the concrete coupled forest process.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace HeightPaper.CountCoupling

/-- Rejection sampling with an adapted, changing proposal set.  `H k` is the
past-state event specifying that no earlier draw was accepted.  The theorem
does not assume that the proposal set is constant between rejected draws. -/
theorem adaptive_first_acceptance_balance
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → α) (U : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k))
    (hU : ∀ k, Measurable (U k))
    (hind : ∀ k, IndepFun (X k) (U k) μ)
    (hUlaw : ∀ k, μ.map (U k) = unitUniform)
    (A : Finset ℕ) (B : ℕ → α → Finset ℕ)
    (hB : ∀ k a, (B k a).Nonempty)
    (hAB : ∀ k a, A ⊆ B k a)
    (H : ℕ → α → Prop)
    (hH : ∀ k, MeasurableSet {a | H k a})
    (hdisj : Pairwise (Disjoint on fun k : ℕ ↦
      {ω : Ω | H k (X k ω) ∧
        selectFinite (B k (X k ω)) (hB k (X k ω)) (U k ω) ∈ A}))
    {v : ℕ} (hv : v ∈ A) :
    (A.card : ℝ≥0∞) *
      μ (⋃ k : ℕ, {ω | H k (X k ω) ∧
        selectFinite (B k (X k ω)) (hB k (X k ω)) (U k ω) = v}) =
      μ (⋃ k : ℕ, {ω | H k (X k ω) ∧
        selectFinite (B k (X k ω)) (hB k (X k ω)) (U k ω) ∈ A}) := by
  let E : ℕ → Set Ω := fun k ↦
    {ω | H k (X k ω) ∧
      selectFinite (B k (X k ω)) (hB k (X k ω)) (U k ω) = v}
  let F : ℕ → Set Ω := fun k ↦
    {ω | H k (X k ω) ∧
      selectFinite (B k (X k ω)) (hB k (X k ω)) (U k ω) ∈ A}
  have hsubset (k : ℕ) : E k ⊆ F k := by
    rintro ω ⟨hh, he⟩
    exact ⟨hh, he ▸ hv⟩
  have hdisjE : Pairwise (Disjoint on E) := by
    intro i j hij
    exact (hdisj hij).mono (hsubset i) (hsubset j)
  have hmeasE (k : ℕ) : MeasurableSet (E k) := by
    have hsel : Measurable (fun z : α × ℝ ↦
        selectFinite (B k z.1) (hB k z.1) z.2) :=
      measurable_from_prod_countable_right
        (fun a ↦ measurable_selectFinite (B k a) (hB k a))
    have hset : MeasurableSet {z : α × ℝ | H k z.1 ∧
        selectFinite (B k z.1) (hB k z.1) z.2 = v} :=
      ((hH k).preimage measurable_fst).inter
        (hsel (measurableSet_singleton v))
    exact hset.preimage ((hX k).prodMk (hU k))
  have hmeasF (k : ℕ) : MeasurableSet (F k) := by
    have hsel : Measurable (fun z : α × ℝ ↦
        selectFinite (B k z.1) (hB k z.1) z.2) :=
      measurable_from_prod_countable_right
        (fun a ↦ measurable_selectFinite (B k a) (hB k a))
    have hset : MeasurableSet {z : α × ℝ | H k z.1 ∧
        selectFinite (B k z.1) (hB k z.1) z.2 ∈ A} :=
      ((hH k).preimage measurable_fst).inter (hsel A.measurableSet)
    exact hset.preimage ((hX k).prodMk (hU k))
  change (A.card : ℝ≥0∞) * μ (⋃ k, E k) = μ (⋃ k, F k)
  rw [measure_iUnion hdisjE hmeasE, measure_iUnion hdisj hmeasF]
  change (A.card : ℝ≥0∞) * (∑' k, μ (E k)) = ∑' k, μ (F k)
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext k
  exact adaptive_selectFinite_acceptance_balance_of_indep
    μ (X k) (U k) (hX k) (hU k) (hind k) (hUlaw k)
    A (B k) (hB k) (hAB k) (H k) (hH k) hv

/-- Stopping-time balance with a countable code of each past state.  The
code records only the proposed active set and whether an acceptance is still
pending, so the underlying genealogy itself need not be countable. -/
theorem coded_first_acceptance_balance
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Finset ℕ) (hA : A.Nonempty)
    (C : ℕ → Ω → Finset ℕ × Bool) (U : ℕ → Ω → ℝ)
    (hC : ∀ k, Measurable (C k))
    (hU : ∀ k, Measurable (U k))
    (hind : ∀ k, IndepFun (C k) (U k) μ)
    (hUlaw : ∀ k, μ.map (U k) = unitUniform)
    (hdisj : Pairwise (Disjoint on fun k : ℕ ↦
      {ω : Ω | (C k ω).2 = true ∧
        selectFinite ((C k ω).1 ∪ A)
          (hA.mono Finset.subset_union_right) (U k ω) ∈ A}))
    {v : ℕ} (hv : v ∈ A) :
    (A.card : ℝ≥0∞) *
      μ (⋃ k : ℕ, {ω | (C k ω).2 = true ∧
        selectFinite ((C k ω).1 ∪ A)
          (hA.mono Finset.subset_union_right) (U k ω) = v}) =
      μ (⋃ k : ℕ, {ω | (C k ω).2 = true ∧
        selectFinite ((C k ω).1 ∪ A)
          (hA.mono Finset.subset_union_right) (U k ω) ∈ A}) := by
  let B : ℕ → Finset ℕ × Bool → Finset ℕ :=
    fun _ c ↦ c.1 ∪ A
  have hB (k : ℕ) (c : Finset ℕ × Bool) : (B k c).Nonempty :=
    hA.mono Finset.subset_union_right
  have hAB (k : ℕ) (c : Finset ℕ × Bool) : A ⊆ B k c :=
    Finset.subset_union_right
  let H : ℕ → Finset ℕ × Bool → Prop := fun _ c ↦ c.2 = true
  have hH (k : ℕ) : MeasurableSet {c : Finset ℕ × Bool | H k c} :=
    (measurableSet_singleton true).preimage measurable_snd
  change (A.card : ℝ≥0∞) *
    μ (⋃ k : ℕ, {ω | H k (C k ω) ∧
      selectFinite (B k (C k ω)) (hB k (C k ω)) (U k ω) = v}) =
    μ (⋃ k : ℕ, {ω | H k (C k ω) ∧
      selectFinite (B k (C k ω)) (hB k (C k ω)) (U k ω) ∈ A})
  exact adaptive_first_acceptance_balance μ C U hC hU hind hUlaw
    A B hB hAB H hH hdisj hv

/-- If the pending flag becomes false at the first accepted draw and stays
false afterwards, the acceptance events at distinct times are disjoint. -/
theorem coded_first_acceptance_pairwise
    {Ω : Type*} (A : Finset ℕ) (hA : A.Nonempty)
    (C : ℕ → Ω → Finset ℕ × Bool) (U : ℕ → Ω → ℝ)
    (hstep : ∀ k ω, (C (k + 1) ω).2 = true ↔
      (C k ω).2 = true ∧
        selectFinite ((C k ω).1 ∪ A)
          (hA.mono Finset.subset_union_right) (U k ω) ∉ A) :
    Pairwise (Disjoint on fun k : ℕ ↦
      {ω : Ω | (C k ω).2 = true ∧
        selectFinite ((C k ω).1 ∪ A)
          (hA.mono Finset.subset_union_right) (U k ω) ∈ A}) := by
  let F : ℕ → Set Ω := fun k ↦ {ω | (C k ω).2 = true ∧
    selectFinite ((C k ω).1 ∪ A)
      (hA.mono Finset.subset_union_right) (U k ω) ∈ A}
  have hback (ω : Ω) {i j : ℕ} (hij : i ≤ j)
      (hj : (C j ω).2 = true) : (C i ω).2 = true := by
    induction j, hij using Nat.le_induction with
    | base => exact hj
    | succ j _ ih => exact ih ((hstep j ω).mp hj).1
  intro i j hij
  have hdisj_lt {i j : ℕ} (hij : i < j) : Disjoint (F i) (F j) := by
    apply Set.disjoint_left.mpr
    intro ω hi hj
    have hnext : (C (i + 1) ω).2 = true :=
      hback ω (Nat.succ_le_of_lt hij) hj.1
    exact ((hstep i ω).mp hnext).2 hi.2
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hdisj_lt hlt
  · exact (hdisj_lt hgt).symm

end HeightPaper.CountCoupling
