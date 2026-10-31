module

public import HeightPaper.Probability.CorrectedCouplingStoppingTime

/-!
# Eventual acceptance before upper extinction

While a smaller active set `A` remains pending, it is contained in the
upper active set.  If the upper forest eventually has no active vertices,
some proposed vertex must have been accepted first.  This pathwise fact
turns almost-sure upper extinction into almost-sure coverage of the
stopping-time rejection events.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace HeightPaper.CountCoupling

/-- A pending nonempty active set must be selected before an enclosing upper
active set becomes empty. -/
theorem first_acceptance_before_upper_empty
    (A : Finset ℕ) (hA : A.Nonempty)
    (C : ℕ → Finset ℕ × Bool) (U : ℕ → ℝ)
    (hstart : (C 0).2 = true)
    (hstep : ∀ k, (C (k + 1)).2 = true ↔
      (C k).2 = true ∧
        selectFinite ((C k).1 ∪ A)
          (hA.mono Finset.subset_union_right) (U k) ∉ A)
    (hsubset : ∀ k, (C k).2 = true → A ⊆ (C k).1)
    (hext : ∃ k, (C k).1 = ∅) :
    ∃ k, (C k).2 = true ∧
      selectFinite ((C k).1 ∪ A)
        (hA.mono Finset.subset_union_right) (U k) ∈ A := by
  by_contra hnone
  have hpending : ∀ k, (C k).2 = true := by
    intro k
    induction k with
    | zero => exact hstart
    | succ k ih =>
        apply (hstep k).2
        refine ⟨ih, ?_⟩
        intro hacc
        exact hnone ⟨k, ih, hacc⟩
  obtain ⟨k, hk⟩ := hext
  obtain ⟨v, hv⟩ := hA
  have hvupper := hsubset k (hpending k) hv
  simp [hk] at hvupper

/-- The preceding deterministic fact gives probability one to the union of
first-acceptance events, assuming almost-sure upper extinction. -/
theorem coded_first_acceptance_cover_of_upper_extinction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Finset ℕ) (hA : A.Nonempty)
    (C : ℕ → Ω → Finset ℕ × Bool) (U : ℕ → Ω → ℝ)
    (hC : ∀ k, Measurable (C k))
    (hU : ∀ k, Measurable (U k))
    (hstart : ∀ ω, (C 0 ω).2 = true)
    (hstep : ∀ k ω, (C (k + 1) ω).2 = true ↔
      (C k ω).2 = true ∧
        selectFinite ((C k ω).1 ∪ A)
          (hA.mono Finset.subset_union_right) (U k ω) ∉ A)
    (hsubset : ∀ k ω, (C k ω).2 = true → A ⊆ (C k ω).1)
    (hext : ∀ᵐ ω ∂μ, ∃ k, (C k ω).1 = ∅) :
    μ (⋃ k : ℕ, {ω | (C k ω).2 = true ∧
      selectFinite ((C k ω).1 ∪ A)
        (hA.mono Finset.subset_union_right) (U k ω) ∈ A}) = 1 := by
  let F : ℕ → Set Ω := fun k ↦ {ω | (C k ω).2 = true ∧
    selectFinite ((C k ω).1 ∪ A)
      (hA.mono Finset.subset_union_right) (U k ω) ∈ A}
  have hmeas (k : ℕ) : MeasurableSet (F k) := by
    have hsel : Measurable (fun z : (Finset ℕ × Bool) × ℝ ↦
        selectFinite (z.1.1 ∪ A)
          (hA.mono Finset.subset_union_right) z.2) :=
      measurable_from_prod_countable_right
        (fun c ↦ measurable_selectFinite (c.1 ∪ A)
          (hA.mono Finset.subset_union_right))
    have hset : MeasurableSet
        {z : (Finset ℕ × Bool) × ℝ | z.1.2 = true ∧
          selectFinite (z.1.1 ∪ A)
            (hA.mono Finset.subset_union_right) z.2 ∈ A} :=
      (((measurableSet_singleton true).preimage measurable_snd).preimage
        measurable_fst).inter (hsel A.measurableSet)
    exact hset.preimage ((hC k).prodMk (hU k))
  have hcover : ∀ᵐ ω ∂μ, ω ∈ ⋃ k, F k := by
    filter_upwards [hext] with ω hω
    obtain ⟨k, hk⟩ := first_acceptance_before_upper_empty A hA
      (fun j ↦ C j ω) (fun j ↦ U j ω)
      (hstart ω) (fun j ↦ hstep j ω)
      (fun j ↦ hsubset j ω) hω
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  change μ (⋃ k, F k) = 1
  exact (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hmeas)).mp hcover

/-- A uniform accepted label from a changing proposal set.  The assumptions
are the predictable-code independence, the pending-flag update, inclusion of
the smaller active set while pending, and almost-sure upper extinction. -/
theorem coded_first_accepted_label_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Finset ℕ) (hA : A.Nonempty)
    (C : ℕ → Ω → Finset ℕ × Bool) (U : ℕ → Ω → ℝ)
    (hC : ∀ k, Measurable (C k))
    (hU : ∀ k, Measurable (U k))
    (hind : ∀ k, IndepFun (C k) (U k) μ)
    (hUlaw : ∀ k, μ.map (U k) = unitUniform)
    (hstart : ∀ ω, (C 0 ω).2 = true)
    (hstep : ∀ k ω, (C (k + 1) ω).2 = true ↔
      (C k ω).2 = true ∧
        selectFinite ((C k ω).1 ∪ A)
          (hA.mono Finset.subset_union_right) (U k ω) ∉ A)
    (hsubset : ∀ k ω, (C k ω).2 = true → A ⊆ (C k ω).1)
    (hext : ∀ᵐ ω ∂μ, ∃ k, (C k ω).1 = ∅)
    {v : ℕ} (hv : v ∈ A) :
    μ (⋃ k : ℕ, {ω | (C k ω).2 = true ∧
      selectFinite ((C k ω).1 ∪ A)
        (hA.mono Finset.subset_union_right) (U k ω) = v}) =
      (A.card : ℝ≥0∞)⁻¹ := by
  have hdisj := coded_first_acceptance_pairwise A hA C U hstep
  have hbalance := coded_first_acceptance_balance
    μ A hA C U hC hU hind hUlaw hdisj hv
  have hcover := coded_first_acceptance_cover_of_upper_extinction
    μ A hA C U hC hU hstart hstep hsubset hext
  rw [hcover] at hbalance
  apply ENNReal.eq_inv_of_mul_eq_one_left
  simpa only [mul_comm] using hbalance

/-- The recovery uniform at the first accepted proposal is still fresh and
independent of its selected label.  This is the joint version of the
stopping-time rejection law used by the time-changed middle forest. -/
theorem coded_first_accepted_label_recovery_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Finset ℕ) (hA : A.Nonempty)
    (C : ℕ → Ω → Finset ℕ × Bool)
    (U R : ℕ → Ω → ℝ)
    (hC : ∀ k, Measurable (C k))
    (hU : ∀ k, Measurable (U k))
    (hR : ∀ k, Measurable (R k))
    (hindU : ∀ k, IndepFun (C k) (U k) μ)
    (hindR : ∀ k, IndepFun
      (fun ω ↦ (C k ω, U k ω)) (R k) μ)
    (hUlaw : ∀ k, μ.map (U k) = unitUniform)
    (hRlaw : ∀ k, μ.map (R k) = unitUniform)
    (hstart : ∀ ω, (C 0 ω).2 = true)
    (hstep : ∀ k ω, (C (k + 1) ω).2 = true ↔
      (C k ω).2 = true ∧
        selectFinite ((C k ω).1 ∪ A)
          (hA.mono Finset.subset_union_right) (U k ω) ∉ A)
    (hsubset : ∀ k ω, (C k ω).2 = true → A ⊆ (C k ω).1)
    (hext : ∀ᵐ ω ∂μ, ∃ k, (C k ω).1 = ∅)
    {v : ℕ} (hv : v ∈ A) (D : Set ℝ) (hD : MeasurableSet D) :
    μ (⋃ k : ℕ, {ω | (C k ω).2 = true ∧
      selectFinite ((C k ω).1 ∪ A)
        (hA.mono Finset.subset_union_right) (U k ω) = v ∧
      R k ω ∈ D}) =
      (A.card : ℝ≥0∞)⁻¹ * unitUniform D := by
  let T : Set ((Finset ℕ × Bool) × ℝ) :=
    {z | z.1.2 = true ∧
      selectFinite (z.1.1 ∪ A)
        (hA.mono Finset.subset_union_right) z.2 = v}
  let E : ℕ → Set Ω := fun k ↦
    {ω | (C k ω).2 = true ∧
      selectFinite ((C k ω).1 ∪ A)
        (hA.mono Finset.subset_union_right) (U k ω) = v}
  let F : ℕ → Set Ω := fun k ↦ E k ∩ (R k) ⁻¹' D
  have hsel : Measurable (fun z : (Finset ℕ × Bool) × ℝ ↦
      selectFinite (z.1.1 ∪ A)
        (hA.mono Finset.subset_union_right) z.2) :=
    measurable_from_prod_countable_right
      (fun c ↦ measurable_selectFinite (c.1 ∪ A)
        (hA.mono Finset.subset_union_right))
  have hT : MeasurableSet T :=
    (((measurableSet_singleton true).preimage measurable_snd).preimage
      measurable_fst).inter (hsel (measurableSet_singleton v))
  have hE (k : ℕ) : MeasurableSet (E k) :=
    hT.preimage ((hC k).prodMk (hU k))
  have hF (k : ℕ) : MeasurableSet (F k) :=
    (hE k).inter ((hR k) hD)
  have hpair : Pairwise (Disjoint on E) := by
    have hpairA := coded_first_acceptance_pairwise A hA C U hstep
    intro i j hij
    apply (hpairA hij).mono
    · rintro ω ⟨hp, he⟩
      exact ⟨hp, he ▸ hv⟩
    · rintro ω ⟨hp, he⟩
      exact ⟨hp, he ▸ hv⟩
  have hpairF : Pairwise (Disjoint on F) := by
    intro i j hij
    exact (hpair hij).mono Set.inter_subset_left Set.inter_subset_left
  have hmul (k : ℕ) : μ (F k) = μ (E k) * unitUniform D := by
    have hi := (hindR k).measure_inter_preimage_eq_mul T D hT hD
    have hmeasure : μ ((R k) ⁻¹' D) = unitUniform D := by
      rw [← Measure.map_apply (hR k) hD, hRlaw k]
    rw [hmeasure] at hi
    exact hi
  have hunion :
      (⋃ k : ℕ, {ω | (C k ω).2 = true ∧
        selectFinite ((C k ω).1 ∪ A)
          (hA.mono Finset.subset_union_right) (U k ω) = v ∧
        R k ω ∈ D}) = ⋃ k, F k := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, F, E,
      Set.mem_inter_iff, Set.mem_preimage]
    simp [and_assoc]
  rw [hunion]
  rw [measure_iUnion hpairF hF]
  simp_rw [hmul]
  rw [ENNReal.tsum_mul_right, ← measure_iUnion hpair hE]
  rw [coded_first_accepted_label_probability
    μ A hA C U hC hU hindU hUlaw hstart hstep hsubset hext hv]

end HeightPaper.CountCoupling
