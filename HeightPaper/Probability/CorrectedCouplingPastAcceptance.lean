module

public import HeightPaper.Probability.CorrectedCouplingFreshPairs

/-!
# Rejection and emissions on events determined by the past

The first accepted proposal can start on an event of arbitrary probability.
All identities are stated as identities of masses, so no conditional measure
or strong Markov theorem is needed. The coverage hypotheses are separate from
freshness and must be supplied by the concrete coupled construction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace HeightPaper.CountCoupling

/-- A fresh recovery draw retains its law at an emission chosen before that
draw is inspected. The disjoint emission events can cover any past event. -/
theorem emission_joint_probability_of_cover
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (R : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hR : ∀ k, Measurable (R k))
    (hind : ∀ k, IndepFun (X k) (R k) μ)
    (hRlaw : ∀ k, μ.map (R k) = unitUniform)
    (E : ℕ → Set α) (hE : ∀ k, MeasurableSet (E k))
    (hdisj : Pairwise (Disjoint on fun k ↦ (X k) ⁻¹' E k))
    (H : Set Ω) (hcover : μ (⋃ k, (X k) ⁻¹' E k) = μ H)
    (D : Set ℝ) (hD : MeasurableSet D) :
    μ (⋃ k, (X k) ⁻¹' E k ∩ (R k) ⁻¹' D) =
      μ H * unitUniform D := by
  have hm (k : ℕ) : MeasurableSet ((X k) ⁻¹' E k) := (hE k).preimage (hX k)
  have hpair : Pairwise (Disjoint on fun k ↦ (X k) ⁻¹' E k ∩ (R k) ⁻¹' D) := by
    intro i j hij
    exact (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
  have hmul (k : ℕ) :
      μ ((X k) ⁻¹' E k ∩ (R k) ⁻¹' D) =
        μ ((X k) ⁻¹' E k) * unitUniform D := by
    have hi := (hind k).measure_inter_preimage_eq_mul (E k) D (hE k) hD
    have hmass : μ ((R k) ⁻¹' D) = unitUniform D := by
      rw [← Measure.map_apply (hR k) hD, hRlaw k]
    rwa [hmass] at hi
  rw [measure_iUnion hpair (fun k ↦ (hm k).inter ((hR k) hD))]
  simp_rw [hmul]
  rw [ENNReal.tsum_mul_right, ← measure_iUnion hdisj hm, hcover]

/-- First accepted labels are uniform, jointly with a fresh recovery draw,
even when the acceptance interval starts only on an event `H`. -/
theorem coded_first_accepted_joint_probability_of_cover
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Finset ℕ) (hA : A.Nonempty)
    (C : ℕ → Ω → Finset ℕ × Bool) (U R : ℕ → Ω → ℝ)
    (hC : ∀ k, Measurable (C k))
    (hU : ∀ k, Measurable (U k)) (hR : ∀ k, Measurable (R k))
    (hindU : ∀ k, IndepFun (C k) (U k) μ)
    (hindR : ∀ k, IndepFun (fun ω ↦ (C k ω, U k ω)) (R k) μ)
    (hUlaw : ∀ k, μ.map (U k) = unitUniform)
    (hRlaw : ∀ k, μ.map (R k) = unitUniform)
    (hdisj : Pairwise (Disjoint on fun k ↦
      {ω | (C k ω).2 = true ∧
        selectFinite ((C k ω).1 ∪ A)
          (hA.mono Finset.subset_union_right) (U k ω) ∈ A}))
    (H : Set Ω)
    (hcover : μ (⋃ k, {ω | (C k ω).2 = true ∧
      selectFinite ((C k ω).1 ∪ A)
        (hA.mono Finset.subset_union_right) (U k ω) ∈ A}) = μ H)
    {v : ℕ} (hv : v ∈ A) (D : Set ℝ) (hD : MeasurableSet D) :
    μ (⋃ k, {ω | (C k ω).2 = true ∧
      selectFinite ((C k ω).1 ∪ A)
        (hA.mono Finset.subset_union_right) (U k ω) = v ∧ R k ω ∈ D}) =
      (A.card : ℝ≥0∞)⁻¹ * μ H * unitUniform D := by
  let T : Set ((Finset ℕ × Bool) × ℝ) :=
    {z | z.1.2 = true ∧
      selectFinite (z.1.1 ∪ A)
        (hA.mono Finset.subset_union_right) z.2 = v}
  let X : ℕ → Ω → (Finset ℕ × Bool) × ℝ := fun k ω ↦ (C k ω, U k ω)
  have hsel : Measurable (fun z : (Finset ℕ × Bool) × ℝ ↦
      selectFinite (z.1.1 ∪ A)
        (hA.mono Finset.subset_union_right) z.2) :=
    measurable_from_prod_countable_right
      (fun c ↦ measurable_selectFinite (c.1 ∪ A)
        (hA.mono Finset.subset_union_right))
  have hT : MeasurableSet T :=
    (((measurableSet_singleton true).preimage measurable_snd).preimage
      measurable_fst).inter (hsel (measurableSet_singleton v))
  have hpair : Pairwise (Disjoint on fun k ↦ (X k) ⁻¹' T) := by
    intro i j hij
    apply (hdisj hij).mono
    · rintro ω ⟨hp, he⟩
      exact ⟨hp, he ▸ hv⟩
    · rintro ω ⟨hp, he⟩
      exact ⟨hp, he ▸ hv⟩
  have hbalance := coded_first_acceptance_balance
    μ A hA C U hC hU hindU hUlaw hdisj hv
  rw [hcover] at hbalance
  have hcard0 : (A.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  have hmass : μ (⋃ k, (X k) ⁻¹' T) = (A.card : ℝ≥0∞)⁻¹ * μ H := by
    calc
      μ (⋃ k, (X k) ⁻¹' T) =
          (A.card : ℝ≥0∞)⁻¹ * ((A.card : ℝ≥0∞) *
            μ (⋃ k, (X k) ⁻¹' T)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcard0 (by simp), one_mul]
      _ = _ := congrArg ((A.card : ℝ≥0∞)⁻¹ * ·) hbalance
  have he := emission_joint_probability_of_cover μ X R
    (fun k ↦ (hC k).prodMk (hU k)) hR hindR hRlaw
    (fun _ ↦ T) (fun _ ↦ hT) hpair
    (⋃ k, (X k) ⁻¹' T) rfl D hD
  rw [hmass] at he
  convert he using 1
  congr 1
  ext ω
  simp [X, T, and_assoc]

end HeightPaper.CountCoupling
