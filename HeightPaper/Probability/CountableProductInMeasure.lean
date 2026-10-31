module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.MetricSpace.PiNat

/-!
# Convergence in measure in a countable product

The compatible metric on a countable product is a weighted sum of truncated
coordinate distances. Coordinatewise convergence in measure therefore gives
convergence in measure of the whole product under a finite source measure.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology ENNReal PiCountable

namespace HeightPaper

theorem tendstoInMeasure_countablePi {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {F : ℕ → Type*}
    [∀ i, PseudoEMetricSpace (F i)]
    (X : ℕ → Ω → ∀ i, F i) (Z : Ω → ∀ i, F i)
    (h : ∀ i, TendstoInMeasure μ (fun n ω ↦ X n ω i) atTop
      (fun ω ↦ Z ω i)) :
    TendstoInMeasure μ X atTop Z := by
  apply tendstoInMeasure_of_ne_top
  intro ε hε hεtop
  obtain ⟨K, hK⟩ : ∃ K : Finset ℕ,
      (∑' i : {j : ℕ // j ∉ K}, (2⁻¹ : ℝ≥0∞) ^ Encodable.encode (i : ℕ)) <
        ε / 2 := by
    have hs : (∑' i : ℕ, (2⁻¹ : ℝ≥0∞) ^ Encodable.encode i) ≠ ∞ :=
      (tsum_geometric_encode_lt_top ENNReal.one_half_lt_one).ne
    exact ((tendsto_order.1 <|
      ENNReal.tendsto_tsum_compl_atTop_zero hs).2 _
        (by simpa using hε.ne')).exists
  obtain ⟨δ, hδpos, hδsmall⟩ : ∃ δ : ℝ≥0∞, 0 < δ ∧
      δ * (K.card : ℝ≥0∞) < ε / 2 :=
    ENNReal.exists_pos_mul_lt (by simp) (by simpa using hε.ne')
  let bad (i n : ℕ) : Set Ω := {ω | δ ≤ edist (X n ω i) (Z ω i)}
  have hbad (i : ℕ) : Tendsto (fun n ↦ μ (bad i n)) atTop (𝓝 0) := h i δ hδpos
  have hsum : Tendsto (fun n ↦ ∑ i ∈ K, μ (bad i n)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum K (fun i _ ↦ hbad i)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
  · intro n
    exact bot_le
  · intro n
    have hsub : {ω | ε ≤ edist (X n ω) (Z ω)} ⊆
        ⋃ i ∈ K, bad i n := by
      intro ω hω
      by_contra hnot
      have hcoord (i : ℕ) (hi : i ∈ K) :
          edist (X n ω i) (Z ω i) < δ := by
        by_contra hlarge
        exact hnot (Set.mem_iUnion.mpr ⟨i,
          Set.mem_iUnion.mpr ⟨hi, le_of_not_gt hlarge⟩⟩)
      have hfull : edist (X n ω) (Z ω) < ε := by
        calc
          edist (X n ω) (Z ω) =
              ∑' i : ℕ, min ((2⁻¹ : ℝ≥0∞) ^ Encodable.encode i)
                (edist (X n ω i) (Z ω i)) :=
            PiCountable.edist_eq_tsum _ _
          _ = ∑ i ∈ K, min ((2⁻¹ : ℝ≥0∞) ^ Encodable.encode i)
                (edist (X n ω i) (Z ω i)) +
              ∑' i : {j : ℕ // j ∉ K},
                min ((2⁻¹ : ℝ≥0∞) ^ Encodable.encode (i : ℕ))
                  (edist (X n ω i) (Z ω i)) :=
            (ENNReal.sum_add_tsum_compl ..).symm
          _ ≤ (∑ _i ∈ K, δ) +
              ∑' i : {j : ℕ // j ∉ K},
                (2⁻¹ : ℝ≥0∞) ^ Encodable.encode (i : ℕ) := by
            gcongr with i hi
            · exact (min_le_right _ _).trans (hcoord i hi).le
            · exact min_le_left _ _
          _ < ε / 2 + ε / 2 := by
            have hsumδ : ∑ _i ∈ K, δ = δ * (K.card : ℝ≥0∞) := by
              simp [mul_comm]
            rw [hsumδ]
            exact ENNReal.add_lt_add hδsmall hK
          _ = ε := ENNReal.add_halves _
      exact (not_le.mpr hfull) hω
    exact (measure_mono hsub).trans
      (measure_biUnion_finset_le (μ := μ) K (bad · n))

end HeightPaper
