module

public import HeightPaper.Probability.TreeUniformCoupling

/-!
# Joint probability bounds from conditional bounds

A uniformly bounded conditional error outside a bad outer event lifts to the
product probability space, with the bad-event probability added explicitly.
Null measurability suffices for the joint event.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

theorem prod_le_bad_add_of_ae_section_le (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set (Ω × Ξ)} (hE : NullMeasurableSet E (μ.prod ν))
    {B : Set Ω} (hB : MeasurableSet B) {C : ℝ≥0∞}
    (hbound : ∀ᵐ u ∂μ, u ∉ B → ν {v | (u, v) ∈ E} ≤ C) :
    μ.prod ν E ≤ μ B + C := by
  rw [prod_apply₀ hE]
  calc
    _ ≤ ∫⁻ u, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) u + C ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with u hu
      have hsection : Prod.mk u ⁻¹' E = {v | (u, v) ∈ E} := by ext v; rfl
      rw [hsection]
      by_cases huB : u ∈ B
      · have hh : ν {v | (u, v) ∈ E} ≤ 1 := by
          simpa only [measure_univ] using (measure_mono (Set.subset_univ {v | (u, v) ∈ E}) :
            ν {v | (u, v) ∈ E} ≤ ν Set.univ)
        simpa only [Set.indicator_of_mem huB] using hh.trans
          (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ C from zero_le))
      · simpa only [Set.indicator_of_notMem huB, zero_add] using hu huB
    _ = μ B + C := by
      rw [lintegral_add_left ((measurable_const : Measurable (fun _ : Ω ↦ (1 : ℝ≥0∞))).indicator hB),
        lintegral_indicator hB]
      simp

theorem prod_real_le_bad_add_of_ae_section_real_le (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set (Ω × Ξ)} (hE : NullMeasurableSet E (μ.prod ν))
    {B : Set Ω} (hB : MeasurableSet B) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ u ∂μ, u ∉ B → ν.real {v | (u, v) ∈ E} ≤ C) :
    (μ.prod ν).real E ≤ μ.real B + C := by
  have hh := prod_le_bad_add_of_ae_section_le μ ν hE hB (C := ENNReal.ofReal C) ?_
  · have ht := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩) hh
    simpa only [Measure.real, ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hC] using ht
  · filter_upwards [hbound] with u hu hB'
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hC, Measure.real] using hu hB'

end MeasureTheory.Measure

namespace HeightPaper.CountCoupling

theorem birthParentLaw_real_le_bad_add {E : Set ((ℕ → ℝ) × (ℕ → ℝ))}
    (hE : NullMeasurableSet E birthParentLaw) {B : Set (ℕ → ℝ)} (hB : MeasurableSet B)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ u ∂uniformLaw, u ∉ B → uniformLaw.real {v | (u, v) ∈ E} ≤ C) :
    birthParentLaw.real E ≤ uniformLaw.real B + C :=
  MeasureTheory.Measure.prod_real_le_bad_add_of_ae_section_real_le
    uniformLaw uniformLaw hE hB hC hbound

end HeightPaper.CountCoupling
