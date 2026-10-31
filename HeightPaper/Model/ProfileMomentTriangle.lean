module

public import HeightPaper.Model.ProfileLimitMomentBound

/-! # Conditional moment of a difference from two component moments -/

@[expose] public section

open MeasureTheory

namespace HeightPaper.Model

theorem integral_norm_sub_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℂ} {p : ℝ} (hp : 1 ≤ p)
    (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable (fun ω ↦ ‖f ω‖ ^ p) μ)
    (hgi : Integrable (fun ω ↦ ‖g ω‖ ^ p) μ) :
    Integrable (fun ω ↦ ‖f ω - g ω‖ ^ p) μ ∧
      (∫ ω, ‖f ω - g ω‖ ^ p ∂μ) ≤
        (2 : ℝ) ^ (p - 1) *
          ((∫ ω, ‖f ω‖ ^ p ∂μ) + (∫ ω, ‖g ω‖ ^ p ∂μ)) := by
  have hpower (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      (a + b) ^ p ≤ (2 : ℝ) ^ (p - 1) * (a ^ p + b ^ p) := by
    lift a to NNReal using ha
    lift b to NNReal using hb
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow a b hp
  have hc : 0 ≤ (2 : ℝ) ^ (p - 1) := Real.rpow_nonneg (by norm_num) _
  have hpoint (ω : Ω) : ‖f ω - g ω‖ ^ p ≤
      (2 : ℝ) ^ (p - 1) * (‖f ω‖ ^ p + ‖g ω‖ ^ p) := by
    calc
      ‖f ω - g ω‖ ^ p ≤ (‖f ω‖ + ‖g ω‖) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le _ _) (zero_le_one.trans hp)
      _ ≤ _ := hpower _ _ (norm_nonneg _) (norm_nonneg _)
  have hdom : Integrable
      (fun ω ↦ (2 : ℝ) ^ (p - 1) * (‖f ω‖ ^ p + ‖g ω‖ ^ p)) μ :=
    (hfi.add hgi).const_mul _
  have htarget : Integrable (fun ω ↦ ‖f ω - g ω‖ ^ p) μ := by
    apply Integrable.mono' hdom
      ((Real.continuous_rpow_const (zero_le_one.trans hp)).measurable.comp
        (hf.sub hg).norm).aestronglyMeasurable
    filter_upwards with ω
    simpa only [Function.comp_apply, Pi.sub_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (f ω - g ω)) p),
      abs_of_nonneg (mul_nonneg hc (add_nonneg
        (Real.rpow_nonneg (norm_nonneg (f ω)) p)
        (Real.rpow_nonneg (norm_nonneg (g ω)) p)))] using hpoint ω
  refine ⟨htarget, ?_⟩
  calc
    (∫ ω, ‖f ω - g ω‖ ^ p ∂μ) ≤
      ∫ ω, (2 : ℝ) ^ (p - 1) * (‖f ω‖ ^ p + ‖g ω‖ ^ p) ∂μ :=
      integral_mono_ae htarget hdom (ae_of_all _ hpoint)
    _ = _ := by rw [integral_const_mul, integral_add hfi hgi]

end HeightPaper.Model
