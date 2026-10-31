module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Passing between linear and logarithmic count scales -/

public section

open Filter
open scoped Topology

namespace HeightPaper

variable {ι : Type*} {ℓ : Filter ι} {X scale : ι → ℝ}

/-- A nonnegative count with logarithmic exponent below one is negligible
relative to the population. Zero counts are allowed. -/
theorem tendsto_div_zero_of_log_ratio_lt_one
    (hscale : Tendsto scale ℓ atTop) (hX : ∀ᶠ i in ℓ, 0 ≤ X i)
    {f : ℝ} (hf : f < 1)
    (hlog : Tendsto (fun i ↦ Real.log (X i) / Real.log (scale i)) ℓ (𝓝 f)) :
    Tendsto (fun i ↦ X i / scale i) ℓ (𝓝 0) := by
  obtain ⟨r, hfr, hr⟩ := exists_between hf
  have hln := Real.tendsto_log_atTop.comp hscale
  have hexp : Tendsto (fun i ↦ Real.exp ((r - 1) * Real.log (scale i))) ℓ (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (sub_neg.mpr hr) hln)
  apply squeeze_zero' _ _ hexp
  · filter_upwards [hX, hscale.eventually_gt_atTop 1] with i hi hs
    exact div_nonneg hi (zero_lt_one.trans hs).le
  · filter_upwards [hlog.eventually_lt_const hfr, hscale.eventually_gt_atTop 1]
      with i hi hs
    have hs0 := zero_lt_one.trans hs
    have hlogle : Real.log (X i) ≤ r * Real.log (scale i) :=
      ((div_lt_iff₀ (Real.log_pos hs)).mp hi).le
    calc
      X i / scale i ≤ Real.exp (Real.log (X i)) / scale i :=
        div_le_div_of_nonneg_right (Real.le_exp_log _) hs0.le
      _ ≤ Real.exp (r * Real.log (scale i)) / scale i :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hlogle) hs0.le
      _ = Real.exp ((r - 1) * Real.log (scale i)) := by
        calc
          _ = Real.exp (r * Real.log (scale i)) / Real.exp (Real.log (scale i)) := by
            rw [Real.exp_log hs0]
          _ = _ := by rw [← Real.exp_sub]; congr 1; ring

/-- A positive limiting fraction has logarithmic exponent one. -/
theorem tendsto_log_ratio_one_of_div_pos
    (hscale : Tendsto scale ℓ atTop) {c : ℝ} (hc : 0 < c)
    (hX : Tendsto (fun i ↦ X i / scale i) ℓ (𝓝 c)) :
    Tendsto (fun i ↦ Real.log (X i) / Real.log (scale i)) ℓ (𝓝 1) := by
  have hln := Real.tendsto_log_atTop.comp hscale
  have hl : Tendsto (fun i ↦ Real.log (X i / scale i)) ℓ (𝓝 (Real.log c)) :=
    (Real.continuousAt_log hc.ne').tendsto.comp hX
  have ht := (hl.div_atTop hln).add_const 1
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [hscale.eventually_gt_atTop 1, hX.eventually_const_lt hc] with i hs hi
  have hs0 := zero_lt_one.trans hs
  have hx : 0 < X i := (div_pos_iff_of_pos_right hs0).mp hi
  rw [Real.log_div hx.ne' hs0.ne']
  simp only [Function.comp_apply]
  field_simp [(Real.log_pos hs).ne']
  ring

end HeightPaper
