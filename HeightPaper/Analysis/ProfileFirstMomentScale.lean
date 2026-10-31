module

public import HeightPaper.Analysis.Parameters
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Vanishing first-moment bounds at logarithmic height scales -/

public section

open Filter
open scoped Topology

namespace HeightPaper

theorem tendsto_nat_rpow_negative {a : ℝ} (ha : a < 0) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a) atTop (𝓝 0) := by
  simpa only [neg_neg, Function.comp_def] using
    (tendsto_rpow_neg_atTop (neg_pos.mpr ha)).comp tendsto_natCast_atTop_atTop

theorem tendsto_nat_rpow_ratio_zero {a b : ℝ} (hab : a < b) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a / (n : ℝ) ^ b) atTop (𝓝 0) := by
  apply (tendsto_nat_rpow_negative (sub_neg.mpr hab)).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.rpow_sub (by exact_mod_cast hn)]

theorem tendsto_profile_firstMoment_height_bound (horizon : ℕ → ℕ) {T w b c : ℝ}
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    (hc : 0 < c) (hgap : 1 + b < c) :
    Tendsto (fun n : ℕ ↦ (1 + w * horizon n * (n : ℝ) ^ b) / (n : ℝ) ^ c)
      atTop (𝓝 0) := by
  have h0 := tendsto_nat_rpow_negative (neg_neg_of_pos hc)
  have h1 := (hhorizon.const_mul w).mul (tendsto_nat_rpow_negative (sub_neg.mpr hgap))
  simp only [mul_zero] at h1
  have hh := h0.add h1
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 := hnR.ne'
  rw [Real.rpow_neg hnR.le, Real.rpow_sub hnR, Real.rpow_add hnR,
    Real.rpow_one]
  have hp : (n : ℝ) ^ c ≠ 0 := (Real.rpow_pos_of_pos hnR c).ne'
  field_simp

/-- The critical tilt exactly balances the power of the total-profile first
moment with the pre-cutoff height coefficient. -/
theorem profileRoot_height_balance {l : ℝ} (hl : 1 < l) :
    1 + growthFactor l * (Real.exp (profileRoot l) - 1) =
      profileRoot l * (growthFactor l * Real.exp (profileRoot l)) := by
  have hh := profileExponent_profileRoot hl
  unfold profileExponent at hh
  nlinarith only [hh]

end HeightPaper
