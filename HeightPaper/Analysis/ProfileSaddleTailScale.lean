module

public import HeightPaper.Analysis.ProfileSaddleWindow

/-! # Decay after the lattice union bound and the conditional moment root -/

@[expose] public section

open Filter
open scoped Topology

namespace HeightPaper

theorem saddleWindow_outer_scale_le {D C p c a : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hp : 0 < p) (ha : 1 ≤ a) :
    (C * a + 2) * Real.sqrt a *
        (D * (1 + 2 * a) * (2 * Real.exp (-c * a * saddleWindow a ^ 2))) ^ p⁻¹ ≤
      ((C + 2) * (6 * D) ^ p⁻¹) * a ^ ((3 : ℝ) / 2 + p⁻¹) *
        Real.exp (-(c * p⁻¹) * a * saddleWindow a ^ 2) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hb : D * (1 + 2 * a) * (2 * Real.exp (-c * a * saddleWindow a ^ 2)) ≤
      (6 * D * a) * Real.exp (-c * a * saddleWindow a ^ 2) := by
    nlinarith [mul_nonneg hD (Real.exp_pos (-c * a * saddleWindow a ^ 2)).le,
      mul_nonneg (by linarith : 0 ≤ a - 1)
        (mul_nonneg hD (Real.exp_pos (-c * a * saddleWindow a ^ 2)).le)]
  have hpow := Real.rpow_le_rpow (show 0 ≤
      D * (1 + 2 * a) * (2 * Real.exp (-c * a * saddleWindow a ^ 2)) by positivity)
    hb (inv_pos.mpr hp).le
  have hpre : C * a + 2 ≤ (C + 2) * a := by nlinarith
  have hpower : a * a ^ ((1 : ℝ) / 2) * a ^ p⁻¹ = a ^ ((3 : ℝ) / 2 + p⁻¹) := by
    calc
      _ = a ^ (1 : ℝ) * a ^ ((1 : ℝ) / 2) * a ^ p⁻¹ := by rw [Real.rpow_one]
      _ = a ^ ((1 : ℝ) + 1 / 2 + p⁻¹) := by rw [← Real.rpow_add ha0, ← Real.rpow_add ha0]
      _ = _ := by norm_num
  calc
    _ ≤ ((C + 2) * a) * Real.sqrt a *
        ((6 * D * a) * Real.exp (-c * a * saddleWindow a ^ 2)) ^ p⁻¹ :=
      mul_le_mul (mul_le_mul_of_nonneg_right hpre (Real.sqrt_nonneg _)) hpow
        (by positivity) (by positivity)
    _ = ((C + 2) * (6 * D) ^ p⁻¹) * (a * a ^ ((1 : ℝ) / 2) * a ^ p⁻¹) *
        Real.exp (-(c * p⁻¹) * a * saddleWindow a ^ 2) := by
      rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le,
        Real.mul_rpow (by positivity) ha0.le, ← Real.exp_mul, Real.sqrt_eq_rpow]
      rw [show (-c * a * saddleWindow a ^ 2) * p⁻¹ =
        -(c * p⁻¹) * a * saddleWindow a ^ 2 by ring]
      ring
    _ = _ := by rw [hpower]

/-- The complete outer-error scale vanishes, including a linear lattice
cardinality, square-root saddle normalization and the conditional Lp root. -/
theorem saddleWindow_outer_scale_tendsto_zero {D C p c : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hp : 0 < p) (hc : 0 < c) :
    Tendsto (fun a : ℝ => (C * a + 2) * Real.sqrt a *
      (D * (1 + 2 * a) * (2 * Real.exp (-c * a * saddleWindow a ^ 2))) ^ p⁻¹)
      atTop (𝓝 0) := by
  have hh := (saddleWindow_polynomial_tail_tendsto_zero (mul_pos hc (inv_pos.mpr hp))
    ((3 : ℝ) / 2 + p⁻¹)).const_mul ((C + 2) * (6 * D) ^ p⁻¹)
  simp only [mul_zero] at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    simpa only [mul_assoc] using saddleWindow_outer_scale_le hD hC hp ha

end HeightPaper
