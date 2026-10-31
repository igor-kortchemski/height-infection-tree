module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The source saddle window and its decay rates

The choice `a^(-5/12)` makes the cubic remainder vanish while the squared
Gaussian width diverges. Polynomial factors, including the retained
logarithmic factor in the general Fourier moment bound, are dominated by
the resulting stretched exponential.
-/

@[expose] public section

open Filter
open scoped Topology

namespace HeightPaper

noncomputable def saddleWindow (a : ℝ) : ℝ := a ^ (-(5 : ℝ) / 12)

theorem saddleWindow_pos {a : ℝ} (ha : 0 < a) : 0 < saddleWindow a :=
  Real.rpow_pos_of_pos ha _

theorem saddleWindow_le_one {a : ℝ} (ha : 1 ≤ a) : saddleWindow a ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos ha (by norm_num)

theorem saddleWindow_tendsto_zero : Tendsto saddleWindow atTop (𝓝 0) := by
  change Tendsto (fun a : ℝ => a ^ (-(5 : ℝ) / 12)) atTop (𝓝 0)
  simpa only [neg_div] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 12))

theorem saddleWindow_cubic {a : ℝ} (ha : 0 < a) :
    a * saddleWindow a ^ 3 = a ^ (-(1 : ℝ) / 4) := by
  calc
    _ = a ^ (1 : ℝ) * a ^ ((-(5 : ℝ) / 12) * (3 : ℝ)) := by
      rw [Real.rpow_one, Real.rpow_mul ha.le]
      norm_num [saddleWindow]
    _ = a ^ ((1 : ℝ) + (-(5 : ℝ) / 12) * (3 : ℝ)) := (Real.rpow_add ha _ _).symm
    _ = _ := by norm_num

theorem saddleWindow_quadratic {a : ℝ} (ha : 0 < a) :
    a * saddleWindow a ^ 2 = a ^ ((1 : ℝ) / 6) := by
  calc
    _ = a ^ (1 : ℝ) * a ^ ((-(5 : ℝ) / 12) * (2 : ℝ)) := by
      rw [Real.rpow_one, Real.rpow_mul ha.le]
      norm_num [saddleWindow]
    _ = a ^ ((1 : ℝ) + (-(5 : ℝ) / 12) * (2 : ℝ)) := (Real.rpow_add ha _ _).symm
    _ = _ := by norm_num

theorem saddleWindow_cubic_tendsto_zero :
    Tendsto (fun a : ℝ => a * saddleWindow a ^ 3) atTop (𝓝 0) := by
  have hh := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  simpa only [neg_div] using (saddleWindow_cubic ha).symm

theorem saddleWindow_quadratic_tendsto_atTop :
    Tendsto (fun a : ℝ => a * saddleWindow a ^ 2) atTop atTop := by
  apply (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  exact (saddleWindow_quadratic ha).symm

theorem saddleWindow_eventually_cubic_small (θ : ℝ) :
    ∀ᶠ a : ℝ in atTop, a * θ * saddleWindow a ^ 3 ≤ 1 := by
  have hh := saddleWindow_cubic_tendsto_zero.const_mul θ
  simp only [mul_zero] at hh
  filter_upwards [hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with a ha
  nlinarith only [ha]

/-- A polynomial is dominated by any stretched exponential with positive
power and positive decay coefficient. -/
theorem tendsto_rpow_mul_exp_neg_rpow {q c : ℝ} (hq : 0 < q) (hc : 0 < c) (s : ℝ) :
    Tendsto (fun a : ℝ => a ^ s * Real.exp (-c * a ^ q)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / q) c hc).comp
    (tendsto_rpow_atTop hq)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
  simp only [Function.comp_def, ← Real.rpow_mul ha]
  rw [show q * (s / q) = s by field_simp]

/-- This handles every polynomial loss in the full Fourier moment bound,
including the harmonic factor that occurs at the critical exponent. -/
theorem saddleWindow_polynomial_tail_tendsto_zero {c : ℝ} (hc : 0 < c) (s : ℝ) :
    Tendsto (fun a : ℝ => a ^ s * Real.exp (-c * a * saddleWindow a ^ 2)) atTop (𝓝 0) := by
  apply (tendsto_rpow_mul_exp_neg_rpow (by norm_num : (0 : ℝ) < 1 / 6) hc s).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  rw [← saddleWindow_quadratic ha]
  congr 2
  ring

theorem saddleWindow_scaled_gaussian_tail_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun a : ℝ => Real.sqrt a * Real.exp (-c * a * saddleWindow a ^ 2))
      atTop (𝓝 0) := by
  simpa only [Real.sqrt_eq_rpow] using saddleWindow_polynomial_tail_tendsto_zero hc (1 / 2)

end HeightPaper
