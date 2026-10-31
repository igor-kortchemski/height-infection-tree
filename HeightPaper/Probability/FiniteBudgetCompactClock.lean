module

public import HeightPaper.Probability.GhostBudgetClockConcentration
public import HeightPaper.Probability.FiniteBudgetFluidLocation

/-!
# Clock concentration uniformly over a compact rate interval

The stopped variance bound has a parameter-independent upper bound whenever
the rate stays above a fixed positive value. The low-susceptible event is
largest at the upper endpoint under the common-uniform coupling.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace HeightPaper.CountCoupling

theorem budgetClock_above_uniform_bound_tendsto_zero
    (a₀ : ℝ≥0) (horizon : ℕ → ℕ) {T c ε : ℝ}
    (ha₀ : 0 < a₀) (hc : 0 < c) (hε : 0 < ε)
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    Tendsto (fun n : ℕ ↦ (horizon n : ℝ) /
      (((a₀ / n : ℝ≥0) : ℝ) * fluidThreshold c n * (ε * n) ^ 2))
      atTop (𝓝 0) := by
  let rates : ℕ → ℝ≥0 := fun n ↦ a₀ / n
  let threshold : ℕ → ℕ := fun n ↦ fluidThreshold c n
  have ha₀R : (0 : ℝ) < a₀ := by exact_mod_cast ha₀
  have hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 (a₀ : ℝ)) := by
    apply (tendsto_const_nhds (x := (a₀ : ℝ))).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [rates, NNReal.coe_div, NNReal.coe_natCast, div_mul_cancel₀ _ hnR]
  have hpressure := Model.tendsto_fluidThreshold_pressure rates hc.le hrates
  have ht := (hhorizon.div (hpressure.mul_const (ε ^ 2))
      (mul_ne_zero (mul_ne_zero ha₀R.ne' hc.ne') (pow_ne_zero _ hε.ne'))).mul
    (tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  dsimp [rates, threshold]
  field_simp

theorem finiteSusceptible_budgetClockError_above_uniform_le
    (a₀ a : ℝ≥0) (n H threshold : ℕ)
    (ha₀ : 0 < a₀) (haa₀ : a₀ ≤ a)
    (hn : 0 < n) (hthreshold : 0 < threshold)
    {ε : ℝ} (hε : 0 < ε) :
    uniformLaw.real {u | threshold ≤ finiteSusceptible (a : ℝ) n u H ∧
      ε ≤ |budgetClockError (a / n) n (finiteSusceptible (a : ℝ) n u H) H / n|} ≤
      (H : ℝ) / (((a₀ / n : ℝ≥0) : ℝ) * threshold * (ε * n) ^ 2) := by
  have ha : 0 < a := ha₀.trans_le haa₀
  have hraw := finiteSusceptible_budgetClockError_above_le a n H threshold
    ha hn hthreshold hε
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrate : ((a₀ / n : ℝ≥0) : ℝ) ≤ ((a / n : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_div, NNReal.coe_natCast]
    exact div_le_div_of_nonneg_right (by exact_mod_cast haa₀) hnR.le
  have hrate0 : (0 : ℝ) < ((a₀ / n : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_div, NNReal.coe_natCast]
    exact div_pos (by exact_mod_cast ha₀) hnR
  have hden0 : (0 : ℝ) < ((a₀ / n : ℝ≥0) : ℝ) * threshold * (ε * n) ^ 2 := by
    positivity
  have hden : ((a₀ / n : ℝ≥0) : ℝ) * threshold * (ε * n) ^ 2 ≤
      ((a / n : ℝ≥0) : ℝ) * threshold * (ε * n) ^ 2 := by
    gcongr
  exact hraw.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg H) hden0 hden)

end HeightPaper.CountCoupling
