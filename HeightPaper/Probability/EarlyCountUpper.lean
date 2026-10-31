module

public import HeightPaper.Probability.EarlyExtinctionTail
public import HeightPaper.Probability.KernelIteration
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Field.GeomSum

/-! # Exponential upper bounds for the epidemic active-count path -/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace HeightPaper.Model

theorem geometricContraction_monotone_pressure {R x q : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ R) (hq : 1 ≤ q) :
    geometricContraction x q ≤ geometricContraction R q := by
  have hR : 0 ≤ R := hx0.trans hx
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  unfold geometricContraction
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hsq : 0 ≤ q ^ 2 - 1 := by nlinarith
  have hh := mul_nonneg (sub_nonneg.mpr hx) hsq
  have hhh := mul_nonneg hq0.le hh
  nlinarith

theorem one_le_geometricContraction {R q : ℝ} (hR : 1 ≤ R) (hq : 1 ≤ q) :
    1 ≤ geometricContraction R q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  unfold geometricContraction
  apply (one_le_div (by positivity)).mpr
  have hRq : 1 ≤ R * q := by nlinarith
  have hh := mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hRq)
  nlinarith

/-- The un-killed geometric potential with parameter at least one controls
large active counts; absorbed states are included in this inequality. -/
theorem step_upperGeometric_integral_le (rate : ℝ≥0) (s : State) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 1 ≤ q) (hpressure : infectionPressure rate s ≤ R) :
    (∫ t, q ^ infectious t ∂(step rate s).toMeasure) ≤
      geometricContraction R q * q ^ infectious s := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  by_cases ha : s.active.Nonempty
  · rw [step_infectious_power_integral rate s ha hq0]
    have hx : 0 ≤ infectionPressure rate s := by unfold infectionPressure; positivity
    have hb := mul_le_mul_of_nonneg_left
      (geometricContraction_monotone_pressure hx hpressure hq) (pow_nonneg hq0.le (infectious s))
    simpa only [geometricContraction, mul_comm] using hb
  · have hzero : infectious s = 0 := by
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp ha)
    rw [step_absorbed rate (Finset.not_nonempty_iff_eq_empty.mp ha), PMF.toMeasure_pure]
    simpa only [integral_dirac, hzero, pow_zero, mul_one] using one_le_geometricContraction hR hq

/-- A genuine finite-population geometric moment bound under an upper bound
on the initial infection pressure. -/
theorem evolve_upperGeometric_integral_le (rate : ℝ≥0) (n k : ℕ) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 1 ≤ q) (hpressure : (rate : ℝ) * n ≤ R) :
    (∫ s, q ^ infectious s ∂(evolve rate n k).toMeasure) ≤ q * geometricContraction R q ^ k := by
  induction k with
  | zero => simp [evolve, PMF.toMeasure_pure]
  | succ k ih =>
      rw [evolve_integral_succ]
      have hh : (∫ s, (∫ t, q ^ infectious t ∂(step rate s).toMeasure)
          ∂(evolve rate n k).toMeasure) ≤
          ∫ s, geometricContraction R q * q ^ infectious s ∂(evolve rate n k).toMeasure := by
        apply integral_mono_ae (evolve_integrable _ _ _ _) (evolve_integrable _ _ _ _)
        apply FinitePMF.ae_of_forall_mem_support
        intro s hs
        apply step_upperGeometric_integral_le rate s hR hq
        apply le_trans _ hpressure
        unfold infectionPressure
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast evolve_susceptible_le hs) rate.coe_nonneg
      rw [integral_const_mul] at hh
      have hmul := mul_le_mul_of_nonneg_left ih (one_le_geometricContraction hR hq |>.trans' zero_le_one)
      exact hh.trans (by simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul)

/-- An active count above the linear time barrier. -/
def largeActiveCount (c : ℝ) (k : ℕ) : Set State :=
  {s | c * k ≤ (infectious s : ℝ)}

theorem evolve_largeActiveCount_le (rate : ℝ≥0) (n k : ℕ) (c : ℝ)
    {R q : ℝ} (hR : 1 ≤ R) (hq : 1 ≤ q) (hpressure : (rate : ℝ) * n ≤ R) :
    (evolve rate n k).toMeasure.real (largeActiveCount c k) ≤
      q * (geometricContraction R q / q ^ c) ^ k := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hA : 0 < q ^ (c * (k : ℝ)) := Real.rpow_pos_of_pos hq0 _
  have hbound : (∫ s, (largeActiveCount c k).indicator (fun _ ↦ q ^ (c * (k : ℝ))) s
      ∂(evolve rate n k).toMeasure) ≤ ∫ s, q ^ infectious s ∂(evolve rate n k).toMeasure := by
    apply integral_mono (evolve_integrable _ _ _ _) (evolve_integrable _ _ _ _)
    intro s
    by_cases hs : s ∈ largeActiveCount c k
    · rw [Set.indicator_of_mem hs]
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hq hs
    · rw [Set.indicator_of_notMem hs]
      exact pow_nonneg hq0.le _
  rw [integral_indicator_const _ (show MeasurableSet (largeActiveCount c k) from trivial)] at hbound
  simp only [smul_eq_mul] at hbound
  have hmoment := evolve_upperGeometric_integral_le rate n k hR hq hpressure
  have hpow : q ^ (c * (k : ℝ)) = (q ^ c) ^ k := by
    rw [Real.rpow_mul hq0.le, Real.rpow_natCast]
  calc
    _ ≤ (q * geometricContraction R q ^ k) / q ^ (c * (k : ℝ)) :=
      (le_div_iff₀ hA).mpr (hbound.trans hmoment)
    _ = _ := by rw [hpow, div_pow]; ring

/-- A large count somewhere after the chosen starting time. -/
def earlyLargeActivePaths (c : ℝ) (K horizon : ℕ) : Set (FinitePath horizon) :=
  ⋃ k ∈ Finset.Ico K (horizon + 1), {p | p.eval k ∈ largeActiveCount c k}

theorem pathMeasure_earlyLargeActive_le (rate : ℝ≥0) (n horizon K : ℕ) (c : ℝ)
    {R q : ℝ} (hR : 1 ≤ R) (hq : 1 ≤ q)
    (hc : geometricContraction R q < q ^ c) (hpressure : (rate : ℝ) * n ≤ R) :
    (pathMeasure rate n horizon).real (earlyLargeActivePaths c K horizon) ≤
      q * (geometricContraction R q / q ^ c) ^ K /
        (1 - geometricContraction R q / q ^ c) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hδ : 0 ≤ geometricContraction R q / q ^ c :=
    div_nonneg (geometricContraction_pos (zero_le_one.trans hR) hq0).le (Real.rpow_pos_of_pos hq0 c).le
  have hδ1 : geometricContraction R q / q ^ c < 1 :=
    (div_lt_one (Real.rpow_pos_of_pos hq0 c)).mpr hc
  calc
    _ ≤ ∑ k ∈ Finset.Ico K (horizon + 1),
        (pathMeasure rate n horizon).real {p | p.eval k ∈ largeActiveCount c k} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.Ico K (horizon + 1), q * (geometricContraction R q / q ^ c) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkH : k ≤ horizon := by have := (Finset.mem_Ico.mp hk).2; omega
      rw [pathMeasure_event_at rate n horizon k hkH]
      exact evolve_largeActiveCount_le rate n k c hR hq hpressure
    _ = q * ∑ k ∈ Finset.Ico K (horizon + 1), (geometricContraction R q / q ^ c) ^ k := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (geom_sum_Ico_le_of_lt_one (m := K) (n := horizon + 1) hδ hδ1) hq0.le
      simpa only [mul_div_assoc] using hh

end HeightPaper.Model
