module

public import HeightPaper.Probability.EarlyExtinctionTail
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.PSeries

/-!
# Uniform lower bounds on positive early active counts

The killed geometric moment gives exponential bounds for positive active counts
below a linear barrier. A union bound controls the entire early history, and
then the reciprocal-square tail is deterministically summable off that event.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace HeightPaper.Model

/-- A positive active count below a linear time barrier. -/
def smallActiveCount (c : ℝ) (k : ℕ) : Set State :=
  {s | 0 < infectious s ∧ (infectious s : ℝ) ≤ c * k}

/-- A finite-population exponential lower-tail bound for active counts.
Extinct states are excluded by the killed geometric potential. -/
theorem evolve_smallActiveCount_le (rate : ℝ≥0) (n horizon k : ℕ) (c : ℝ)
    {R q : ℝ} (hR : 0 ≤ R) (hq : 0 < q) (hq1 : q ≤ 1)
    (hpressure : R ≤ (rate : ℝ) * (n - horizon : ℕ)) (hk : k ≤ horizon) :
    (evolve rate n k).toMeasure.real (smallActiveCount c k) ≤
      q * (geometricContraction R q / q ^ c) ^ k := by
  have hA : 0 < q ^ (c * (k : ℝ)) := Real.rpow_pos_of_pos hq _
  have hbound : (∫ s, (smallActiveCount c k).indicator (fun _ ↦ q ^ (c * (k : ℝ))) s
      ∂(evolve rate n k).toMeasure) ≤
      ∫ s, activeGeometric q s ∂(evolve rate n k).toMeasure := by
    apply integral_mono (evolve_integrable _ _ _ _) (evolve_integrable _ _ _ _)
    intro s
    by_cases hs : s ∈ smallActiveCount c k
    · rw [Set.indicator_of_mem hs, activeGeometric, ite_eq_right (Nat.ne_of_gt hs.1)]
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_ge hq hq1 hs.2
    · rw [Set.indicator_of_notMem hs]
      exact activeGeometric_nonneg hq.le s
  rw [integral_indicator_const _ (show MeasurableSet (smallActiveCount c k) from trivial)] at hbound
  simp only [smul_eq_mul] at hbound
  have hmoment := evolve_activeGeometric_integral_le rate n horizon k hR hq hq1 hpressure hk
  have hpow : q ^ (c * (k : ℝ)) = (q ^ c) ^ k := by
    rw [Real.rpow_mul hq.le, Real.rpow_natCast]
  calc
    _ ≤ (q * geometricContraction R q ^ k) / q ^ (c * (k : ℝ)) :=
      (le_div_iff₀ hA).mpr (hbound.trans hmoment)
    _ = _ := by rw [hpow, div_pow]; ring

/-- There is a strictly positive linear slope whose bad-event geometric ratio
is below one whenever the early pressure is uniformly supercritical. -/
theorem exists_positive_count_slope {R q : ℝ} (hR : 0 ≤ R) (hq : 0 < q)
    (hq1 : q < 1) (hRq : 1 < R * q) :
    ∃ c : ℝ, 0 < c ∧ geometricContraction R q < q ^ c := by
  have hρ := geometricContraction_pos hR hq
  have hρ1 := geometricContraction_lt_one hR hq hq1 hRq
  have hlogq : Real.log q < 0 := Real.log_neg hq hq1
  have hlogρ : Real.log (geometricContraction R q) < 0 := Real.log_neg hρ hρ1
  let c := Real.log (geometricContraction R q) / (2 * Real.log q)
  have hc : 0 < c := div_pos_of_neg_of_neg hlogρ (by linarith)
  refine ⟨c, hc, ?_⟩
  rw [Real.rpow_def_of_pos hq]
  have he : Real.log q * c = Real.log (geometricContraction R q) / 2 := by
    dsimp only [c]
    field_simp [ne_of_lt hlogq]
  rw [he]
  calc
    _ = Real.exp (Real.log (geometricContraction R q)) := (Real.exp_log hρ).symm
    _ < _ := Real.exp_lt_exp.mpr (by linarith)

/-- Some positive active count below the linear barrier after time `K`. -/
def earlySmallActivePaths (c : ℝ) (K horizon : ℕ) : Set (FinitePath horizon) :=
  ⋃ k ∈ Finset.Ico K (horizon + 1), {p | p.eval k ∈ smallActiveCount c k}

/-- One geometric estimate controls every coordinate of the actual early
history simultaneously. Constants do not depend on the population or horizon. -/
theorem pathMeasure_earlySmallActive_le (rate : ℝ≥0) (n horizon K : ℕ) (c : ℝ)
    {R q : ℝ} (hR : 0 ≤ R) (hq : 0 < q) (hq1 : q ≤ 1)
    (hc : geometricContraction R q < q ^ c)
    (hpressure : R ≤ (rate : ℝ) * (n - horizon : ℕ)) :
    (pathMeasure rate n horizon).real (earlySmallActivePaths c K horizon) ≤
      q * (geometricContraction R q / q ^ c) ^ K /
        (1 - geometricContraction R q / q ^ c) := by
  have hδ : 0 ≤ geometricContraction R q / q ^ c :=
    div_nonneg (geometricContraction_pos hR hq).le (Real.rpow_pos_of_pos hq c).le
  have hδ1 : geometricContraction R q / q ^ c < 1 :=
    (div_lt_one (Real.rpow_pos_of_pos hq c)).mpr hc
  calc
    _ ≤ ∑ k ∈ Finset.Ico K (horizon + 1),
        (pathMeasure rate n horizon).real {p | p.eval k ∈ smallActiveCount c k} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.Ico K (horizon + 1), q * (geometricContraction R q / q ^ c) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkH : k ≤ horizon := by have := (Finset.mem_Ico.mp hk).2; omega
      rw [pathMeasure_event_at rate n horizon k hkH]
      exact evolve_smallActiveCount_le rate n horizon k c hR hq hq1 hpressure hkH
    _ = q * ∑ k ∈ Finset.Ico K (horizon + 1), (geometricContraction R q / q ^ c) ^ k := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (geom_sum_Ico_le_of_lt_one (m := K) (n := horizon + 1) hδ hδ1) hq.le
      simpa only [mul_div_assoc] using hh

/-- Off the small-count event, the tail of reciprocal squared active counts
is bounded by a deterministic p-series tail. Extinct counts contribute zero
under the field's ordinary inverse convention. -/
theorem reciprocalSquare_tail_le_of_no_small (c : ℝ) (hc : 0 < c) (K horizon : ℕ)
    (p : FinitePath horizon) (hp : p ∉ earlySmallActivePaths c (K + 1) horizon) :
    (∑ k ∈ Finset.Ioo K (horizon + 1), ((infectious (p.eval k) : ℝ) ^ 2)⁻¹) ≤
      2 / (c ^ 2 * (K + 1)) := by
  have hpoint (k : ℕ) (hk : k ∈ Finset.Ioo K (horizon + 1)) :
      ((infectious (p.eval k) : ℝ) ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ * ((k : ℝ) ^ 2)⁻¹ := by
    have hk0 : 0 < k := by have := (Finset.mem_Ioo.mp hk).1; omega
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
    by_cases hI : infectious (p.eval k) = 0
    · simp only [hI, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, inv_zero]
      positivity
    · have hlinear : c * k < (infectious (p.eval k) : ℝ) := by
        apply lt_of_not_ge
        intro hle
        apply hp
        exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨
          Finset.mem_Ico.mpr ⟨by have := (Finset.mem_Ioo.mp hk).1; omega,
            (Finset.mem_Ioo.mp hk).2⟩, ⟨Nat.pos_of_ne_zero hI, hle⟩⟩⟩
      have hsquare : c ^ 2 * (k : ℝ) ^ 2 ≤ (infectious (p.eval k) : ℝ) ^ 2 := by
        simpa only [mul_pow] using
          pow_le_pow_left₀ (mul_pos hc hkR).le hlinear.le 2
      simpa only [mul_inv] using inv_anti₀ (mul_pos (sq_pos_of_pos hc) (sq_pos_of_pos hkR)) hsquare
  calc
    _ ≤ ∑ k ∈ Finset.Ioo K (horizon + 1), (c ^ 2)⁻¹ * ((k : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum hpoint
    _ = (c ^ 2)⁻¹ * ∑ k ∈ Finset.Ioo K (horizon + 1), ((k : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (c ^ 2)⁻¹ * (2 / (K + 1)) :=
      mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le (α := ℝ) K (horizon + 1)) (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv]; ring

/-- The reciprocal-square tail has a uniform exponentially small exceptional
probability. This supplies the random quadratic remainder control in log products. -/
theorem pathMeasure_reciprocalSquare_tail_le (rate : ℝ≥0) (n horizon K : ℕ) (c : ℝ)
    (hcpos : 0 < c) {R q : ℝ} (hR : 0 ≤ R) (hq : 0 < q) (hq1 : q ≤ 1)
    (hc : geometricContraction R q < q ^ c)
    (hpressure : R ≤ (rate : ℝ) * (n - horizon : ℕ)) :
    (pathMeasure rate n horizon).real
      {p | 2 / (c ^ 2 * (K + 1)) <
        ∑ k ∈ Finset.Ioo K (horizon + 1), ((infectious (p.eval k) : ℝ) ^ 2)⁻¹} ≤
      q * (geometricContraction R q / q ^ c) ^ (K + 1) /
        (1 - geometricContraction R q / q ^ c) := by
  apply le_trans (measureReal_mono ?_)
    (pathMeasure_earlySmallActive_le rate n horizon (K + 1) c hR hq hq1 hc hpressure)
  intro p hp
  by_contra hnot
  exact not_lt_of_ge (reciprocalSquare_tail_le_of_no_small c hcpos K horizon p hnot) hp

end HeightPaper.Model
