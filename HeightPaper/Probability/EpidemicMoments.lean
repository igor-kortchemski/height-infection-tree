module

public import HeightPaper.Probability.EarlyExtinction

/-!
# A complementary geometric test function for the original epidemic

The initial susceptible count bounds infection pressure from above. Consequently
`q ^ I` is subharmonic for `q * rate * n ≤ 1`, and its expectation stays above
its initial value. This will identify the early-extinction mass once surviving
infectious populations are known to be macroscopic.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace HeightPaper.Model

theorem step_support_finite (rate : ℝ≥0) (s : State) : (step rate s).support.Finite := by
  by_cases ha : s.active.Nonempty
  · rw [step_eq_map_stepDraw rate s ha, PMF.support_map]
    exact (Set.toFinite _).image _
  · rw [step_absorbed rate (Finset.not_nonempty_iff_eq_empty.mp ha), PMF.support_pure]
    exact Set.finite_singleton s

theorem evolve_support_finite (rate : ℝ≥0) (n k : ℕ) : (evolve rate n k).support.Finite := by
  induction k with
  | zero => simp only [evolve, PMF.support_pure]; exact Set.finite_singleton _
  | succ k ih => exact FinitePMF.finite_support_bind _ _ ih (fun s _ ↦ step_support_finite _ s)

theorem evolve_integrable (rate : ℝ≥0) (n k : ℕ) (f : State → ℝ) :
    Integrable f (evolve rate n k).toMeasure :=
  FinitePMF.integrable_of_finite_support _ (evolve_support_finite _ _ _) f

theorem evolve_integral_succ (rate : ℝ≥0) (n k : ℕ) (f : State → ℝ) :
    (∫ t, f t ∂(evolve rate n (k + 1)).toMeasure) =
      ∫ s, (∫ t, f t ∂(step rate s).toMeasure) ∂(evolve rate n k).toMeasure :=
  FinitePMF.integral_bind_of_finite_support _ _ (measurable_state _)
    (evolve_support_finite _ _ _) (fun s _ ↦ step_support_finite _ s) f

/-- The infection pressure is bounded above by its initial value. -/
theorem evolve_susceptible_le {rate : ℝ≥0} {n k : ℕ} {s : State}
    (hs : s ∈ (evolve rate n k).support) : s.susceptible ≤ n := by
  have hp := evolve_population hs
  have hv := s.tree.size_pos
  omega

/-- The same exact generating-function identity gives subharmonicity when
infection pressure is bounded above rather than below. -/
theorem step_infectious_power_integral_ge (rate : ℝ≥0) (s : State)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hpressure : infectionPressure rate s * q ≤ 1) :
    q ^ infectious s ≤ (∫ t, q ^ infectious t ∂(step rate s).toMeasure) := by
  by_cases ha : s.active.Nonempty
  · rw [step_infectious_power_integral rate s ha hq]
    have hd : 0 < q * (1 + infectionPressure rate s) := by
      unfold infectionPressure
      positivity
    have hf : 1 ≤ (infectionPressure rate s * q ^ 2 + 1) /
        (q * (1 + infectionPressure rate s)) := by
      apply (one_le_div hd).mpr
      have hh := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hq1) (sub_nonpos.mpr hpressure)
      nlinarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hf (pow_nonneg hq.le _)
  · rw [step_absorbed rate (Finset.not_nonempty_iff_eq_empty.mp ha), PMF.toMeasure_pure]
    simp

/-- The original epidemic's geometric infectious-count moment stays at least
its initial value. This is derived from the actual finite SIR kernel. -/
theorem evolve_infectious_power_integral_ge (rate : ℝ≥0) (n k : ℕ)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hpressure : (rate : ℝ) * n * q ≤ 1) :
    q ≤ (∫ s, q ^ infectious s ∂(evolve rate n k).toMeasure) := by
  induction k with
  | zero => simp [evolve, PMF.toMeasure_pure]
  | succ k ih =>
    rw [evolve_integral_succ]
    apply ih.trans
    apply integral_mono_ae (evolve_integrable _ _ _ _) (evolve_integrable _ _ _ _)
    have hsupp : ∀ᵐ s ∂(evolve rate n k).toMeasure, s ∈ (evolve rate n k).support := by
      apply ae_iff.mpr
      apply (PMF.toMeasure_apply_eq_zero_iff _ (show MeasurableSet {s | s ∉ (evolve rate n k).support} from trivial)).mpr
      exact Set.disjoint_left.mpr (fun s hs hn ↦ hn hs)
    filter_upwards [hsupp] with s hs
    apply step_infectious_power_integral_ge rate s hq hq1
    apply le_trans _ hpressure
    unfold infectionPressure
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast evolve_susceptible_le hs) rate.coe_nonneg) hq.le

/-- The geometric moment differs from extinction probability by at most the
probability of a small positive infectious population and the tail `q ^ M`. -/
theorem evolve_infectious_power_integral_le (rate : ℝ≥0) (n k M : ℕ)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ s, q ^ infectious s ∂(evolve rate n k).toMeasure) ≤
      (evolve rate n k).toMeasure.real {s | infectious s = 0} +
      (evolve rate n k).toMeasure.real {s | 0 < infectious s ∧ infectious s < M} + q ^ M := by
  have hpoint (s : State) : q ^ infectious s ≤
      ({s : State | infectious s = 0}.indicator (fun _ ↦ (1 : ℝ)) s +
       {s : State | 0 < infectious s ∧ infectious s < M}.indicator (fun _ ↦ (1 : ℝ)) s) + q ^ M := by
    by_cases hz : infectious s = 0
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hz, pow_zero, lt_self_iff_false,
        false_and, ↓reduceIte, add_zero]
      have : 0 ≤ q ^ M := pow_nonneg hq _
      linarith
    · by_cases hsmall : infectious s < M
      · have hpos : 0 < infectious s := Nat.pos_of_ne_zero hz
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, hz, hsmall, hpos, and_self,
          ↓reduceIte, zero_add]
        exact (pow_le_one₀ hq hq1).trans (le_add_of_nonneg_right (pow_nonneg hq _))
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hz, hsmall, and_false,
          ↓reduceIte, zero_add]
        exact pow_le_pow_of_le_one hq hq1 (Nat.le_of_not_gt hsmall)
  have h := integral_mono (evolve_integrable rate n k _) (evolve_integrable rate n k _) hpoint
  rw [integral_add (evolve_integrable _ _ _ _) (integrable_const _),
    integral_add (evolve_integrable _ _ _ _) (evolve_integrable _ _ _ _),
    integral_indicator_const (1 : ℝ) (show MeasurableSet {s : State | infectious s = 0} from trivial),
    integral_indicator_const (1 : ℝ) (show MeasurableSet {s : State | 0 < infectious s ∧ infectious s < M} from trivial),
    integral_const, probReal_univ, one_smul] at h
  simpa using h

/-- A finite original-law lower bound for extinction probability, with the only
error being the explicitly measured small positive infectious-population event. -/
theorem evolve_extinction_lower_bound (rate : ℝ≥0) (n k M : ℕ)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hpressure : (rate : ℝ) * n * q ≤ 1) :
    q - q ^ M - (evolve rate n k).toMeasure.real
      {s | 0 < infectious s ∧ infectious s < M} ≤
      (evolve rate n k).toMeasure.real {s | infectious s = 0} := by
  have hl := evolve_infectious_power_integral_ge rate n k hq hq1 hpressure
  have hu := evolve_infectious_power_integral_le rate n k M hq.le hq1
  linarith

end HeightPaper.Model
