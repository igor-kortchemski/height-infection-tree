module

public import HeightPaper.Probability.StoppedComparison

/-!
# Early-extinction bounds from the actual SIR kernel

The geometric test function `q ^ I` is superharmonic while infection pressure
is at least `1 / q`. Iterating the stopped kernel gives an exponential bound
on extinction from any initial infectious population. No branching-process
coupling or survival-limit hypothesis is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace HeightPaper.Model

/-- The exact one-step generating function of the infectious count. -/
theorem step_infectious_power_integral (rate : ℝ≥0) (s : State)
    (h : s.active.Nonempty) {q : ℝ} (hq : 0 < q) :
    (∫ t, q ^ infectious t ∂(step rate s).toMeasure) =
      q ^ infectious s * ((infectionPressure rate s * q ^ 2 + 1) /
        (q * (1 + infectionPressure rate s))) := by
  have hi : 1 ≤ infectious s := h.card_pos
  have he := step_integral_counts rate s h (fun c ↦ q ^ c.2)
  change (∫ t, q ^ infectious t ∂(step rate s).toMeasure) = _ at he
  rw [he]
  have hpred : q ^ (infectious s - 1) = q ^ infectious s / q := by
    apply (eq_div_iff hq.ne').mpr
    rw [← pow_succ, Nat.sub_add_cancel hi]
  by_cases hH : 0 < s.susceptible
  · simp only [hH, ↓reduceIte, pow_succ, hpred]
    rw [infectionProbability_real]
    have hd : 1 + infectionPressure rate s ≠ 0 := by unfold infectionPressure; positivity
    field_simp
    ring
  · have hH0 : s.susceptible = 0 := by omega
    simp [hH0, hpred, infectionPressure, div_eq_mul_inv]

/-- A lower infection-pressure bound makes `q ^ I` superharmonic. -/
theorem step_infectious_power_integral_le (rate : ℝ≥0) (s : State)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hpressure : 1 ≤ infectionPressure rate s * q) :
    (∫ t, q ^ infectious t ∂(step rate s).toMeasure) ≤ q ^ infectious s := by
  by_cases ha : s.active.Nonempty
  · rw [step_infectious_power_integral rate s ha hq]
    have hd : 0 < q * (1 + infectionPressure rate s) := by
      unfold infectionPressure
      positivity
    have hf : (infectionPressure rate s * q ^ 2 + 1) /
        (q * (1 + infectionPressure rate s)) ≤ 1 := by
      apply (div_le_one hd).mpr
      have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hq1) (sub_nonneg.mpr hpressure)
      nlinarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hf (pow_nonneg hq.le _)
  · rw [step_absorbed rate (Finset.not_nonempty_iff_eq_empty.mp ha), PMF.toMeasure_pure]
    simp

/-- The stopped kernel has the same superharmonic inequality everywhere. -/
theorem stoppedCountStep_infectious_power_integral_le (rate : ℝ≥0) (threshold : ℕ)
    (s : State) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hpressure : 1 ≤ (rate : ℝ) * threshold * q) :
    (∫ t, q ^ infectious t ∂(stoppedCountStep rate threshold s).toMeasure) ≤
      q ^ infectious s := by
  unfold stoppedCountStep
  split_ifs with hH
  · apply step_infectious_power_integral_le rate s hq hq1
    apply hpressure.trans
    unfold infectionPressure
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hH.1) rate.coe_nonneg) hq.le
  · rw [PMF.toMeasure_pure]
    simp

/-- Iteration gives an exponential moment bound for the infectious count of
the actual stopped epidemic, starting from any state. -/
theorem stoppedCountLaw_infectious_power_integral_le (rate : ℝ≥0) (threshold : ℕ)
    (start : State) (k : ℕ) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hpressure : 1 ≤ (rate : ℝ) * threshold * q) :
    (∫ s, q ^ infectious s ∂(stoppedCountLaw rate threshold start k).toMeasure) ≤
      q ^ infectious start := by
  induction k with
  | zero => simp [stoppedCountLaw, PMF.toMeasure_pure]
  | succ k ih =>
    rw [stoppedCountLaw_integral_succ]
    apply le_trans _ ih
    apply integral_mono (stoppedCountLaw_integrable _ _ _ _ _) (stoppedCountLaw_integrable _ _ _ _ _)
    intro s
    exact stoppedCountStep_infectious_power_integral_le rate threshold s hq hq1 hpressure

/-- Before the susceptible threshold is reached, extinction from `I` infectious
individuals has probability at most `q ^ I`. This is an actual finite-time law
bound, not an assumed branching comparison. -/
theorem stoppedCountLaw_extinction_le (rate : ℝ≥0) (threshold : ℕ)
    (start : State) (k : ℕ) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hpressure : 1 ≤ (rate : ℝ) * threshold * q) :
    (stoppedCountLaw rate threshold start k).toMeasure.real {s | infectious s = 0} ≤
      q ^ infectious start := by
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := (stoppedCountLaw rate threshold start k).toMeasure)
    (f := fun s ↦ q ^ infectious s)
    (Filter.Eventually.of_forall (fun _ ↦ pow_nonneg hq.le _))
    (stoppedCountLaw_integrable _ _ _ _ _) 1
  simp only [one_mul] at hmark
  apply le_trans _ (hmark.trans
    (stoppedCountLaw_infectious_power_integral_le rate threshold start k hq hq1 hpressure))
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro s hs
  change (1 : ℝ) ≤ q ^ infectious s
  rw [hs, pow_zero]

/-- At most one susceptible is lost per event in the original epidemic. -/
theorem evolve_susceptible_lower {rate : ℝ≥0} {n k : ℕ} {s : State}
    (hs : s ∈ (evolve rate n k).support) : n - k ≤ s.susceptible := by
  induction k generalizing s with
  | zero =>
    have heq : s = initial n := by simpa [evolve] using hs
    simp [heq, initial]
  | succ k ih =>
    obtain ⟨t, ht, hstep⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    have hl := ih ht
    rcases step_support_cases hstep with ⟨_, rfl⟩ | ⟨v, _, rfl | ⟨_, rfl⟩⟩
    · omega
    · change n - (k + 1) ≤ t.susceptible
      omega
    · change n - (k + 1) ≤ t.susceptible - 1
      omega

/-- No threshold lower than the worst possible susceptible count can have
been reached by the specified time. -/
theorem evolve_below_threshold_eq_zero (rate : ℝ≥0) (threshold n k : ℕ)
    (hk : k + threshold ≤ n) :
    (evolve rate n k).toMeasure {s | s.susceptible < threshold} = 0 := by
  apply (PMF.toMeasure_apply_eq_zero_iff _ (show MeasurableSet {s : State | s.susceptible < threshold} from trivial)).mpr
  apply Set.disjoint_left.mpr
  intro s hs hbelow
  have hlow := evolve_susceptible_lower hs
  change s.susceptible < threshold at hbelow
  omega

/-- Direct early-extinction bound for the original epidemic started from
patient zero. There is no stopped-process approximation error on this horizon. -/
theorem evolve_early_extinction_le (rate : ℝ≥0) (threshold n k : ℕ)
    (hthreshold : 0 < threshold) (hk : k + threshold ≤ n)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hpressure : 1 ≤ (rate : ℝ) * threshold * q) :
    (evolve rate n k).toMeasure.real {s | infectious s = 0} ≤ q := by
  have hcomp := evolve_measureReal_le_stopped rate threshold n k hthreshold {s | infectious s = 0}
  have hext := stoppedCountLaw_extinction_le rate threshold (initial n) k hq hq1 hpressure
  have hzero : (evolve rate n k).toMeasure.real {s | s.susceptible < threshold} = 0 := by
    simp only [measureReal_def, evolve_below_threshold_eq_zero rate threshold n k hk, ENNReal.toReal_zero]
  rw [hzero, add_zero] at hcomp
  exact hcomp.trans (by simpa using hext)

end HeightPaper.Model
