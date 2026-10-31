module

public import HeightPaper.Model.CountFluctuation
public import HeightPaper.Probability.FinitePMF
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Concentration of the stopped finite-population SIR invariant

This constructs the actual iterated stopped kernel and proves a mean-square
bound and a Chebyshev bound from its exact conditional moments. Its normalized
fluctuations vanish on linear event horizons whenever infection pressure at the
stopping threshold is bounded away from zero.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace HeightPaper.Model

/-- Actual law of the SIR chain stopped below a positive susceptible threshold. -/
noncomputable def stoppedCountLaw (rate : ℝ≥0) (threshold : ℕ) (start : State) : ℕ → PMF State
  | 0 => PMF.pure start
  | k + 1 => (stoppedCountLaw rate threshold start k).bind (stoppedCountStep rate threshold)

theorem stoppedCountLaw_support_finite (rate : ℝ≥0) (threshold : ℕ) (start : State) (k : ℕ) :
    (stoppedCountLaw rate threshold start k).support.Finite := by
  induction k with
  | zero => simp only [stoppedCountLaw, PMF.support_pure]; exact Set.finite_singleton start
  | succ k ih =>
    exact FinitePMF.finite_support_bind _ _ ih (fun s _ ↦ stoppedCountStep_support_finite _ _ s)

theorem stoppedCountLaw_integrable (rate : ℝ≥0) (threshold : ℕ) (start : State) (k : ℕ)
    (f : State → ℝ) : Integrable f (stoppedCountLaw rate threshold start k).toMeasure :=
  FinitePMF.integrable_of_finite_support _ (stoppedCountLaw_support_finite _ _ _ _) f

/-- Iterated expectation for this particular stopped epidemic. -/
theorem stoppedCountLaw_integral_succ (rate : ℝ≥0) (threshold : ℕ) (start : State) (k : ℕ)
    (f : State → ℝ) :
    (∫ t, f t ∂(stoppedCountLaw rate threshold start (k + 1)).toMeasure) =
      ∫ s, (∫ t, f t ∂(stoppedCountStep rate threshold s).toMeasure)
        ∂(stoppedCountLaw rate threshold start k).toMeasure :=
  FinitePMF.integral_bind_of_finite_support _ _ (measurable_state _)
    (stoppedCountLaw_support_finite _ _ _ _) (fun s _ ↦ stoppedCountStep_support_finite _ _ s) f

/-- The stopped invariant has its initial mean after every finite number of events. -/
theorem stoppedCountLaw_finalSizeInvariant_mean (rate : ℝ≥0) (threshold : ℕ)
    (start : State) (hr : 0 < rate) (k : ℕ) :
    (∫ s, finalSizeInvariant rate s ∂(stoppedCountLaw rate threshold start k).toMeasure) =
      finalSizeInvariant rate start := by
  induction k with
  | zero => simp [stoppedCountLaw, PMF.toMeasure_pure]
  | succ k ih =>
    rw [stoppedCountLaw_integral_succ]
    simp_rw [stoppedCountStep_finalSizeInvariant_integral rate threshold _ hr]
    exact ih

/-- Conditional variances accumulate linearly, proved directly from the exact
kernel moments rather than assumed as a martingale estimate. -/
theorem stoppedCountLaw_finalSizeInvariant_sq_le (rate : ℝ≥0) (threshold : ℕ)
    (start : State) (hr : 0 < rate) (hthreshold : 0 < threshold) (k : ℕ) :
    (∫ s, (finalSizeInvariant rate s - finalSizeInvariant rate start) ^ 2
      ∂(stoppedCountLaw rate threshold start k).toMeasure) ≤
      (k : ℝ) / ((rate : ℝ) * threshold) := by
  induction k with
  | zero => simp [stoppedCountLaw, PMF.toMeasure_pure]
  | succ k ih =>
    rw [stoppedCountLaw_integral_succ]
    calc
      _ ≤ ∫ s, (finalSizeInvariant rate s - finalSizeInvariant rate start) ^ 2 +
          1 / ((rate : ℝ) * threshold)
          ∂(stoppedCountLaw rate threshold start k).toMeasure := by
        apply integral_mono (stoppedCountLaw_integrable _ _ _ _ _)
          (stoppedCountLaw_integrable _ _ _ _ _)
        intro s
        dsimp only
        rw [stoppedCountStep_sq_about rate threshold s hr]
        have hb := stoppedCountStep_finalSizeInvariant_sq_le rate threshold s hr hthreshold
        linarith
      _ = (∫ s, (finalSizeInvariant rate s - finalSizeInvariant rate start) ^ 2
          ∂(stoppedCountLaw rate threshold start k).toMeasure) +
          1 / ((rate : ℝ) * threshold) := by
        rw [integral_add (stoppedCountLaw_integrable _ _ _ _ _) (integrable_const _),
          integral_const, probReal_univ, one_smul]
      _ ≤ (k : ℝ) / ((rate : ℝ) * threshold) + 1 / ((rate : ℝ) * threshold) :=
        by linarith
      _ = _ := by push_cast; ring

/-- Quantitative concentration around the initial harmonic invariant. -/
theorem stoppedCountLaw_finalSizeInvariant_tail_le (rate : ℝ≥0) (threshold : ℕ)
    (start : State) (hr : 0 < rate) (hthreshold : 0 < threshold) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    (stoppedCountLaw rate threshold start k).toMeasure.real
      {s | ε ≤ |finalSizeInvariant rate s - finalSizeInvariant rate start|} ≤
        (k : ℝ) / ((rate : ℝ) * threshold * ε ^ 2) := by
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := (stoppedCountLaw rate threshold start k).toMeasure)
    (f := fun s ↦ (finalSizeInvariant rate s - finalSizeInvariant rate start) ^ 2)
    (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
    (stoppedCountLaw_integrable _ _ _ _ _) (ε ^ 2)
  have hevent : {s : State | ε ^ 2 ≤ (finalSizeInvariant rate s - finalSizeInvariant rate start) ^ 2} =
      {s | ε ≤ |finalSizeInvariant rate s - finalSizeInvariant rate start|} := by
    ext s
    change ε ^ 2 ≤ (finalSizeInvariant rate s - finalSizeInvariant rate start) ^ 2 ↔
      ε ≤ |finalSizeInvariant rate s - finalSizeInvariant rate start|
    simpa only [sq_abs] using (sq_le_sq₀ hε.le (abs_nonneg (finalSizeInvariant rate s - finalSizeInvariant rate start)))
  rw [hevent] at hmark
  have hle := hmark.trans (stoppedCountLaw_finalSizeInvariant_sq_le rate threshold start hr hthreshold k)
  rw [div_mul_eq_div_div]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  simpa only [mul_comm] using hle

/-- On a linear event horizon, the actual stopped invariant divided by the
population scale concentrates at its initial value. The deterministic rate
assumptions are precisely a positive limiting pressure at the threshold and a
finite limiting number of events per individual. -/
theorem stoppedCountLaw_normalized_concentration
    (rates : ℕ → ℝ≥0) (threshold horizon : ℕ → ℕ) (start : ℕ → State)
    {ρ T : ℝ} (hρ : 0 < ρ)
    (hpressure : Tendsto (fun n ↦ (rates n : ℝ) * threshold n) atTop (𝓝 ρ))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (stoppedCountLaw (rates n) (threshold n) (start n) (horizon n)).toMeasure.real
      {s | ε ≤ |(finalSizeInvariant (rates n) s - finalSizeInvariant (rates n) (start n)) / n|})
      atTop (𝓝 0) := by
  let bound : ℕ → ℝ := fun n ↦ (horizon n : ℝ) /
    ((rates n : ℝ) * threshold n * (ε * n) ^ 2)
  have hbound : Tendsto bound atTop (𝓝 0) := by
    have hh := (hhorizon.div (hpressure.mul_const (ε ^ 2))
      (mul_ne_zero hρ.ne' (pow_ne_zero _ hε.ne'))).mul
      (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
    have hz : T / (ρ * ε ^ 2) * 0 = 0 := mul_zero _
    rw [hz] at hh
    convert hh using 1
    funext n
    dsimp [bound]
    ring
  have hevent : ∀ᶠ n in atTop, (0 : ℝ) < (rates n : ℝ) * threshold n ∧ 0 < n := by
    filter_upwards [hpressure.eventually (Ioi_mem_nhds hρ), eventually_gt_atTop 0] with n hn hN
    exact ⟨hn, hN⟩
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hbound
  filter_upwards [hevent] with n hn
  have hr : 0 < rates n := by
    have hprod := hn.1
    have ha : (0 : ℝ) ≤ threshold n := Nat.cast_nonneg _
    have hr0 : (0 : ℝ) < (rates n : ℝ) := by nlinarith
    exact_mod_cast hr0
  have ha : 0 < threshold n := by
    have hprod := hn.1
    have hr0 := (rates n).coe_nonneg
    have ha0 : (0 : ℝ) < threshold n := by nlinarith
    exact_mod_cast ha0
  have hN : (0 : ℝ) < n := by exact_mod_cast hn.2
  have htail := stoppedCountLaw_finalSizeInvariant_tail_le (rates n) (threshold n)
    (start n) hr ha (horizon n) (mul_pos hε hN)
  convert htail using 2
  ext s
  change ε ≤ |(finalSizeInvariant (rates n) s - finalSizeInvariant (rates n) (start n)) / n| ↔
    ε * n ≤ |finalSizeInvariant (rates n) s - finalSizeInvariant (rates n) (start n)|
  rw [abs_div, abs_of_pos hN, le_div_iff₀ hN]

end HeightPaper.Model
