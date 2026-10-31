module

public import HeightPaper.Model.CountProcess

/-!
# Stopped harmonic-invariant fluctuations

The actual one-step conditional variance of the harmonic invariant is
`1 / (rate * H)`. Stopping when susceptibles fall below a positive threshold
therefore gives a uniform variance bound, without assuming a fluid limit.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace HeightPaper.Model

/-- Exact second moment of the centered harmonic-invariant increment. -/
theorem step_finalSizeInvariant_sq_increment (rate : ℝ≥0) (s : State)
    (h : s.active.Nonempty) (hr : 0 < rate) (hH : 0 < s.susceptible) :
    (∫ t, (finalSizeInvariant rate t - finalSizeInvariant rate s) ^ 2
      ∂(step rate s).toMeasure) = 1 / ((rate : ℝ) * s.susceptible) := by
  obtain ⟨v, hv⟩ := h
  let g : ℕ × ℕ → ℝ := fun c ↦
    (c.2 : ℝ) + c.1 - (harmonic c.1 : ℝ) / rate - finalSizeInvariant rate s
  have hb : g (s.susceptible - 1, infectious s + 1) =
      1 / ((rate : ℝ) * s.susceptible) := by
    have hb' := finalSizeInvariant_infect rate s v hH
    unfold finalSizeInvariant at hb'
    rw [infectious_infect] at hb'
    exact hb' 
  have hd : g (s.susceptible, infectious s - 1) = -1 := by
    have hd' := finalSizeInvariant_recover rate hv
    unfold finalSizeInvariant at hd'
    rw [infectious_recover hv] at hd'
    exact hd'
  have he := step_integral_counts rate s ⟨v, hv⟩ (fun c ↦ (g c) ^ 2)
  change (∫ t, (finalSizeInvariant rate t - finalSizeInvariant rate s) ^ 2
    ∂(step rate s).toMeasure) = _ at he
  rw [he]
  simp only [hH, ↓reduceIte, hb, hd]
  rw [infectionProbability_real]
  unfold infectionPressure
  have hr0 : (rate : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hH0 : (s.susceptible : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hden : 1 + (rate : ℝ) * s.susceptible ≠ 0 := by positivity
  field_simp
  ring

/-- Every supported increment lies in the exact infection/recovery interval. -/
theorem finalSizeInvariant_increment_mem {rate : ℝ≥0} {s t : State}
    (hr : 0 < rate) (hH : 0 < s.susceptible) (ht : t ∈ (step rate s).support) :
    finalSizeInvariant rate t - finalSizeInvariant rate s ∈
      Icc (-1 : ℝ) (1 / ((rate : ℝ) * s.susceptible)) := by
  have hbound : 0 < 1 / ((rate : ℝ) * s.susceptible) := by positivity
  rcases step_support_cases ht with ⟨_, rfl⟩ | ⟨v, hv, rfl | ⟨_, rfl⟩⟩
  · simp only [sub_self, mem_Icc]
    exact ⟨by norm_num, hbound.le⟩
  · rw [finalSizeInvariant_recover rate hv]
    exact ⟨le_rfl, by linarith⟩
  · rw [finalSizeInvariant_infect rate s v hH]
    exact ⟨by linarith, le_rfl⟩

/-- The embedded epidemic stopped as soon as the susceptible count is below
`threshold` (or is zero). Absorbed epidemic states remain absorbed as before. -/
noncomputable def stoppedCountStep (rate : ℝ≥0) (threshold : ℕ) (s : State) : PMF State :=
  if threshold ≤ s.susceptible ∧ 0 < s.susceptible then step rate s else PMF.pure s

theorem stoppedCountStep_integrable (rate : ℝ≥0) (threshold : ℕ) (s : State)
    (f : State → ℝ) : Integrable f (stoppedCountStep rate threshold s).toMeasure := by
  unfold stoppedCountStep
  split_ifs
  · exact integrable_step rate s f
  · rw [PMF.toMeasure_pure]
    exact integrable_dirac (by simp)

/-- The stopped kernel preserves the harmonic invariant at every state,
including extinct epidemics and states where the stopping threshold was hit. -/
theorem stoppedCountStep_finalSizeInvariant_integral (rate : ℝ≥0) (threshold : ℕ)
    (s : State) (hr : 0 < rate) :
    (∫ t, finalSizeInvariant rate t ∂(stoppedCountStep rate threshold s).toMeasure) =
      finalSizeInvariant rate s := by
  unfold stoppedCountStep
  split_ifs with hH
  · by_cases ha : s.active.Nonempty
    · exact step_finalSizeInvariant_integral rate s ha hr hH.2
    · rw [step_absorbed rate (Finset.not_nonempty_iff_eq_empty.mp ha), PMF.toMeasure_pure]
      exact integral_dirac _ _
  · rw [PMF.toMeasure_pure]
    exact integral_dirac _ _

theorem stoppedCountStep_finalSizeInvariant_drift (rate : ℝ≥0) (threshold : ℕ)
    (s : State) (hr : 0 < rate) :
    (∫ t, finalSizeInvariant rate t - finalSizeInvariant rate s
      ∂(stoppedCountStep rate threshold s).toMeasure) = 0 := by
  rw [integral_sub (stoppedCountStep_integrable _ _ _ _) (integrable_const _),
    stoppedCountStep_finalSizeInvariant_integral rate threshold s hr,
    integral_const, probReal_univ, one_smul, sub_self]

/-- A threshold bounds the conditional variance uniformly by the reciprocal
infection pressure at that threshold. -/
theorem stoppedCountStep_finalSizeInvariant_sq_le (rate : ℝ≥0) (threshold : ℕ)
    (s : State) (hr : 0 < rate) (hthreshold : 0 < threshold) :
    (∫ t, (finalSizeInvariant rate t - finalSizeInvariant rate s) ^ 2
      ∂(stoppedCountStep rate threshold s).toMeasure) ≤
      1 / ((rate : ℝ) * threshold) := by
  have hc : 0 < 1 / ((rate : ℝ) * threshold) := by positivity
  unfold stoppedCountStep
  split_ifs with hH
  · by_cases ha : s.active.Nonempty
    · rw [step_finalSizeInvariant_sq_increment rate s ha hr hH.2]
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hH.1) rate.coe_nonneg
    · rw [step_absorbed rate (Finset.not_nonempty_iff_eq_empty.mp ha), PMF.toMeasure_pure]
      simpa using hc.le
  · rw [PMF.toMeasure_pure]
    simpa using hc.le

/-- Uniform supported-increment bound for the stopped kernel. -/
theorem stoppedCountStep_increment_abs_le {rate : ℝ≥0} {threshold : ℕ}
    {s t : State} (hr : 0 < rate) (hthreshold : 0 < threshold)
    (ht : t ∈ (stoppedCountStep rate threshold s).support) :
    |finalSizeInvariant rate t - finalSizeInvariant rate s| ≤
      max 1 (1 / ((rate : ℝ) * threshold)) := by
  have hc : 0 < 1 / ((rate : ℝ) * threshold) := by positivity
  unfold stoppedCountStep at ht
  split_ifs at ht with hH
  · have hb := finalSizeInvariant_increment_mem hr hH.2 ht
    apply abs_le.mpr
    constructor
    · exact (neg_le_neg (le_max_left _ _)).trans hb.1
    · apply hb.2.trans
      apply le_trans _ (le_max_right _ _)
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hH.1) rate.coe_nonneg
  · have heq : t = s := by simpa using ht
    subst t
    rw [sub_self, abs_zero]
    exact zero_le_one.trans (le_max_left 1 (1 / ((rate : ℝ) * threshold)))

/-- The stopped transition still has finite support. -/
theorem stoppedCountStep_support_finite (rate : ℝ≥0) (threshold : ℕ) (s : State) :
    (stoppedCountStep rate threshold s).support.Finite := by
  unfold stoppedCountStep
  split_ifs
  · by_cases ha : s.active.Nonempty
    · rw [step_eq_map_stepDraw rate s ha, PMF.support_map]
      exact (Set.toFinite _).image _
    · rw [step_absorbed rate (Finset.not_nonempty_iff_eq_empty.mp ha), PMF.support_pure]
      exact Set.finite_singleton s
  · rw [PMF.support_pure]
    exact Set.finite_singleton s

/-- Centering at any fixed initial value gives the usual variance increment
identity, proved here directly for the actual stopped transition. -/
theorem stoppedCountStep_sq_about (rate : ℝ≥0) (threshold : ℕ) (s : State)
    (hr : 0 < rate) (a : ℝ) :
    (∫ t, (finalSizeInvariant rate t - a) ^ 2 ∂(stoppedCountStep rate threshold s).toMeasure) =
      (finalSizeInvariant rate s - a) ^ 2 +
      (∫ t, (finalSizeInvariant rate t - finalSizeInvariant rate s) ^ 2
        ∂(stoppedCountStep rate threshold s).toMeasure) := by
  have heq (t : State) : (finalSizeInvariant rate t - a) ^ 2 =
      ((finalSizeInvariant rate t - finalSizeInvariant rate s) ^ 2 +
      2 * (finalSizeInvariant rate s - a) *
        (finalSizeInvariant rate t - finalSizeInvariant rate s)) +
      (finalSizeInvariant rate s - a) ^ 2 := by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall heq)]
  rw [integral_add (stoppedCountStep_integrable _ _ _ _) (integrable_const _),
    integral_add (stoppedCountStep_integrable _ _ _ _) (stoppedCountStep_integrable _ _ _ _),
    integral_const_mul, stoppedCountStep_finalSizeInvariant_drift rate threshold s hr,
    integral_const, probReal_univ, one_smul]
  ring

end HeightPaper.Model
