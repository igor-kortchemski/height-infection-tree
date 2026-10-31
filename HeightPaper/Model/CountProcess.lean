module

public import HeightPaper.Model.StateMeasure
public import HeightPaper.Model.Profile
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Exact count drifts and the finite-population harmonic invariant

These identities are with respect to the actual SIR transition kernel.
Before susceptible exhaustion, `I + H - harmonic(H) / rate` has zero drift.
Its increments have explicit bounds after stopping above a positive susceptible
threshold. No stochastic fluid limit is assumed in these statements.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace HeightPaper.Model

/-- Real infection pressure in the transition probabilities. -/
def infectionPressure (rate : ℝ≥0) (s : State) : ℝ := (rate : ℝ) * s.susceptible

/-- The exact count transition, integrated against any real observable of the
susceptible and infectious counts. -/
theorem step_integral_counts (rate : ℝ≥0) (s : State) (h : s.active.Nonempty)
    (f : ℕ × ℕ → ℝ) :
    (∫ t, f (counts t) ∂(step rate s).toMeasure) =
      (infectionProbability rate s.susceptible : ℝ) *
        f (if 0 < s.susceptible then (s.susceptible - 1, infectious s + 1)
          else (s.susceptible, infectious s - 1)) +
      (1 - (infectionProbability rate s.susceptible : ℝ)) *
        f (s.susceptible, infectious s - 1) := by
  have hc : Measurable counts := measurable_state counts
  have hf : StronglyMeasurable f := (measurable_of_countable f).stronglyMeasurable
  rw [← integral_map_of_stronglyMeasurable hc hf,
    PMF.toMeasure_map counts (step rate s) hc, step_counts rate s h,
    ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    integral_map_of_stronglyMeasurable (measurable_of_finite _) hf,
    PMF.integral_eq_sum, Fintype.sum_bool]
  have hp : (infectionProbability rate s.susceptible : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast infectionProbability_le_one rate s.susceptible
  simp [eventChoice_true, eventChoice_false, ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top,
    smul_eq_mul]

/-- Integration of an arbitrary real state observable is well-defined: a
single transition has finite support. -/
theorem integrable_step (rate : ℝ≥0) (s : State) (f : State → ℝ) :
    Integrable f (step rate s).toMeasure := by
  by_cases h : s.active.Nonempty
  · rw [step_eq_map_stepDraw rate s h, ← PMF.toMeasure_map _ _ (measurable_of_finite _)]
    exact (integrable_map_measure (measurable_state f).aestronglyMeasurable
      (measurable_of_finite _).aemeasurable).mpr (Integrable.of_finite)
  · rw [step_absorbed rate (Finset.not_nonempty_iff_eq_empty.mp h), PMF.toMeasure_pure]
    exact integrable_dirac (by simp)

theorem infectionProbability_real (rate : ℝ≥0) (s : State) :
    (infectionProbability rate s.susceptible : ℝ) =
      infectionPressure rate s / (1 + infectionPressure rate s) := by
  simp [infectionProbability, infectionPressure]

theorem step_susceptible_drift (rate : ℝ≥0) (s : State) (h : s.active.Nonempty) :
    (∫ t, (t.susceptible : ℝ) - s.susceptible ∂(step rate s).toMeasure) =
      -infectionPressure rate s / (1 + infectionPressure rate s) := by
  have hi := h.card_pos
  have he := step_integral_counts rate s h (fun c ↦ (c.1 : ℝ) - s.susceptible)
  change (∫ t, (t.susceptible : ℝ) - s.susceptible ∂(step rate s).toMeasure) = _ at he
  rw [he]
  by_cases hH : 0 < s.susceptible
  · simp only [hH, ↓reduceIte, Nat.cast_sub (by omega : 1 ≤ s.susceptible), Nat.cast_one]
    rw [infectionProbability_real]
    ring
  · have hH0 : s.susceptible = 0 := by omega
    simp [hH0, infectionPressure]

theorem step_infectious_drift (rate : ℝ≥0) (s : State) (h : s.active.Nonempty) :
    (∫ t, (infectious t : ℝ) - infectious s ∂(step rate s).toMeasure) =
      (infectionPressure rate s - 1) / (1 + infectionPressure rate s) := by
  have hi : 1 ≤ infectious s := h.card_pos
  have he := step_integral_counts rate s h (fun c ↦ (c.2 : ℝ) - infectious s)
  change (∫ t, (infectious t : ℝ) - infectious s ∂(step rate s).toMeasure) = _ at he
  rw [he]
  by_cases hH : 0 < s.susceptible
  · simp only [hH, ↓reduceIte, Nat.cast_sub hi, Nat.cast_add, Nat.cast_one]
    rw [infectionProbability_real]
    have hd : 1 + infectionPressure rate s ≠ 0 := by
      unfold infectionPressure
      positivity
    field_simp
    ring
  · have hH0 : s.susceptible = 0 := by omega
    simp [hH0, infectionPressure, Nat.cast_sub hi]

/-- Natural susceptible counts decrease by at most one in a supported step. -/
theorem susceptible_increment_bounds {rate : ℝ≥0} {s t : State}
    (ht : t ∈ (step rate s).support) :
    -1 ≤ (t.susceptible : ℝ) - s.susceptible ∧
      (t.susceptible : ℝ) - s.susceptible ≤ 0 := by
  rcases step_support_cases ht with ⟨_, rfl⟩ | ⟨v, _, rfl | ⟨hH, rfl⟩⟩
  · simp
  · simp [recover]
  · change -1 ≤ ((s.susceptible - 1 : ℕ) : ℝ) - s.susceptible ∧
      ((s.susceptible - 1 : ℕ) : ℝ) - s.susceptible ≤ 0
    rw [Nat.cast_sub (by omega : 1 ≤ s.susceptible), Nat.cast_one]
    constructor <;> linarith

theorem infectious_increment_abs_le_one {rate : ℝ≥0} {s t : State}
    (ht : t ∈ (step rate s).support) :
    |(infectious t : ℝ) - infectious s| ≤ 1 := by
  rcases step_support_cases ht with ⟨_, rfl⟩ | ⟨v, hv, rfl | ⟨_, rfl⟩⟩
  · simp
  · have hi : 1 ≤ infectious s := Finset.card_pos.mpr ⟨v, hv⟩
    simp [infectious_recover hv, Nat.cast_sub hi]
  · simp [infectious_infect]

/-- Exact finite-population analogue of the deterministic SIR conserved
quantity. Stopping before `H = 0` is necessary for the harmonic identity. -/
noncomputable def finalSizeInvariant (rate : ℝ≥0) (s : State) : ℝ :=
  (infectious s : ℝ) + s.susceptible - (harmonic s.susceptible : ℝ) / rate

private theorem harmonic_pred_real {H : ℕ} (hH : 0 < H) :
    (harmonic (H - 1) : ℝ) = (harmonic H : ℝ) - 1 / H := by
  have h := harmonic_succ (H - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ H)] at h
  have hc := congrArg (fun q : ℚ ↦ (q : ℝ)) h
  push_cast at hc
  simpa only [one_div] using (eq_sub_iff_add_eq.mpr hc.symm)

theorem finalSizeInvariant_infect (rate : ℝ≥0) (s : State) (v : Fin s.vertices)
    (hH : 0 < s.susceptible) :
    finalSizeInvariant rate (infect s v) - finalSizeInvariant rate s =
      1 / ((rate : ℝ) * s.susceptible) := by
  unfold finalSizeInvariant
  rw [infectious_infect]
  change ((infectious s + 1 : ℕ) : ℝ) + ((s.susceptible - 1 : ℕ) : ℝ) -
      (harmonic (s.susceptible - 1) : ℝ) / rate -
      ((infectious s : ℝ) + s.susceptible - (harmonic s.susceptible : ℝ) / rate) = _
  rw [harmonic_pred_real hH, Nat.cast_sub (by omega : 1 ≤ s.susceptible)]
  push_cast
  rw [div_mul_eq_div_div]
  ring

theorem finalSizeInvariant_recover (rate : ℝ≥0) {s : State} {v : Fin s.vertices}
    (hv : v ∈ s.active) :
    finalSizeInvariant rate (recover s v) - finalSizeInvariant rate s = -1 := by
  have hi : 1 ≤ infectious s := Finset.card_pos.mpr ⟨v, hv⟩
  change (infectious (recover s v) : ℝ) + s.susceptible -
    (harmonic s.susceptible : ℝ) / rate -
    ((infectious s : ℝ) + s.susceptible - (harmonic s.susceptible : ℝ) / rate) = -1
  rw [infectious_recover hv, Nat.cast_sub hi, Nat.cast_one]
  ring

/-- The conserved quantity has genuinely zero drift under the actual epidemic
kernel whenever the rate and susceptible count are positive. -/
theorem step_finalSizeInvariant_drift (rate : ℝ≥0) (s : State)
    (h : s.active.Nonempty) (hr : 0 < rate) (hH : 0 < s.susceptible) :
    (∫ t, finalSizeInvariant rate t - finalSizeInvariant rate s ∂(step rate s).toMeasure) = 0 := by
  have hi : 1 ≤ infectious s := h.card_pos
  have he := step_integral_counts rate s h (fun c ↦
    (c.2 : ℝ) + c.1 - (harmonic c.1 : ℝ) / rate - finalSizeInvariant rate s)
  change (∫ t, finalSizeInvariant rate t - finalSizeInvariant rate s ∂(step rate s).toMeasure) = _ at he
  rw [he]
  simp only [hH, ↓reduceIte, Nat.cast_add, Nat.cast_sub hi,
    Nat.cast_sub (by omega : 1 ≤ s.susceptible), Nat.cast_one, harmonic_pred_real hH]
  rw [infectionProbability_real]
  unfold finalSizeInvariant infectionPressure
  have hr0 : (rate : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hH0 : (s.susceptible : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hd : 1 + (rate : ℝ) * s.susceptible ≠ 0 := by positivity
  field_simp
  ring

/-- The corresponding actual one-step expectation preserves the invariant. -/
theorem step_finalSizeInvariant_integral (rate : ℝ≥0) (s : State)
    (h : s.active.Nonempty) (hr : 0 < rate) (hH : 0 < s.susceptible) :
    (∫ t, finalSizeInvariant rate t ∂(step rate s).toMeasure) = finalSizeInvariant rate s := by
  have he := step_finalSizeInvariant_drift rate s h hr hH
  rw [integral_sub (integrable_step _ _ _) (integrable_const _), integral_const,
    probReal_univ, one_smul] at he
  exact sub_eq_zero.mp he

end HeightPaper.Model
