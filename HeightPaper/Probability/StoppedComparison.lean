module

public import HeightPaper.Probability.StoppedFluid

/-!
# Comparing stopped and original epidemic laws

Susceptibles never increase. Therefore the stopped and original kernels have
identical finite-time laws above the stopping threshold and identical total
probability of falling below it. The stopped count can cross the threshold by
only one individual, making the harmonic-invariant barrier explicit.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace HeightPaper.Model

theorem susceptible_step_le {rate : ℝ≥0} {s t : State}
    (ht : t ∈ (step rate s).support) : t.susceptible ≤ s.susceptible := by
  rcases step_support_cases ht with ⟨_, rfl⟩ | ⟨v, _, rfl | ⟨_, rfl⟩⟩
  · exact le_rfl
  · exact le_rfl
  · exact Nat.sub_le _ _

theorem step_apply_eq_zero_of_susceptible_lt {rate : ℝ≥0} {s t : State}
    (hlt : s.susceptible < t.susceptible) : step rate s t = 0 := by
  by_contra h
  exact (not_le_of_gt hlt) (susceptible_step_le (show t ∈ (step rate s).support from h))

theorem stoppedCountStep_apply_of_above {rate : ℝ≥0} {threshold : ℕ} {s t : State}
    (hthreshold : 0 < threshold) (ht : threshold ≤ t.susceptible) :
    stoppedCountStep rate threshold s t = step rate s t := by
  unfold stoppedCountStep
  split_ifs with hs
  · rfl
  · have hslt : s.susceptible < threshold := by
      by_contra hn
      have hle : threshold ≤ s.susceptible := by omega
      exact hs ⟨hle, hthreshold.trans_le hle⟩
    have hlt := hslt.trans_le ht
    have hne : t ≠ s := by
      intro heq
      rw [heq] at hlt
      exact (lt_irrefl _ hlt)
    rw [step_apply_eq_zero_of_susceptible_lt hlt]
    simp [PMF.pure_apply, hne]

/-- The two finite-time laws agree pointwise at every state at or above the
stopping threshold. -/
theorem stoppedCountLaw_apply_of_above (rate : ℝ≥0) (threshold n k : ℕ)
    (hthreshold : 0 < threshold) {t : State} (ht : threshold ≤ t.susceptible) :
    stoppedCountLaw rate threshold (initial n) k t = evolve rate n k t := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    simp only [stoppedCountLaw, evolve, PMF.bind_apply]
    apply tsum_congr
    intro s
    rw [stoppedCountStep_apply_of_above hthreshold ht]
    by_cases hs : threshold ≤ s.susceptible
    · rw [ih hs]
    · rw [step_apply_eq_zero_of_susceptible_lt
        (show s.susceptible < t.susceptible by omega)]
      simp

/-- Any measurable event restricted to states above the threshold has the same
probability in the original and stopped processes. -/
theorem stoppedCountLaw_measure_above (rate : ℝ≥0) (threshold n k : ℕ)
    (hthreshold : 0 < threshold) (A : Set State) :
    (stoppedCountLaw rate threshold (initial n) k).toMeasure
        (A ∩ {s | threshold ≤ s.susceptible}) =
      (evolve rate n k).toMeasure (A ∩ {s | threshold ≤ s.susceptible}) := by
  rw [PMF.toMeasure_apply _ (show MeasurableSet (A ∩ {s : State | threshold ≤ s.susceptible}) from trivial),
    PMF.toMeasure_apply _ (show MeasurableSet (A ∩ {s : State | threshold ≤ s.susceptible}) from trivial)]
  apply tsum_congr
  intro s
  by_cases hs : s ∈ A ∩ {s | threshold ≤ s.susceptible}
  · simp only [Set.indicator_of_mem hs]
    exact stoppedCountLaw_apply_of_above rate threshold n k hthreshold hs.2
  · simp only [Set.indicator_of_notMem hs]

/-- Falling below the threshold has exactly the same probability for the
stopped and original epidemics, despite their different states after crossing. -/
theorem stoppedCountLaw_measure_below (rate : ℝ≥0) (threshold n k : ℕ)
    (hthreshold : 0 < threshold) :
    (stoppedCountLaw rate threshold (initial n) k).toMeasure {s | s.susceptible < threshold} =
      (evolve rate n k).toMeasure {s | s.susceptible < threshold} := by
  have heq := stoppedCountLaw_measure_above rate threshold n k hthreshold Set.univ
  simp only [Set.univ_inter] at heq
  have hset : {s : State | s.susceptible < threshold} = {s | threshold ≤ s.susceptible}ᶜ := by
    ext s
    simp
  rw [hset, measure_compl (show MeasurableSet {s : State | threshold ≤ s.susceptible} from trivial) (measure_ne_top _ _),
    measure_compl (show MeasurableSet {s : State | threshold ≤ s.susceptible} from trivial) (measure_ne_top _ _),
    measure_univ, measure_univ, heq]

/-- Any original-law event is controlled by its stopped-law probability plus
the probability of reaching the stopping region. -/
theorem evolve_measureReal_le_stopped (rate : ℝ≥0) (threshold n k : ℕ)
    (hthreshold : 0 < threshold) (A : Set State) :
    (evolve rate n k).toMeasure.real A ≤
      (stoppedCountLaw rate threshold (initial n) k).toMeasure.real A +
      (evolve rate n k).toMeasure.real {s | s.susceptible < threshold} := by
  have hcover : A ⊆ (A ∩ {s : State | threshold ≤ s.susceptible}) ∪
      {s | s.susceptible < threshold} := by
    intro s hs
    by_cases hH : threshold ≤ s.susceptible
    · exact Or.inl ⟨hs, hH⟩
    · exact Or.inr (Nat.lt_of_not_ge hH)
  have h1 := measureReal_mono (μ := (evolve rate n k).toMeasure) hcover
  have h2 := measureReal_union_le (μ := (evolve rate n k).toMeasure)
    (A ∩ {s : State | threshold ≤ s.susceptible}) {s | s.susceptible < threshold}
  have h3 := measureReal_mono (μ := (stoppedCountLaw rate threshold (initial n) k).toMeasure)
    (Set.inter_subset_left (s := A) (t := {s : State | threshold ≤ s.susceptible}))
  have heq : (evolve rate n k).toMeasure.real (A ∩ {s | threshold ≤ s.susceptible}) =
      (stoppedCountLaw rate threshold (initial n) k).toMeasure.real
        (A ∩ {s | threshold ≤ s.susceptible}) := by
    exact congrArg ENNReal.toReal (stoppedCountLaw_measure_above rate threshold n k hthreshold A).symm
  rw [heq] at h2
  linarith

/-- The stopped chain crosses by at most one susceptible individual. -/
theorem stoppedCountLaw_susceptible_lower (rate : ℝ≥0) (threshold : ℕ) (start : State)
    (hstart : threshold ≤ start.susceptible) (k : ℕ) {s : State}
    (hs : s ∈ (stoppedCountLaw rate threshold start k).support) :
    threshold - 1 ≤ s.susceptible := by
  induction k generalizing s with
  | zero =>
    have heq : s = start := by simpa [stoppedCountLaw] using hs
    rw [heq]
    omega
  | succ k ih =>
    obtain ⟨t, ht, hstep⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    unfold stoppedCountStep at hstep
    split_ifs at hstep with hH
    · rcases step_support_cases hstep with ⟨_, rfl⟩ | ⟨v, _, rfl | ⟨_, rfl⟩⟩
      · exact ih ht
      · change threshold - 1 ≤ t.susceptible
        exact ih ht
      · change threshold - 1 ≤ t.susceptible - 1
        omega
    · have heq : s = t := by simpa using hstep
      rw [heq]
      exact ih ht

theorem stoppedCountLaw_below_susceptible_eq (rate : ℝ≥0) (threshold n k : ℕ)
    (ha : threshold ≤ n) {s : State}
    (hs : s ∈ (stoppedCountLaw rate threshold (initial n) k).support)
    (hbelow : s.susceptible < threshold) : s.susceptible = threshold - 1 := by
  have hlow := stoppedCountLaw_susceptible_lower rate threshold (initial n) ha k hs
  omega

/-- The minimum possible invariant change at first crossing of the susceptible
threshold, attained when there are no infectious individuals left. -/
noncomputable def stoppingBarrier (rate : ℝ≥0) (n threshold : ℕ) : ℝ :=
  ((threshold - 1 : ℕ) : ℝ) - (n + 1 : ℕ) -
    ((harmonic (threshold - 1) : ℝ) - harmonic n) / rate

theorem stoppingBarrier_le_increment (rate : ℝ≥0) (threshold n k : ℕ)
    (ha : threshold ≤ n) {s : State}
    (hs : s ∈ (stoppedCountLaw rate threshold (initial n) k).support)
    (hbelow : s.susceptible < threshold) :
    stoppingBarrier rate n threshold ≤
      finalSizeInvariant rate s - finalSizeInvariant rate (initial n) := by
  have hH := stoppedCountLaw_below_susceptible_eq rate threshold n k ha hs hbelow
  unfold stoppingBarrier finalSizeInvariant
  rw [infectious_initial]
  simp only [initial, Nat.cast_one]
  rw [hH, sub_div]
  push_cast
  have hi : (0 : ℝ) ≤ infectious s := Nat.cast_nonneg _
  linarith

/-- An explicit finite-population bound for the *original* epidemic reaching
a low susceptible threshold. The only assumptions concern positive deterministic
parameters and the explicit barrier, not a stochastic concentration estimate. -/
theorem evolve_below_threshold_le (rate : ℝ≥0) (threshold n k : ℕ)
    (hr : 0 < rate) (hthreshold : 0 < threshold) (ha : threshold ≤ n)
    (hbarrier : 0 < stoppingBarrier rate n threshold) :
    (evolve rate n k).toMeasure.real {s | s.susceptible < threshold} ≤
      (k : ℝ) / ((rate : ℝ) * threshold * (stoppingBarrier rate n threshold) ^ 2) := by
  rw [measureReal_def, ← stoppedCountLaw_measure_below rate threshold n k hthreshold]
  change (stoppedCountLaw rate threshold (initial n) k).toMeasure.real
    {s | s.susceptible < threshold} ≤ _
  apply le_trans _ (stoppedCountLaw_finalSizeInvariant_tail_le rate threshold (initial n)
    hr hthreshold k hbarrier)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {s : State | s.susceptible < threshold} from trivial)
  intro s hs
  exact (stoppingBarrier_le_increment rate threshold n k ha hs.2 hs.1).trans (le_abs_self _)

end HeightPaper.Model
