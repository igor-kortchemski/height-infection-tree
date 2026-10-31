module

public import HeightPaper.Probability.GhostBudgetTreeMarginal
public import HeightPaper.Probability.StoppedComparison
public import HeightPaper.Model.KernelPathMarginal

/-!
# Stopped count comparison from the active-padded state

The stopped and unstopped kernels agree above a susceptible threshold for
every initial state. At the first crossing from the padded state, the harmonic
invariant has a deterministic lower barrier with an explicit padding cost.
-/

@[expose] public section

set_option maxHeartbeats 500000

open MeasureTheory Set
open scoped NNReal ENNReal

namespace HeightPaper.Model

theorem stoppedCountLaw_apply_of_above_start (rate : ℝ≥0)
    (threshold : ℕ) (start : State) (k : ℕ)
    (hthreshold : 0 < threshold) {t : State} (ht : threshold ≤ t.susceptible) :
    stoppedCountLaw rate threshold start k t =
      FinitePMF.kernelEvolve (PMF.pure start) (fun _ ↦ step rate) k t := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    simp only [stoppedCountLaw, FinitePMF.kernelEvolve, PMF.bind_apply]
    apply tsum_congr
    intro s
    rw [stoppedCountStep_apply_of_above hthreshold ht]
    by_cases hs : threshold ≤ s.susceptible
    · rw [ih hs]
    · rw [step_apply_eq_zero_of_susceptible_lt
        (show s.susceptible < t.susceptible by omega)]
      simp

theorem stoppedCountLaw_measure_above_start (rate : ℝ≥0)
    (threshold : ℕ) (start : State) (k : ℕ)
    (hthreshold : 0 < threshold) (A : Set State) :
    (stoppedCountLaw rate threshold start k).toMeasure
        (A ∩ {s | threshold ≤ s.susceptible}) =
      (FinitePMF.kernelEvolve (PMF.pure start) (fun _ ↦ step rate) k).toMeasure
        (A ∩ {s | threshold ≤ s.susceptible}) := by
  rw [PMF.toMeasure_apply _ (show MeasurableSet
      (A ∩ {s : State | threshold ≤ s.susceptible}) from trivial),
    PMF.toMeasure_apply _ (show MeasurableSet
      (A ∩ {s : State | threshold ≤ s.susceptible}) from trivial)]
  apply tsum_congr
  intro s
  by_cases hs : s ∈ A ∩ {s | threshold ≤ s.susceptible}
  · simp only [Set.indicator_of_mem hs]
    exact stoppedCountLaw_apply_of_above_start rate threshold start k hthreshold hs.2
  · simp only [Set.indicator_of_notMem hs]

theorem stoppedCountLaw_measure_below_start (rate : ℝ≥0)
    (threshold : ℕ) (start : State) (k : ℕ)
    (hthreshold : 0 < threshold) :
    (stoppedCountLaw rate threshold start k).toMeasure
        {s | s.susceptible < threshold} =
      (FinitePMF.kernelEvolve (PMF.pure start) (fun _ ↦ step rate) k).toMeasure
        {s | s.susceptible < threshold} := by
  have heq := stoppedCountLaw_measure_above_start rate threshold start k
    hthreshold Set.univ
  simp only [Set.univ_inter] at heq
  have hset : {s : State | s.susceptible < threshold} =
      {s | threshold ≤ s.susceptible}ᶜ := by
    ext s
    simp
  rw [hset, measure_compl (show MeasurableSet
      {s : State | threshold ≤ s.susceptible} from trivial) (measure_ne_top _ _),
    measure_compl (show MeasurableSet
      {s : State | threshold ≤ s.susceptible} from trivial) (measure_ne_top _ _),
    measure_univ, measure_univ, heq]

/-- The original stopping barrier loses exactly `H` when the initial active
population is padded by `H` vertices. -/
theorem ghostBudget_stopped_below_barrier (rate : ℝ≥0)
    (threshold n H k : ℕ) (hthreshold : threshold ≤ n)
    {s : State}
    (hs : s ∈ (stoppedCountLaw rate threshold (ghostBudgetStart n H) k).support)
    (hbelow : s.susceptible < threshold) :
    stoppingBarrier rate n threshold - H ≤
      finalSizeInvariant rate s - finalSizeInvariant rate (ghostBudgetStart n H) := by
  have hlow := stoppedCountLaw_susceptible_lower rate threshold
    (ghostBudgetStart n H) (by simpa using hthreshold) k hs
  have hS : s.susceptible = threshold - 1 := by omega
  have hI : (0 : ℝ) ≤ infectious s := Nat.cast_nonneg _
  unfold stoppingBarrier finalSizeInvariant
  rw [ghostBudgetStart_susceptible, ghostBudgetStart_infectious, hS]
  push_cast
  rw [sub_div]
  linarith

theorem ghostBudget_stopped_below_probability_le (rate : ℝ≥0)
    (threshold n H k : ℕ) (hr : 0 < rate)
    (hthreshold : 0 < threshold) (hthresholdN : threshold ≤ n)
    (hbarrier : 0 < stoppingBarrier rate n threshold - H) :
    (stoppedCountLaw rate threshold (ghostBudgetStart n H) k).toMeasure.real
      {s | s.susceptible < threshold} ≤
        (k : ℝ) / ((rate : ℝ) * threshold *
          (stoppingBarrier rate n threshold - H) ^ 2) := by
  have htail := stoppedCountLaw_finalSizeInvariant_tail_le rate threshold
    (ghostBudgetStart n H) hr hthreshold k hbarrier
  apply le_trans _ htail
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply (stoppedCountLaw rate threshold (ghostBudgetStart n H) k).toMeasure_mono
    (show MeasurableSet
    {s : State | s.susceptible < threshold} from trivial)
  intro s ⟨hbelow, hs⟩
  have hb := ghostBudget_stopped_below_barrier rate threshold n H k
    hthresholdN hs hbelow
  exact hb.trans (le_abs_self _)

end HeightPaper.Model
