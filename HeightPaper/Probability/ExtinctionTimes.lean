module

public import HeightPaper.Probability.EarlyExtinction
public import HeightPaper.Model.PathMeasure

/-!
# Extinction between two observation times

An infectious population loses at most one individual per event. Under the
actual joint path law, extinction between two times therefore forces the
population at the earlier time to be positive but no larger than the gap.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace HeightPaper.Model

/-- At most one infectious individual is lost by a supported transition. -/
theorem infectious_le_step_add_one {rate : ℝ≥0} {s t : State}
    (ht : t ∈ (step rate s).support) : infectious s ≤ infectious t + 1 := by
  rcases step_support_cases ht with ⟨_, rfl⟩ | ⟨v, hv, rfl | ⟨_, rfl⟩⟩
  · omega
  · rw [infectious_recover hv]
    omega
  · rw [infectious_infect]
    omega

namespace SupportedPath

/-- The number of recoveries cannot exceed the number of elapsed events. -/
theorem infectious_le_later_add_gap {rate : ℝ≥0} {n steps : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n steps path) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps) :
    infectious (path i) ≤ infectious (path j) + (j - i) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have hh := ih (by omega)
    have hl := infectious_le_step_add_one (hp.2 j (by omega))
    omega

/-- Extinction is an absorbing event along every supported path. -/
theorem infectious_eq_zero_later {rate : ℝ≥0} {n steps : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n steps path) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps)
    (hi : infectious (path i) = 0) : infectious (path j) = 0 := by
  have ha : (path i).active = ∅ := Finset.card_eq_zero.mp hi
  rw [hp.absorbed_stable hij hj ha]
  exact hi

/-- If an earlier state is still active, a later extinct state must have
experienced more genuine events than the earlier observation time. -/
theorem active_earlier_lt_eventCount {rate : ℝ≥0} {n steps : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n steps path) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps)
    (hi : 0 < infectious (path i)) (hz : infectious (path j) = 0) :
    i < eventCount (path j) := by
  have hne : i ≠ j := by intro h; subst j; omega
  have hij' : i < j := lt_of_le_of_ne hij hne
  have ha : (path i).active.Nonempty := Finset.card_pos.mp hi
  have he := evolve_eventCount_eq_of_active (hp.mem_evolve (hij.trans hj)) ha
  have hs := eventCount_step ha (hp.2 i (lt_of_lt_of_le hij' hj))
  have hm := hp.eventCount_mono (i := i + 1) (j := j) (by omega) hj
  omega

end SupportedPath

/-- Event probabilities at a path coordinate are the original state-law
probabilities, with no extra path hypothesis. -/
theorem pathMeasure_event_at (rate : ℝ≥0) (n steps k : ℕ) (hk : k ≤ steps)
    (A : Set State) :
    (pathMeasure rate n steps).real {p | p.eval k ∈ A} =
      (evolve rate n k).toMeasure.real A := by
  rw [← pathMeasure_map_at rate n steps k hk]
  simp only [measureReal_def,
    Measure.map_apply (FinitePath.measurable _) (show MeasurableSet A from trivial)]
  rfl

/-- The extinction probabilities are nondecreasing in the number of events. -/
theorem evolve_extinction_mono (rate : ℝ≥0) (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    (evolve rate n i).toMeasure.real {s | infectious s = 0} ≤
      (evolve rate n j).toMeasure.real {s | infectious s = 0} := by
  rw [← pathMeasure_event_at rate n j i hij, ← pathMeasure_event_at rate n j j le_rfl]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {p : FinitePath j | infectious (p.eval i) = 0} from trivial)
  intro p hp
  have hs := (mem_support_pathLaw_iff p).mp hp.2
  exact hs.infectious_eq_zero_later hij le_rfl hp.1

/-- Extinction after time `i` requires at most `j-i` infectious individuals at
that earlier time. This finite bound supplies the no-late-extinction step. -/
theorem evolve_extinction_le_earlier_add_small (rate : ℝ≥0) (n : ℕ)
    {i j : ℕ} (hij : i ≤ j) :
    (evolve rate n j).toMeasure.real {s | infectious s = 0} ≤
      (evolve rate n i).toMeasure.real {s | infectious s = 0} +
      (evolve rate n i).toMeasure.real {s | 0 < infectious s ∧ infectious s ≤ j - i} := by
  rw [← pathMeasure_event_at rate n j j le_rfl,
    ← pathMeasure_event_at rate n j i hij {s | infectious s = 0},
    ← pathMeasure_event_at rate n j i hij {s | 0 < infectious s ∧ infectious s ≤ j - i}]
  apply le_trans _ (measureReal_union_le _ _)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {p : FinitePath j | infectious (p.eval j) = 0} from trivial)
  intro p hp
  have hs := (mem_support_pathLaw_iff p).mp hp.2
  by_cases hi : infectious (p.eval i) = 0
  · exact Or.inl hi
  · apply Or.inr
    have hl := hs.infectious_le_later_add_gap hij le_rfl
    have hz : infectious (p.eval j) = 0 := hp.1
    exact ⟨Nat.pos_of_ne_zero hi, by omega⟩

/-- A later extinction either already happened at the earlier observation or
has a genuine event count larger than that earlier time. -/
theorem evolve_extinction_le_earlier_add_late (rate : ℝ≥0) (n : ℕ)
    {i j : ℕ} (hij : i ≤ j) :
    (evolve rate n j).toMeasure.real {s | infectious s = 0} ≤
      (evolve rate n i).toMeasure.real {s | infectious s = 0} +
      (evolve rate n j).toMeasure.real {s | infectious s = 0 ∧ i < eventCount s} := by
  rw [← pathMeasure_event_at rate n j j le_rfl {s | infectious s = 0},
    ← pathMeasure_event_at rate n j i hij {s | infectious s = 0},
    ← pathMeasure_event_at rate n j j le_rfl {s | infectious s = 0 ∧ i < eventCount s}]
  apply le_trans _ (measureReal_union_le _ _)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {p : FinitePath j | infectious (p.eval j) = 0} from trivial)
  intro p hp
  have hs := (mem_support_pathLaw_iff p).mp hp.2
  by_cases hi : infectious (p.eval i) = 0
  · exact Or.inl hi
  · exact Or.inr ⟨hp.1, hs.active_earlier_lt_eventCount hij le_rfl (Nat.pos_of_ne_zero hi) hp.1⟩

end HeightPaper.Model
