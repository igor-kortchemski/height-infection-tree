module

public import HeightPaper.Model.InfectionTree
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Measures and event counts for the finite SIR chain

The state space carries the discrete sigma algebra. Pushforwards below identify
its terminal tree-height observable with the previously defined height law.
-/

@[expose] public section
open scoped NNReal ENNReal
open MeasureTheory

namespace HeightPaper.Model

instance : MeasurableSpace State := ⊤

instance : MeasurableSingletonClass State where
  measurableSet_singleton _ := trivial

/-- Every observable on the discrete state space is measurable. -/
theorem measurable_state {α : Type*} [MeasurableSpace α] (f : State → α) : Measurable f :=
  fun _ _ => trivial

/-- The measure of the final state of an epidemic with `n` initial susceptibles. -/
noncomputable def terminalStateMeasure (rate : ℝ≥0) (n : ℕ) : Measure State :=
  (evolve rate n (2 * n + 1)).toMeasure

instance (rate : ℝ≥0) (n : ℕ) : IsProbabilityMeasure (terminalStateMeasure rate n) := by
  unfold terminalStateMeasure
  infer_instance

/-- The terminal state height has exactly `heightLaw` as its distribution. -/
theorem terminalStateMeasure_map_height (rate : ℝ≥0) (n : ℕ) :
    (terminalStateMeasure rate n).map height = (heightLaw rate n).toMeasure := by
  exact PMF.toMeasure_map height _ (measurable_state height)

/-- The normalized terminal height law, as a pushforward from the state space. -/
theorem terminalStateMeasure_map_normalizedHeight (rate : ℝ≥0) (n : ℕ) :
    (terminalStateMeasure rate n).map (fun s => (height s : ℝ) / Real.log n) =
      (heightLaw rate n).toMeasure.map (fun h : ℕ => (h : ℝ) / Real.log n) := by
  have hf : Measurable (fun h : ℕ => (h : ℝ) / Real.log n) := by fun_prop
  rw [← terminalStateMeasure_map_height]
  exact (Measure.map_map hf (measurable_state height)).symm

/-- The number of events already performed before absorption, obtained from
birth and recovery counts. It is unchanged during absorbing self-loops. -/
def eventCount (s : State) : ℕ := 2 * s.vertices - infectious s - 1

theorem infectious_le_vertices (s : State) : infectious s ≤ s.vertices := by
  simpa [infectious] using Finset.card_le_univ s.active

@[simp] theorem eventCount_initial (n : ℕ) : eventCount (initial n) = 0 := by
  simp [eventCount, initial, infectious]

/-- If no vertex is infectious, all infected vertices have recovered, so
there were one fewer infections than vertices and one recovery per vertex. -/
theorem eventCount_absorbed {s : State} (h : s.active = ∅) :
    eventCount s = 2 * s.vertices - 1 := by
  simp [eventCount, infectious, h]

 theorem eventCount_recover {s : State} {v : Fin s.vertices} (hv : v ∈ s.active) :
    eventCount (recover s v) = eventCount s + 1 := by
  have hcard := infectious_le_vertices s
  have hpos : 0 < infectious s := Finset.card_pos.mpr ⟨v, hv⟩
  have hvertices := s.tree.size_pos
  unfold eventCount
  rw [infectious_recover hv]
  change 2 * s.vertices - (infectious s - 1) - 1 = _
  omega

 theorem eventCount_infect (s : State) (v : Fin s.vertices) :
    eventCount (infect s v) = eventCount s + 1 := by
  have hcard := infectious_le_vertices s
  have hvertices := s.tree.size_pos
  unfold eventCount
  rw [infectious_infect]
  change 2 * (s.vertices + 1) - (infectious s + 1) - 1 = _
  omega

/-- Every genuine supported event increases the event count by exactly one. -/
theorem eventCount_step {rate : ℝ≥0} {s t : State} (h : s.active.Nonempty)
    (ht : t ∈ (step rate s).support) : eventCount t = eventCount s + 1 := by
  rcases step_support_cases ht with ⟨hs, _⟩ | ⟨v, hv, hrec | ⟨_, hinf⟩⟩
  · simp [hs] at h
  · rw [hrec, eventCount_recover hv]
  · rw [hinf, eventCount_infect]

/-- All supported transitions have nondecreasing event count. -/
theorem eventCount_step_mono {rate : ℝ≥0} {s t : State}
    (ht : t ∈ (step rate s).support) : eventCount s ≤ eventCount t := by
  rcases step_support_cases ht with ⟨_, rfl⟩ | ⟨v, hv, hrec | ⟨_, hinf⟩⟩
  · exact le_rfl
  · rw [hrec, eventCount_recover hv]
    omega
  · rw [hinf, eventCount_infect]
    omega

/-- An absorbing self-loop is the only supported step from an absorbed state. -/
theorem step_eq_of_absorbed {rate : ℝ≥0} {s t : State} (hs : s.active = ∅)
    (ht : t ∈ (step rate s).support) : t = s := by
  simpa [step_absorbed rate hs] using ht

/-- Event count never exceeds the number of steps, because extra steps after
extinction are absorbing self-loops. -/
theorem evolve_eventCount_le {rate : ℝ≥0} {n k : ℕ} {s : State}
    (hs : s ∈ (evolve rate n k).support) : eventCount s ≤ k := by
  induction k generalizing s with
  | zero =>
      have heq : s = initial n := by simpa [evolve] using hs
      simp [heq]
  | succ k ih =>
      obtain ⟨t, ht, hstep⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
      have hb := ih ht
      rcases step_support_cases hstep with ⟨_, rfl⟩ | ⟨v, hv, hrec | ⟨_, hinf⟩⟩
      · omega
      · rw [hrec, eventCount_recover hv]
        omega
      · rw [hinf, eventCount_infect]
        omega

/-- Before extinction there have been no absorbing self-loops, so event count
is exactly the number of steps. -/
theorem evolve_eventCount_eq_of_active {rate : ℝ≥0} {n k : ℕ} {s : State}
    (hs : s ∈ (evolve rate n k).support) (ha : s.active.Nonempty) : eventCount s = k := by
  induction k generalizing s with
  | zero =>
      have heq : s = initial n := by simpa [evolve] using hs
      simp [heq]
  | succ k ih =>
      obtain ⟨t, ht, hstep⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
      have htactive : t.active.Nonempty := by
        by_contra h
        have heq := step_eq_of_absorbed (Finset.not_nonempty_iff_eq_empty.mp h) hstep
        subst s
        exact h ha
      rw [eventCount_step htactive hstep, ih ht htactive]

end HeightPaper.Model
