module

public import HeightPaper.Model.StateMeasure

/-!
# Extinction time along supported finite epidemic paths

The identities here concern every finite path following the support of the
SIR kernel. In particular they identify the terminal-state event count with
the first extinction step, without any asymptotic or coupling assumption.
-/

@[expose] public section
open scoped NNReal ENNReal

namespace HeightPaper.Model

/-- A finite path starts with patient zero and takes supported SIR steps. Values
past `steps` are irrelevant. -/
def SupportedPath (rate : ℝ≥0) (n steps : ℕ) (path : ℕ → State) : Prop :=
  path 0 = initial n ∧
    ∀ k < steps, path (k + 1) ∈ (step rate (path k)).support

namespace SupportedPath

variable {rate : ℝ≥0} {n steps : ℕ} {path : ℕ → State}

/-- Every state on a supported path belongs to the corresponding marginal law. -/
theorem mem_evolve (hp : SupportedPath rate n steps path) {k : ℕ} (hk : k ≤ steps) :
    path k ∈ (evolve rate n k).support := by
  induction k with
  | zero => simp [evolve, hp.1]
  | succ k ih =>
      apply (PMF.mem_support_bind_iff _ _ _).mpr
      exact ⟨path k, ih (by omega), hp.2 k (by omega)⟩

/-- Once the path reaches an absorbed state, every later state is identical. -/
theorem absorbed_stable (hp : SupportedPath rate n steps path)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps) (hi : (path i).active = ∅) :
    path j = path i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
      have heq := ih (by omega)
      have hstep := hp.2 j (by omega)
      have habs : (path j).active = ∅ := by rw [heq]; exact hi
      exact (step_eq_of_absorbed habs hstep).trans heq

/-- The actual number of events is nondecreasing along a supported path. -/
theorem eventCount_mono (hp : SupportedPath rate n steps path)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps) :
    eventCount (path i) ≤ eventCount (path j) := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      exact (ih (by omega)).trans (eventCount_step_mono (hp.2 j (by omega)))

/-- Final-state vertex count recovers the first extinction step. At a positive
cutoff, survival through that many events means the preceding state is active. -/
theorem cutoff_survival_iff (hp : SupportedPath rate n steps path)
    (hsteps : 2 * n + 1 ≤ steps) {cutoff : ℕ} (hcutoff : 0 < cutoff)
    (hcutoff_le : cutoff ≤ steps) :
    cutoff ≤ 2 * (path steps).vertices - 1 ↔
      (path (cutoff - 1)).active.Nonempty := by
  have hterminal := evolve_absorbed hsteps (hp.mem_evolve le_rfl)
  rw [← eventCount_absorbed hterminal]
  constructor
  · intro hcount
    by_contra hactive
    have habs : (path (cutoff - 1)).active = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hactive
    have heq := hp.absorbed_stable (i := cutoff - 1) (j := steps) (by omega) le_rfl habs
    have hb := evolve_eventCount_le (hp.mem_evolve (k := cutoff - 1) (by omega))
    rw [heq] at hcount
    omega
  · intro hactive
    have htime := evolve_eventCount_eq_of_active
      (hp.mem_evolve (k := cutoff - 1) (by omega)) hactive
    have hnext := eventCount_step hactive (hp.2 (cutoff - 1) (by omega))
    have hsucc : cutoff - 1 + 1 = cutoff := by omega
    rw [hsucc, htime] at hnext
    have hmono := hp.eventCount_mono (i := cutoff) hcutoff_le le_rfl
    omega

/-- At the terminal event count the path is absorbed. -/
theorem absorbed_at_eventCount (hp : SupportedPath rate n steps path)
    (hsteps : 2 * n + 1 ≤ steps) :
    (path (eventCount (path steps))).active = ∅ := by
  have hterminal := evolve_absorbed hsteps (hp.mem_evolve le_rfl)
  have ht := evolve_eventCount_le (hp.mem_evolve (k := steps) le_rfl)
  by_contra hactive
  have ha : (path (eventCount (path steps))).active.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hactive
  by_cases hlt : eventCount (path steps) < steps
  · have heq := evolve_eventCount_eq_of_active (hp.mem_evolve ht) ha
    have hnext := eventCount_step ha (hp.2 _ hlt)
    have hmono := hp.eventCount_mono (i := eventCount (path steps) + 1)
      (j := steps) (by omega) le_rfl
    omega
  · have heq : eventCount (path steps) = steps := by omega
    rw [heq, hterminal] at ha
    exact Finset.not_nonempty_empty ha

/-- Every earlier step is active: terminal `eventCount` really is the first
extinction step rather than merely some upper bound. -/
theorem active_before_eventCount (hp : SupportedPath rate n steps path)
    (hsteps : 2 * n + 1 ≤ steps) {k : ℕ} (hk : k < eventCount (path steps)) :
    (path k).active.Nonempty := by
  have ht := evolve_eventCount_le (hp.mem_evolve (k := steps) le_rfl)
  have hterminal := evolve_absorbed hsteps (hp.mem_evolve le_rfl)
  have hcut := (hp.cutoff_survival_iff hsteps (cutoff := k + 1) (by omega) (by omega)).mp
    (by rw [← eventCount_absorbed hterminal]; omega)
  simpa using hcut

/-- The paper's formula `τ = 2 * number_of_vertices - 1`, with a first-hitting
characterization rather than just an algebraic identity at the last state. -/
theorem first_extinction (hp : SupportedPath rate n steps path)
    (hsteps : 2 * n + 1 ≤ steps) :
    let τ := 2 * (path steps).vertices - 1
    0 < τ ∧ τ ≤ steps ∧ (path τ).active = ∅ ∧
      ∀ k < τ, (path k).active.Nonempty := by
  have hterminal := evolve_absorbed hsteps (hp.mem_evolve le_rfl)
  have hcount := eventCount_absorbed hterminal
  have hsize := (path steps).tree.size_pos
  dsimp only
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rw [← hcount]
    exact evolve_eventCount_le (hp.mem_evolve le_rfl)
  · rw [← hcount]
    exact hp.absorbed_at_eventCount hsteps
  · intro k hk
    apply hp.active_before_eventCount hsteps
    rwa [hcount]

end SupportedPath
/-- The path relation is not an extra model assumption: every point in the
support of an evolved state law is attained by a supported finite path. -/
theorem exists_supportedPath {rate : ℝ≥0} {n steps : ℕ} {s : State}
    (hs : s ∈ (evolve rate n steps).support) :
    ∃ path, SupportedPath rate n steps path ∧ path steps = s := by
  induction steps generalizing s with
  | zero =>
      have heq : s = initial n := by simpa [evolve] using hs
      exact ⟨fun _ => initial n, ⟨rfl, by intro k hk; omega⟩, heq.symm⟩
  | succ k ih =>
      obtain ⟨t, ht, hstep⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
      obtain ⟨path, hp, hend⟩ := ih ht
      let next : ℕ → State := fun j => if j ≤ k then path j else s
      refine ⟨next, ⟨?_, ?_⟩, ?_⟩
      · simpa [next] using hp.1
      · intro j hj
        by_cases hjk : j < k
        · simpa only [next, ite_eq_left (show j + 1 ≤ k by omega), ite_eq_left (show j ≤ k by omega)]
            using hp.2 j hjk
        · have heq : j = k := by omega
          subst j
          simpa [next, hend] using hstep
      · simp [next]

end HeightPaper.Model
