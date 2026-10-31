module

public import HeightPaper.Model.BirthHarmonic
public import HeightPaper.Model.EpidemicEventConditioning
public import HeightPaper.Probability.UniformActiveCounts

/-!
# Reading the event word from an actual epidemic history

Before extinction, an increase in the infectious count identifies a birth
and a decrease identifies recovery. The prescribed count walk is therefore
exactly the observed active count. This connects deterministic normalizer
identities to the actual path measure.
-/

@[expose] public section

open scoped BigOperators NNReal

namespace HeightPaper.Model

def observedBirth (path : ℕ → State) (k : ℕ) : Bool :=
  decide (infectious (path k) < infectious (path (k + 1)))

/-- A genuine active transition is exactly the prescribed update selected by
its observed infectious-count increment. -/
theorem supported_step_observed_update {rate : ℝ≥0} {s t : State}
    (ha : s.active.Nonempty) (ht : t ∈ (step rate s).support) :
    ∃ v ∈ s.active, prescribedUpdate (decide (infectious s < infectious t)) s v = t := by
  rcases step_support_cases ht with ⟨hz, rfl⟩ | ⟨v, hv, rfl | ⟨_, rfl⟩⟩
  · exact False.elim ((Finset.not_nonempty_iff_eq_empty.mpr hz) ha)
  · refine ⟨v, hv, ?_⟩
    have hi : ¬infectious s < infectious s - 1 := by omega
    simp [infectious_recover hv, hi, prescribedUpdate]
  · refine ⟨v, hv, ?_⟩
    simp [infectious_infect, prescribedUpdate]

namespace SupportedPath

theorem observedWalk_eq {rate : ℝ≥0} {n N : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n N path) (ha : (path N).active.Nonempty)
    {k : ℕ} (hk : k ≤ N) :
    prescribedWalk (observedBirth path) 1 k = infectious (path k) := by
  induction k with
  | zero => simp [prescribedWalk, hp.1]
  | succ k ih =>
      have hka := hp.active_of_active_later (by omega : k ≤ N) le_rfl ha
      obtain ⟨v, hv, heq⟩ := supported_step_observed_update hka (hp.2 k (by omega))
      rw [prescribedWalk, ih (by omega)]
      exact (infectious_prescribedUpdate (observedBirth path k) hv).symm.trans
        (congrArg infectious heq)

theorem observedWalk_pos {rate : ℝ≥0} {n N : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n N path) (ha : (path N).active.Nonempty)
    {k : ℕ} (hk : k ≤ N) : 0 < prescribedWalk (observedBirth path) 1 k := by
  rw [hp.observedWalk_eq ha hk]
  exact (hp.active_of_active_later hk le_rfl ha).card_pos

/-- Observed reciprocal counts equal the prescribed ones term by term. -/
theorem observed_birthReciprocal {rate : ℝ≥0} {n N : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n N path) (ha : (path N).active.Nonempty)
    {k : ℕ} (hk : k < N) :
    birthReciprocal (observedBirth path) 1 k =
      if observedBirth path k then 1 / (infectious (path (k + 1)) : ℝ) else 0 := by
  unfold birthReciprocal
  by_cases hb : observedBirth path k = true
  · have hn := hp.observedWalk_eq ha (show k + 1 ≤ N by omega)
    rw [prescribedWalk, prescribedActiveCount, hb, ite_eq_left rfl,
      hp.observedWalk_eq ha (show k ≤ N by omega)] at hn
    simp only [hb, ↓reduceIte, hp.observedWalk_eq ha (show k ≤ N by omega),
      ← hn, Nat.cast_add, Nat.cast_one]
  · simp [hb]

/-- The harmonic birth-sum error bound now applies to the actual supported
history, with no independent event-word hypothesis. -/
theorem observed_birth_sum_error_bounds {rate : ℝ≥0} {n N : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n N path) (ha : (path N).active.Nonempty) :
    0 ≤ (harmonic (infectious (path N)) : ℝ) - 1 +
        (∑ k ∈ Finset.range N, 1 / (infectious (path k) : ℝ)) -
        2 * ∑ k ∈ Finset.range N, birthReciprocal (observedBirth path) 1 k ∧
    (harmonic (infectious (path N)) : ℝ) - 1 +
        (∑ k ∈ Finset.range N, 1 / (infectious (path k) : ℝ)) -
        2 * ∑ k ∈ Finset.range N, birthReciprocal (observedBirth path) 1 k ≤
      ∑ k ∈ Finset.range N, (1 / (infectious (path k) : ℝ)) ^ 2 := by
  have h := sum_birthReciprocal_error_bounds (observedBirth path) 1 N
    (fun k hk ↦ hp.observedWalk_pos ha hk.le)
  have hsum : (∑ k ∈ Finset.range N, 1 / (prescribedWalk (observedBirth path) 1 k : ℝ)) =
      ∑ k ∈ Finset.range N, 1 / (infectious (path k) : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hp.observedWalk_eq ha (Finset.mem_range.mp hk).le]
  have hsq : (∑ k ∈ Finset.range N, (1 / (prescribedWalk (observedBirth path) 1 k : ℝ)) ^ 2) =
      ∑ k ∈ Finset.range N, (1 / (infectious (path k) : ℝ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hp.observedWalk_eq ha (Finset.mem_range.mp hk).le]
  have hone : (harmonic 1 : ℝ) = 1 := by norm_num [harmonic]
  simpa only [hp.observedWalk_eq ha le_rfl, hone, hsum, hsq] using h

end SupportedPath

/-- Every supported finite path active at its horizon lies in the cylinder
of the event word read from that same path. -/
theorem supportedPath_mem_observed_eventCylinder {rate : ℝ≥0} {n N : ℕ}
    (p : FinitePath N) (hp : SupportedPath rate n N p.eval) (ha : p.last.active.Nonempty) :
    p ∈ eventCylinder (observedBirth p.eval) 1 N := by
  have haN : (p.eval N).active.Nonempty := by rw [FinitePath.eval_last]; exact ha
  intro k hk
  exact (hp.observedWalk_eq haN hk).symm

end HeightPaper.Model
