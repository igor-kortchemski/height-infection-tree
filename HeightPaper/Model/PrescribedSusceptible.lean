module

public import HeightPaper.Model.UniformParent
public import HeightPaper.Model.CanonicalAnalyticProfile

/-! # Prescribed profiles do not depend on the unused susceptible counter -/

@[expose] public section

namespace HeightPaper.Model

def clearSusceptible (s : State) : State := { s with susceptible := 0 }

@[simp] theorem infectious_clearSusceptible (s : State) :
    infectious (clearSusceptible s) = infectious s := rfl

@[simp] theorem normalizedActiveWeight_clearSusceptible (w : ℂ) (s : State) :
    normalizedActiveWeight w (clearSusceptible s) = normalizedActiveWeight w s := rfl

theorem clearSusceptible_prescribedUpdate (birth : Bool) (s : State) (v : Fin s.vertices) :
    clearSusceptible (prescribedUpdate birth s v) =
      prescribedUpdate birth (clearSusceptible s) v := by
  cases birth <;> rfl

theorem clearSusceptible_rankUpdate (birth : Bool) (s : State) (u : ℝ) :
    clearSusceptible (rankUpdate birth s u) = rankUpdate birth (clearSusceptible s) u := by
  by_cases hs : s.active.Nonempty
  · rw [rankUpdate_of_nonempty birth s hs u,
      rankUpdate_of_nonempty birth (clearSusceptible s) hs u]
    exact clearSusceptible_prescribedUpdate birth s _
  · have hs' : ¬(clearSusceptible s).active.Nonempty := hs
    rw [rankUpdate, dite_eq_right hs, rankUpdate, dite_eq_right hs']

theorem clearSusceptible_rankState (events : ℕ → Bool) (s₀ : State)
    (u : ℕ → ℝ) (k : ℕ) :
    clearSusceptible (rankState events s₀ u k) =
      rankState events (clearSusceptible s₀) u k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rankState, clearSusceptible_rankUpdate, ih]; rfl

theorem rankState_initial_normalizedProfile (w : ℂ) (events : ℕ → Bool)
    (n J : ℕ) (u : ℕ → ℝ) (k : ℕ) :
    prescribedNormalizedProfile w events (initial n) J k (rankState events (initial n) u k) =
      prescribedNormalizedProfile w events (initial 0) J k (rankState events (initial 0) u k) := by
  have hh := congrArg (normalizedActiveWeight w) (clearSusceptible_rankState events (initial n) u k)
  change normalizedActiveWeight w (rankState events (initial n) u k) =
    normalizedActiveWeight w (rankState events (initial 0) u k) at hh
  simp only [prescribedNormalizedProfile, infectious_initial, hh]

/-- The explicit analytic limit on the parent space is the same for every
initial susceptible counter; thus the local limiting law does not vary with n. -/
theorem rankState_initial_analyticProfileLimit (events : ℕ → Bool) (n J : ℕ)
    (u : ℕ → ℝ) (z : ℂ) :
    prescribedAnalyticProfileLimit events (initial n) J (rankState events (initial n) u) z =
      prescribedAnalyticProfileLimit events (initial 0) J (rankState events (initial 0) u) z := by
  simp only [prescribedAnalyticProfileLimit, prescribedAnalyticSequenceLimit,
    analyticSequenceLimit, rankState_initial_normalizedProfile]

end HeightPaper.Model
