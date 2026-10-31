module

public import HeightPaper.Model.GhostBudgetStart
public import HeightPaper.Model.PrescribedPath

/-!
# Prescribed histories from an active-padded state

The auxiliary state remains active throughout the chosen event horizon for
every prescribed birth/recovery word. This is the deterministic input needed
to identify its susceptible marginal with the continued budget process.
-/

@[expose] public section

namespace HeightPaper.Model

theorem prescribedWalk_initial_le_add_time (events : ℕ → Bool) (i₀ k : ℕ) :
    i₀ ≤ prescribedWalk events i₀ k + k := by
  induction k with
  | zero => simp [prescribedWalk]
  | succ k ih =>
    rw [prescribedWalk]
    cases events k <;> simp only [prescribedActiveCount, Bool.false_eq_true,
      ↓reduceIte] <;> omega

theorem ghostBudgetStart_prescribedWalk_pos (n H : ℕ) (events : ℕ → Bool)
    {k : ℕ} (hk : k ≤ H) :
    0 < prescribedWalk events (infectious (ghostBudgetStart n H)) k := by
  have hb := prescribedWalk_initial_le_add_time events
    (infectious (ghostBudgetStart n H)) k
  rw [ghostBudgetStart_infectious] at hb
  rw [ghostBudgetStart_infectious]
  omega

theorem ghostBudgetStart_prescribedPath_active (n H : ℕ) (events : ℕ → Bool)
    {k : ℕ} (hk : k ≤ H) :
    ∀ᵐ q ∂kernelPathMeasure (fun j ↦ prescribedStep (events j))
        (ghostBudgetStart n H) k,
      0 < infectious q.last := by
  filter_upwards [ae_mem_support_kernelPathLaw
    (fun j ↦ prescribedStep (events j)) (ghostBudgetStart n H) k] with q hq
  rw [infectious_kernelPathLaw_prescribed events (ghostBudgetStart n H) k
    (fun j hj ↦ ghostBudgetStart_prescribedWalk_pos n H events (by omega)) q hq]
  exact ghostBudgetStart_prescribedWalk_pos n H events hk

end HeightPaper.Model
