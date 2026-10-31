module

public import HeightPaper.Model.GhostBudgetPrescribed
public import HeightPaper.Model.CountCoupling

/-!
# Continued budget chain as the susceptible marginal of an active path

The fictitious active padding does not change infection probabilities. For
every count word sampled from the unabsorbed budget chain, a prescribed tree
history from the padded state has precisely that budget at every time through
the chosen horizon.
-/

@[expose] public section

open MeasureTheory

namespace HeightPaper.CountCoupling

theorem finiteSusceptible_eq_prescribedSusceptibleWalk
    (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ) :
    finiteSusceptible l n u k =
      Model.prescribedSusceptibleWalk (finiteBirth l n u) n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [finiteSusceptible_succ, Model.prescribedSusceptibleWalk, ← ih]

theorem ghostBudget_prescribedPath_susceptible
    (l : ℝ) (n H : ℕ) (u : ℕ → ℝ) {k : ℕ} (hk : k ≤ H) :
    ∀ᵐ q ∂Model.kernelPathMeasure
        (fun j ↦ Model.prescribedStep (finiteBirth l n u j))
        (Model.ghostBudgetStart n H) k,
      q.last.susceptible = finiteSusceptible l n u k := by
  filter_upwards [Model.ae_mem_support_kernelPathLaw
    (fun j ↦ Model.prescribedStep (finiteBirth l n u j))
    (Model.ghostBudgetStart n H) k] with q hq
  rw [Model.susceptible_kernelPathLaw_prescribed
    (finiteBirth l n u) (Model.ghostBudgetStart n H) k
    (fun j hj ↦ Model.ghostBudgetStart_prescribedWalk_pos n H _ (by omega)) q hq,
    Model.ghostBudgetStart_susceptible]
  exact (finiteSusceptible_eq_prescribedSusceptibleWalk l n u k).symm

end HeightPaper.CountCoupling
