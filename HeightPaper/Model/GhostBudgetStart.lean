module

public import HeightPaper.Model.InfectionTree

/-!
# Active padding for the continued susceptible-budget chain

An auxiliary state may start with enough active vertices to remain active for
any prescribed finite event horizon, even if every event is a recovery. Its
susceptible count can still start at the paper's population size. This permits
use of the existing epidemic kernel's count martingale without stopping at the
first extinction of the source epidemic.
-/

@[expose] public section

namespace HeightPaper.Model

def attachAtRoot (s : State) : State :=
  infect s ⟨0, s.tree.size_pos⟩

def activePadding : ℕ → State → State
  | 0, s => s
  | k + 1, s => activePadding k (attachAtRoot s)

theorem activePadding_susceptible (m : ℕ) (s : State) :
    (activePadding m s).susceptible = s.susceptible - m := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
    rw [activePadding, ih]
    simp only [attachAtRoot, infect]
    omega

theorem activePadding_infectious (m : ℕ) (s : State) :
    infectious (activePadding m s) = infectious s + m := by
  induction m generalizing s with
  | zero => simp [activePadding]
  | succ m ih =>
    rw [activePadding, ih]
    simp only [attachAtRoot, infectious_infect]
    omega

/-- The extra `H` infections are fictitious initialization events, so the
auxiliary state starts with `n` susceptibles and `H+1` active vertices. -/
def ghostBudgetStart (n H : ℕ) : State := activePadding H (initial (n + H))

@[simp] theorem ghostBudgetStart_susceptible (n H : ℕ) :
    (ghostBudgetStart n H).susceptible = n := by
  rw [ghostBudgetStart, activePadding_susceptible]
  change n + H - H = n
  omega

@[simp] theorem ghostBudgetStart_infectious (n H : ℕ) :
    infectious (ghostBudgetStart n H) = H + 1 := by
  rw [ghostBudgetStart, activePadding_infectious, infectious_initial]
  omega

end HeightPaper.Model
