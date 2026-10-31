module

public import HeightPaper.Model.CountCoupling
public import HeightPaper.Analysis.FluidODE

/-!
# Reducing the unabsorbed walk fluid limit to susceptible counts

The unabsorbed count walk has a deterministic, exact relation to the pure
susceptible-budget process. Its unit increments give equicontinuity on the
event-time grid, including after its first visit to zero.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

theorem finiteWalk_lipschitz_nat (l : ℝ) (n : ℕ) (u : ℕ → ℝ)
    {i j : ℕ} (hij : i ≤ j) :
    |finiteWalk l n u j - finiteWalk l n u i| ≤ (j - i : ℤ) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    have hstep : |finiteWalk l n u (j + 1) - finiteWalk l n u j| ≤ (1 : ℤ) := by
      cases h : finiteBirth l n u j <;> simp [finiteWalk_succ, h]
    calc
      |finiteWalk l n u (j + 1) - finiteWalk l n u i| =
          |(finiteWalk l n u (j + 1) - finiteWalk l n u j) +
            (finiteWalk l n u j - finiteWalk l n u i)| := by
              congr 1
              omega
      _ ≤ |finiteWalk l n u (j + 1) - finiteWalk l n u j| +
          |finiteWalk l n u j - finiteWalk l n u i| := abs_add_le _ _
      _ ≤ 1 + (j - i : ℤ) := add_le_add hstep ih
      _ = (j + 1 - i : ℤ) := by omega

theorem finiteSusceptible_antitone_nat (l : ℝ) (n : ℕ) (u : ℕ → ℝ)
    {i j : ℕ} (hij : i ≤ j) :
    finiteSusceptible l n u j ≤ finiteSusceptible l n u i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    rw [finiteSusceptible_succ]
    split_ifs <;> omega

theorem finiteSusceptible_lipschitz_nat (l : ℝ) (n : ℕ) (u : ℕ → ℝ)
    {i j : ℕ} (hij : i ≤ j) :
    finiteSusceptible l n u i ≤ finiteSusceptible l n u j + (j - i) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [finiteSusceptible_succ]
    split_ifs <;> omega

/-- A susceptible-fraction fluid estimate transfers to the raw infectious
walk with an exact factor two and the one-individual initial error. -/
theorem finiteWalk_fluid_error_eq (l : ℝ) (n : ℕ) (u : ℕ → ℝ)
    (k : ℕ) (hn : 0 < n) :
    (finiteWalk l n u k : ℝ) / n -
        fluidInfectiousRaw l ((k : ℝ) / n) =
      1 / (n : ℝ) - 2 *
        ((finiteSusceptible l n u k : ℝ) / n -
          fluidSusceptible l ((k : ℝ) / n)) := by
  rw [finiteWalk_eq_budget]
  unfold fluidInfectiousRaw
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp
  ring

theorem finiteWalk_fluid_error_le (l : ℝ) (n : ℕ) (u : ℕ → ℝ)
    (k : ℕ) (hn : 0 < n) :
    |(finiteWalk l n u k : ℝ) / n -
        fluidInfectiousRaw l ((k : ℝ) / n)| ≤
      1 / (n : ℝ) + 2 *
        |(finiteSusceptible l n u k : ℝ) / n -
          fluidSusceptible l ((k : ℝ) / n)| := by
  rw [finiteWalk_fluid_error_eq l n u k hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    |1 / (n : ℝ) - 2 *
        ((finiteSusceptible l n u k : ℝ) / n -
          fluidSusceptible l ((k : ℝ) / n))| =
        |1 / (n : ℝ) + -(2 *
          ((finiteSusceptible l n u k : ℝ) / n -
            fluidSusceptible l ((k : ℝ) / n)))| := by
            congr 1
    _ ≤ |1 / (n : ℝ)| + |-(2 *
        ((finiteSusceptible l n u k : ℝ) / n -
          fluidSusceptible l ((k : ℝ) / n)))| := abs_add_le _ _
    _ = _ := by simp [abs_mul, abs_of_pos hnR]

theorem finiteWalk_uniform_fluid_of_uniform_susceptible
    (l : ℝ) (n H : ℕ) (u : ℕ → ℝ) (hn : 0 < n)
    {ε : ℝ}
    (hsusc : ∀ k ≤ H,
      |(finiteSusceptible l n u k : ℝ) / n -
        fluidSusceptible l ((k : ℝ) / n)| ≤ ε) :
    ∀ k ≤ H,
      |(finiteWalk l n u k : ℝ) / n -
        fluidInfectiousRaw l ((k : ℝ) / n)| ≤ 1 / (n : ℝ) + 2 * ε := by
  intro k hk
  have htwo := mul_le_mul_of_nonneg_left (hsusc k hk) (by norm_num : (0 : ℝ) ≤ 2)
  linarith only [finiteWalk_fluid_error_le l n u k hn, htwo]

end HeightPaper.CountCoupling
