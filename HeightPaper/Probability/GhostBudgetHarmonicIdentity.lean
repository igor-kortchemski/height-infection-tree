module

public import HeightPaper.Probability.GhostBudgetTreeMarginal
public import HeightPaper.Probability.GhostBudgetTail
public import HeightPaper.Analysis.HarmonicClock

/-!
# Exact harmonic clock of the continued susceptible budget

The fictitious initial active vertices cancel from the harmonic martingale
increment. Thus the padded epidemic's invariant is exactly the clock error of
the unabsorbed susceptible-budget chain.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

open Model
open scoped NNReal

theorem ghostBudget_harmonic_increment_eq (rate : ℝ≥0) (l : ℝ)
    (n H : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ))
    {k : ℕ} (hk : k ≤ H) :
    finalSizeInvariant rate
        (uniformTreeStateFrom l n (ghostBudgetStart n H) q k) -
      finalSizeInvariant rate (ghostBudgetStart n H) =
    (n : ℝ) - (finiteSusceptible l n q.1 k : ℝ) - k -
      ((harmonic (finiteSusceptible l n q.1 k) : ℝ) - harmonic n) / rate := by
  let s := uniformTreeStateFrom l n (ghostBudgetStart n H) q k
  have hs : s.susceptible = finiteSusceptible l n q.1 k :=
    (ghostBudgetTree_counts l n H q hk).1
  have hi : (infectious s : ℤ) = H + finiteWalk l n q.1 k :=
    ghostBudgetTree_infectious_eq_walk l n H q hk
  have hw := finiteWalk_eq_budget l n q.1 k
  rw [hw] at hi
  have hiR : (infectious s : ℝ) =
      (H : ℝ) + 1 + 2 * ((n : ℝ) - finiteSusceptible l n q.1 k) - k := by
    have hiR' : (infectious s : ℝ) =
        (H : ℝ) + (1 + 2 * ((n : ℝ) - finiteSusceptible l n q.1 k) - k) := by
      exact_mod_cast hi
    linarith only [hiR']
  unfold finalSizeInvariant
  rw [ghostBudgetStart_susceptible, ghostBudgetStart_infectious, hs]
  push_cast
  rw [hiR]
  ring

theorem ghostBudget_fluidClock_error (rate : ℝ≥0) (l : ℝ)
    (n H : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ))
    {k : ℕ} (hk : k ≤ H) (hr : 0 < rate) (hn : 0 < n) :
    fluidClock ((rate : ℝ) * n)
        ((finiteSusceptible l n q.1 k : ℝ) / n) - (k : ℝ) / n -
      (finalSizeInvariant rate
        (uniformTreeStateFrom l n (ghostBudgetStart n H) q k) -
        finalSizeInvariant rate (ghostBudgetStart n H)) / n =
      (((harmonic (finiteSusceptible l n q.1 k) : ℝ) - harmonic n) -
        Real.log ((finiteSusceptible l n q.1 k : ℝ) / n)) /
          ((rate : ℝ) * n) := by
  rw [ghostBudget_harmonic_increment_eq rate l n H q hk]
  unfold fluidClock
  have hr0 : (rate : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

theorem ghostBudget_fluidClock_uniform {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (n H : ℕ) (rate : ℝ≥0) (l : ℝ) (q : (ℕ → ℝ) × (ℕ → ℝ))
        (k : ℕ), N ≤ n → N ≤ finiteSusceptible l n q.1 k → k ≤ H →
        c ≤ (rate : ℝ) * n →
        |fluidClock ((rate : ℝ) * n)
            ((finiteSusceptible l n q.1 k : ℝ) / n) - (k : ℝ) / n -
          (finalSizeInvariant rate
            (uniformTreeStateFrom l n (ghostBudgetStart n H) q k) -
            finalSizeInvariant rate (ghostBudgetStart n H)) / n| < ε := by
  obtain ⟨N, hN, hu⟩ := harmonic_log_ratio_uniform (mul_pos hε hc)
  refine ⟨N, hN, ?_⟩
  intro n H rate l q k hn hS hk hrn
  have hnpos : 0 < n := hN.trans_le hn
  have hrn0 : 0 < (rate : ℝ) * n := hc.trans_le hrn
  have hr : 0 < rate := by
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hrpos : (0 : ℝ) < (rate : ℝ) := by nlinarith
    exact_mod_cast hrpos
  rw [ghostBudget_fluidClock_error rate l n H q hk hr hnpos,
    abs_div, abs_of_pos hrn0]
  apply (div_lt_iff₀ hrn0).mpr
  exact (hu (finiteSusceptible l n q.1 k) n hS hn).trans_le
    (mul_le_mul_of_nonneg_left hrn hε.le)

end HeightPaper.CountCoupling
