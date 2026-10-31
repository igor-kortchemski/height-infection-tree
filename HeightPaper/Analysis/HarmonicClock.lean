module

public import HeightPaper.Analysis.FluidODE
public import HeightPaper.Model.CountProcess
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# From the exact finite-population invariant to the fluid clock

The harmonic-number correction is uniformly logarithmic when susceptible and
population counts diverge. Combined with the exact count balance, this relates
the stochastic invariant to the deterministic inverse clock without assuming
convergence of the epidemic.
-/

@[expose] public section

open Filter Set
open scoped Topology NNReal

namespace HeightPaper

/-- Uniform harmonic/logarithm cancellation for any pair of sufficiently large
counts. This is stronger than convergence along one prescribed count sequence. -/
theorem harmonic_log_ratio_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ H n : ℕ, N ≤ H → N ≤ n →
      |((harmonic H : ℝ) - harmonic n) - Real.log ((H : ℝ) / n)| < ε := by
  have he := Real.tendsto_harmonic_sub_log.eventually
    (Metric.ball_mem_nhds Real.eulerMascheroniConstant (half_pos hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨max 1 N, by omega, ?_⟩
  intro H n hH hn
  have hH' := hN H ((le_max_right 1 N).trans hH)
  have hn' := hN n ((le_max_right 1 N).trans hn)
  simp only [Real.dist_eq] at hH' hn'
  have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast (show H ≠ 0 by omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hid : ((harmonic H : ℝ) - harmonic n) - Real.log ((H : ℝ) / n) =
      ((harmonic H : ℝ) - Real.log H - Real.eulerMascheroniConstant) -
      ((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) := by
    rw [Real.log_div hH0 hn0]
    ring
  rw [hid]
  exact (abs_sub _ _).trans_lt (by linarith)

namespace Model

/-- Susceptible count, active count, and genuine event count satisfy an exact
linear identity throughout any population-preserving history, including after
absorption. -/
theorem count_balance {n : ℕ} {s : State} (hpop : s.vertices + s.susceptible = n + 1) :
    infectious s + 2 * s.susceptible + eventCount s = 2 * n + 1 := by
  have hi := infectious_le_vertices s
  have hv := s.tree.size_pos
  unfold eventCount
  omega

theorem finalSizeInvariant_sub_initial {rate : ℝ≥0} {n : ℕ} {s : State}
    (hpop : s.vertices + s.susceptible = n + 1) :
    finalSizeInvariant rate s - finalSizeInvariant rate (initial n) =
      (n : ℝ) - s.susceptible - eventCount s -
        ((harmonic s.susceptible : ℝ) - harmonic n) / rate := by
  have hc : (infectious s : ℝ) + 2 * s.susceptible + eventCount s = 2 * n + 1 := by
    exact_mod_cast count_balance hpop
  unfold finalSizeInvariant
  rw [infectious_initial]
  simp only [initial, Nat.cast_one]
  rw [sub_div]
  linarith

/-- Exact comparison between the finite SIR invariant and the deterministic
fluid clock; the only remaining error is the harmonic/logarithmic discrepancy. -/
theorem finalSizeInvariant_clock_error {rate : ℝ≥0} {n : ℕ} {s : State}
    (hr : 0 < rate) (hn : 0 < n) (hpop : s.vertices + s.susceptible = n + 1) :
    fluidClock ((rate : ℝ) * n) ((s.susceptible : ℝ) / n) - (eventCount s : ℝ) / n -
      (finalSizeInvariant rate s - finalSizeInvariant rate (initial n)) / n =
        (((harmonic s.susceptible : ℝ) - harmonic n) - Real.log ((s.susceptible : ℝ) / n)) /
          ((rate : ℝ) * n) := by
  rw [finalSizeInvariant_sub_initial hpop]
  unfold fluidClock
  have hr0 : (rate : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

/-- Uniform approximation of the inverse fluid clock on large susceptible
counts, with an explicit positive lower bound on the scaled rate. -/
theorem finalSizeInvariant_clock_uniform {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∃ N : ℕ, 0 < N ∧ ∀ (n : ℕ) (rate : ℝ≥0) (s : State), N ≤ n → N ≤ s.susceptible →
      s.vertices + s.susceptible = n + 1 → c ≤ (rate : ℝ) * n →
      |fluidClock ((rate : ℝ) * n) ((s.susceptible : ℝ) / n) - (eventCount s : ℝ) / n -
        (finalSizeInvariant rate s - finalSizeInvariant rate (initial n)) / n| < ε := by
  obtain ⟨N, hN, hu⟩ := harmonic_log_ratio_uniform (mul_pos hε hc)
  refine ⟨N, hN, ?_⟩
  intro n rate s hn hH hpop hrn
  have hnpos : 0 < n := hN.trans_le hn
  have hrn0 : 0 < (rate : ℝ) * n := hc.trans_le hrn
  have hr : 0 < rate := by
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hrpos : (0 : ℝ) < (rate : ℝ) := by nlinarith
    exact_mod_cast hrpos
  rw [finalSizeInvariant_clock_error hr hnpos hpop, abs_div, abs_of_pos hrn0]
  apply (div_lt_iff₀ hrn0).mpr
  exact (hu s.susceptible n hH hn).trans_le (mul_le_mul_of_nonneg_left hrn hε.le)

end Model
end HeightPaper
