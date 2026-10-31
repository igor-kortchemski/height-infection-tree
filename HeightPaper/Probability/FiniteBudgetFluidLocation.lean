module

public import HeightPaper.Probability.GhostBudgetClockLimit
public import HeightPaper.Probability.FiniteWalkFluidReduction
public import HeightPaper.Probability.FluidLocation

/-!
# Fluid location of the unabsorbed susceptible budget

The exact harmonic clock, its concentration, and a positive susceptible
barrier locate the budget chain on the inverse fluid clock at linear times.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace HeightPaper.CountCoupling

theorem budgetClock_fluidClock_error (rate : ℝ≥0) (n m k : ℕ)
    (hr : 0 < rate) (hn : 0 < n) :
    fluidClock ((rate : ℝ) * n) ((m : ℝ) / n) - (k : ℝ) / n -
      budgetClockError rate n m k / n =
      (((harmonic m : ℝ) - harmonic n) - Real.log ((m : ℝ) / n)) /
        ((rate : ℝ) * n) := by
  unfold budgetClockError fluidClock
  have hr0 : (rate : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

theorem budgetClock_fluidClock_uniform {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∃ N : ℕ, 0 < N ∧ ∀ (n m k : ℕ) (rate : ℝ≥0),
      N ≤ n → N ≤ m → c ≤ (rate : ℝ) * n →
      |fluidClock ((rate : ℝ) * n) ((m : ℝ) / n) - (k : ℝ) / n -
        budgetClockError rate n m k / n| < ε := by
  obtain ⟨N, hN, hu⟩ := harmonic_log_ratio_uniform (mul_pos hε hc)
  refine ⟨N, hN, ?_⟩
  intro n m k rate hn hm hrn
  have hnpos : 0 < n := hN.trans_le hn
  have hrn0 : 0 < (rate : ℝ) * n := hc.trans_le hrn
  have hr : 0 < rate := by
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hrpos : (0 : ℝ) < (rate : ℝ) := by nlinarith
    exact_mod_cast hrpos
  rw [budgetClock_fluidClock_error rate n m k hr hnpos, abs_div,
    abs_of_pos hrn0]
  apply (div_lt_iff₀ hrn0).mpr
  exact (hu m n hm hn).trans_le (mul_le_mul_of_nonneg_left hrn hε.le)

theorem eventually_finiteSusceptible_fluidClock_bound
    (a : ℝ≥0) {c : ℝ} (ha : 1 < (a : ℝ)) (hc : 0 < c)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (u : ℕ → ℝ) (k : ℕ),
      fluidThreshold c n ≤ finiteSusceptible (a : ℝ) n u k →
      |fluidClock (a : ℝ) ((finiteSusceptible (a : ℝ) n u k : ℝ) / n) -
        (k : ℝ) / n| <
        |budgetClockError (a / n) n
          (finiteSusceptible (a : ℝ) n u k) k / n| + ε := by
  obtain ⟨N, hN, hclock⟩ := budgetClock_fluidClock_uniform hε
    (zero_lt_one.trans ha)
  filter_upwards [eventually_ge_atTop N,
    (tendsto_nat_floor_mul_atTop c hc).eventually (eventually_ge_atTop N)]
    with n hn hfloor
  intro u k hS
  have hn0 : 0 < n := hN.trans_le hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hSN : N ≤ finiteSusceptible (a : ℝ) n u k := by
    dsimp [fluidThreshold] at hS
    omega
  have hrn : ((a / n : ℝ≥0) : ℝ) * n = (a : ℝ) := by
    simp only [NNReal.coe_div, NNReal.coe_natCast, div_mul_cancel₀ _ hnR]
  have hh := hclock n (finiteSusceptible (a : ℝ) n u k) k
    (a / n) hn hSN (by rw [hrn])
  rw [hrn] at hh
  have ht := abs_add_le
    (fluidClock (a : ℝ) ((finiteSusceptible (a : ℝ) n u k : ℝ) / n) -
      (k : ℝ) / n -
      budgetClockError (a / n) n (finiteSusceptible (a : ℝ) n u k) k / n)
    (budgetClockError (a / n) n (finiteSusceptible (a : ℝ) n u k) k / n)
  have heq : fluidClock (a : ℝ)
      ((finiteSusceptible (a : ℝ) n u k : ℝ) / n) - (k : ℝ) / n -
      budgetClockError (a / n) n (finiteSusceptible (a : ℝ) n u k) k / n +
      budgetClockError (a / n) n (finiteSusceptible (a : ℝ) n u k) k / n =
      fluidClock (a : ℝ)
        ((finiteSusceptible (a : ℝ) n u k : ℝ) / n) - (k : ℝ) / n := by ring
  rw [heq] at ht
  linarith

theorem finiteSusceptible_fluidClock_concentration
    (a : ℝ≥0) (horizon : ℕ → ℕ)
    {T c : ℝ} (ha : 1 < (a : ℝ)) (hc : 0 < c) (hc1 : c < 1)
    (hbar : T < fluidBarrier (a : ℝ) c)
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ uniformLaw.real
      {u | ε ≤ |fluidClock (a : ℝ)
        ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
          (horizon n : ℝ) / n|}) atTop (𝓝 0) := by
  have hlow := finiteSusceptible_below_fluidThreshold_tendsto_zero a horizon
    ha hc hc1 hbar hhorizon
  have herr := finiteSusceptible_budgetClockError_tendsto_zero a horizon
    ha hc hc1 hbar hhorizon (half_pos hε)
  have hsum := hlow.add herr
  simp only [add_zero] at hsum
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [eventually_finiteSusceptible_fluidClock_bound a ha hc
    (half_pos hε)] with n hn
  apply le_trans _ (measureReal_union_le _ _)
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro u hu
  by_cases hbelow : finiteSusceptible (a : ℝ) n u (horizon n) < fluidThreshold c n
  · exact Or.inl hbelow
  · apply Or.inr
    have hb := hn u (horizon n) (Nat.le_of_not_gt hbelow)
    have hu' : ε ≤ |fluidClock (a : ℝ)
        ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
        (horizon n : ℝ) / n| := hu
    change ε / 2 ≤ |budgetClockError (a / n) n
      (finiteSusceptible (a : ℝ) n u (horizon n)) (horizon n) / n|
    linarith only [hb, hu']

theorem finiteSusceptible_pointwise_fluid_concentration
    (a : ℝ≥0) (horizon : ℕ → ℕ)
    {T c : ℝ} (ha : 1 < (a : ℝ)) (hc : 0 < c) (hc1 : c < 1)
    (hbar : T < fluidBarrier (a : ℝ) c)
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ uniformLaw.real
      {u | ε ≤ |(finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n -
        fluidSusceptible (a : ℝ) T|}) atTop (𝓝 0) := by
  have hlow := finiteSusceptible_below_fluidThreshold_tendsto_zero a horizon
    ha hc hc1 hbar hhorizon
  have hclock := finiteSusceptible_fluidClock_concentration a horizon
    ha hc hc1 hbar hhorizon (half_pos hε)
  have hsum := hlow.add hclock
  simp only [add_zero] at hsum
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [hhorizon.eventually (Metric.ball_mem_nhds T (half_pos hε)),
    eventually_gt_atTop 0] with n hn hn0
  simp only [Real.dist_eq] at hn
  apply le_trans _ (measureReal_union_le _ _)
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro u hu
  by_cases hbelow : finiteSusceptible (a : ℝ) n u (horizon n) < fluidThreshold c n
  · exact Or.inl hbelow
  · apply Or.inr
    have hS : 0 < finiteSusceptible (a : ℝ) n u (horizon n) :=
      (fluidThreshold_pos c n).trans_le (Nat.le_of_not_gt hbelow)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hx : (0 : ℝ) <
        (finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n := by
      positivity
    have hinv := abs_sub_fluidSusceptible_le
      (t := T) ha hx
    have htri := abs_add_le
      (fluidClock (a : ℝ)
        ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
        (horizon n : ℝ) / n)
      ((horizon n : ℝ) / n - T)
    rw [sub_add_sub_cancel] at htri
    have hu' : ε ≤ |(finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n -
      fluidSusceptible (a : ℝ) T| := hu
    change ε / 2 ≤ |fluidClock (a : ℝ)
      ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
        (horizon n : ℝ) / n|
    linarith only [hinv, htri, hu', hn]

end HeightPaper.CountCoupling
