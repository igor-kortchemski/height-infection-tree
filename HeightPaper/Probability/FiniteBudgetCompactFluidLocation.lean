module

public import HeightPaper.Probability.FiniteBudgetCompactClock
public import HeightPaper.Probability.FiniteBudgetFunctionalFluid

/-!
# Weakly uniform fluid location over a rate interval

The same threshold works for every rate in a bounded supercritical interval.
Below it, the upper endpoint dominates under the common-uniform coupling;
above it, the lower endpoint controls the stopped martingale variance.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace HeightPaper.CountCoupling

theorem finiteSusceptible_budgetClockError_uniform
    (a₀ L : ℝ≥0) (horizon : ℕ → ℕ)
    {T c : ℝ} (ha₀ : 1 < (a₀ : ℝ)) (haL : a₀ ≤ L)
    (hc : 0 < c) (hc1 : c < 1)
    (hbar : T < fluidBarrier (L : ℝ) c)
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℝ≥0, a₀ ≤ a → a ≤ L →
      uniformLaw.real {u | ε ≤ |budgetClockError (a / n) n
        (finiteSusceptible (a : ℝ) n u (horizon n)) (horizon n) / n|} < η := by
  have hL : 1 < (L : ℝ) := ha₀.trans_le (by exact_mod_cast haL)
  have hlow := finiteSusceptible_below_fluidThreshold_tendsto_zero L horizon
    hL hc hc1 hbar hhorizon
  have ha₀pos : 0 < a₀ := by exact_mod_cast (zero_lt_one.trans ha₀)
  have hbound := budgetClock_above_uniform_bound_tendsto_zero a₀ horizon
    ha₀pos hc hε hhorizon
  have hsum := hlow.add hbound
  simp only [add_zero] at hsum
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hsum.eventually (Iio_mem_nhds hη))
  refine ⟨max N 1, ?_⟩
  intro n hn a haa₀ haL'
  have hn0 : 0 < n := by omega
  have hN' : N ≤ n := (le_max_left N 1).trans hn
  have hS (u : ℕ → ℝ) :
      finiteSusceptible (L : ℝ) n u (horizon n) ≤
        finiteSusceptible (a : ℝ) n u (horizon n) := by
    exact finiteSusceptible_antitone (by positivity : 0 ≤ (a : ℝ))
      (by exact_mod_cast haL') n u (horizon n)
  have hlowcomp : uniformLaw.real
      {u | finiteSusceptible (a : ℝ) n u (horizon n) < fluidThreshold c n} ≤
      uniformLaw.real
        {u | finiteSusceptible (L : ℝ) n u (horizon n) < fluidThreshold c n} := by
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro u hu
    exact lt_of_le_of_lt (hS u) hu
  have habove := finiteSusceptible_budgetClockError_above_uniform_le a₀ a n
    (horizon n) (fluidThreshold c n) ha₀pos haa₀ hn0
    (fluidThreshold_pos c n) hε
  calc
    uniformLaw.real {u | ε ≤ |budgetClockError (a / n) n
        (finiteSusceptible (a : ℝ) n u (horizon n)) (horizon n) / n|}
      ≤ uniformLaw.real
          {u | finiteSusceptible (a : ℝ) n u (horizon n) < fluidThreshold c n} +
        uniformLaw.real
          {u | fluidThreshold c n ≤ finiteSusceptible (a : ℝ) n u (horizon n) ∧
            ε ≤ |budgetClockError (a / n) n
              (finiteSusceptible (a : ℝ) n u (horizon n)) (horizon n) / n|} := by
          apply le_trans _ (measureReal_union_le _ _)
          apply measureReal_mono (h₂ := measure_ne_top _ _)
          intro u hu
          by_cases hb : finiteSusceptible (a : ℝ) n u (horizon n) < fluidThreshold c n
          · exact Or.inl hb
          · exact Or.inr ⟨Nat.le_of_not_gt hb, hu⟩
    _ ≤ uniformLaw.real
          {u | finiteSusceptible (L : ℝ) n u (horizon n) < fluidThreshold c n} +
        (horizon n : ℝ) /
          (((a₀ / n : ℝ≥0) : ℝ) * fluidThreshold c n * (ε * n) ^ 2) :=
          add_le_add hlowcomp habove
    _ < η := hN n hN'

theorem finiteSusceptible_fluidClock_uniform
    (a₀ L : ℝ≥0) (horizon : ℕ → ℕ)
    {T c : ℝ} (ha₀ : 1 < (a₀ : ℝ)) (haL : a₀ ≤ L)
    (hc : 0 < c) (hc1 : c < 1)
    (hbar : T < fluidBarrier (L : ℝ) c)
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℝ≥0, a₀ ≤ a → a ≤ L →
      uniformLaw.real {u | δ ≤ |fluidClock (a : ℝ)
        ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
        (horizon n : ℝ) / n|} < η := by
  have hL : 1 < (L : ℝ) := ha₀.trans_le (by exact_mod_cast haL)
  obtain ⟨Nerr, herr⟩ := finiteSusceptible_budgetClockError_uniform a₀ L horizon
    ha₀ haL hc hc1 hbar hhorizon (half_pos hδ) (half_pos hη)
  have hlow := finiteSusceptible_below_fluidThreshold_tendsto_zero L horizon
    hL hc hc1 hbar hhorizon
  obtain ⟨Nlow, hNlow⟩ := eventually_atTop.mp
    (hlow.eventually (Iio_mem_nhds (half_pos hη)))
  obtain ⟨Nclock, hNclock, hclock⟩ := budgetClock_fluidClock_uniform
    (half_pos hδ) (zero_lt_one.trans ha₀)
  obtain ⟨Nfloor, hNfloor⟩ := eventually_atTop.mp
    ((tendsto_nat_floor_mul_atTop c hc).eventually (eventually_ge_atTop Nclock))
  refine ⟨max (max Nerr Nlow) (max Nclock (max Nfloor 1)), ?_⟩
  intro n hn a haa₀ haL'
  have hn0 : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hS (u : ℕ → ℝ) :
      finiteSusceptible (L : ℝ) n u (horizon n) ≤
        finiteSusceptible (a : ℝ) n u (horizon n) := by
    exact finiteSusceptible_antitone (by positivity : 0 ≤ (a : ℝ))
      (by exact_mod_cast haL') n u (horizon n)
  have hlowcomp : uniformLaw.real
      {u | finiteSusceptible (a : ℝ) n u (horizon n) < fluidThreshold c n} ≤
      uniformLaw.real
        {u | finiteSusceptible (L : ℝ) n u (horizon n) < fluidThreshold c n} := by
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro u hu
    exact lt_of_le_of_lt (hS u) hu
  have hsmall (u : ℕ → ℝ)
      (hu : fluidThreshold c n ≤ finiteSusceptible (a : ℝ) n u (horizon n)) :
      |fluidClock (a : ℝ)
        ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
        (horizon n : ℝ) / n -
        budgetClockError (a / n) n
          (finiteSusceptible (a : ℝ) n u (horizon n)) (horizon n) / n| < δ / 2 := by
    have hSN : Nclock ≤ finiteSusceptible (a : ℝ) n u (horizon n) := by
      dsimp [fluidThreshold] at hu
      have hh := hNfloor n (by omega : Nfloor ≤ n)
      omega
    have hrate : ((a / n : ℝ≥0) : ℝ) * n = (a : ℝ) := by
      simp only [NNReal.coe_div, NNReal.coe_natCast, div_mul_cancel₀ _ hnR]
    have hh := hclock n (finiteSusceptible (a : ℝ) n u (horizon n))
      (horizon n) (a / n) (by omega : Nclock ≤ n) hSN (by
        rw [hrate]
        exact_mod_cast haa₀)
    rwa [hrate] at hh
  have hlow' := (hlowcomp.trans_lt (hNlow n (by omega : Nlow ≤ n)))
  have herr' := herr n (by omega : Nerr ≤ n) a haa₀ haL'
  calc
    uniformLaw.real {u | δ ≤ |fluidClock (a : ℝ)
        ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
        (horizon n : ℝ) / n|}
      ≤ uniformLaw.real
          {u | finiteSusceptible (a : ℝ) n u (horizon n) < fluidThreshold c n} +
        uniformLaw.real {u | δ / 2 ≤ |budgetClockError (a / n) n
          (finiteSusceptible (a : ℝ) n u (horizon n)) (horizon n) / n|} := by
          apply le_trans _ (measureReal_union_le _ _)
          apply measureReal_mono (h₂ := measure_ne_top _ _)
          intro u hu
          by_cases hb : finiteSusceptible (a : ℝ) n u (horizon n) < fluidThreshold c n
          · exact Or.inl hb
          · apply Or.inr
            have hs := hsmall u (Nat.le_of_not_gt hb)
            have hu' : δ ≤ |fluidClock (a : ℝ)
                ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
                (horizon n : ℝ) / n| := hu
            have htri := abs_add_le
              (fluidClock (a : ℝ)
                ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
                (horizon n : ℝ) / n -
                budgetClockError (a / n) n
                  (finiteSusceptible (a : ℝ) n u (horizon n)) (horizon n) / n)
              (budgetClockError (a / n) n
                (finiteSusceptible (a : ℝ) n u (horizon n)) (horizon n) / n)
            have heq : fluidClock (a : ℝ)
                ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
                (horizon n : ℝ) / n -
                budgetClockError (a / n) n
                  (finiteSusceptible (a : ℝ) n u (horizon n)) (horizon n) / n +
                budgetClockError (a / n) n
                  (finiteSusceptible (a : ℝ) n u (horizon n)) (horizon n) / n =
                fluidClock (a : ℝ)
                  ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
                  (horizon n : ℝ) / n := by ring
            rw [heq] at htri
            change δ / 2 ≤ |budgetClockError (a / n) n
              (finiteSusceptible (a : ℝ) n u (horizon n)) (horizon n) / n|
            linarith only [hs, hu', htri]
    _ < η := by linarith only [hlow', herr']

theorem finiteSusceptible_pointwise_fluid_uniform
    (a₀ L : ℝ≥0) (horizon : ℕ → ℕ)
    {T c : ℝ} (ha₀ : 1 < (a₀ : ℝ)) (haL : a₀ ≤ L)
    (hc : 0 < c) (hc1 : c < 1)
    (hbar : T < fluidBarrier (L : ℝ) c)
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℝ≥0, a₀ ≤ a → a ≤ L →
      uniformLaw.real {u | δ ≤ |(finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n -
          fluidSusceptible (a : ℝ) T|} < η := by
  have hL : 1 < (L : ℝ) := ha₀.trans_le (by exact_mod_cast haL)
  obtain ⟨Nclock, hclock⟩ := finiteSusceptible_fluidClock_uniform a₀ L horizon
    ha₀ haL hc hc1 hbar hhorizon (half_pos hδ) (half_pos hη)
  have hlow := finiteSusceptible_below_fluidThreshold_tendsto_zero L horizon
    hL hc hc1 hbar hhorizon
  obtain ⟨Nlow, hNlow⟩ := eventually_atTop.mp
    (hlow.eventually (Iio_mem_nhds (half_pos hη)))
  obtain ⟨Ntime, hNtime⟩ := eventually_atTop.mp
    (hhorizon.eventually (Metric.ball_mem_nhds T (half_pos hδ)))
  refine ⟨max (max Nclock Nlow) (max Ntime 1), ?_⟩
  intro n hn a haa₀ haL'
  have hn0 : 0 < n := by omega
  have htime := hNtime n (by omega : Ntime ≤ n)
  simp only [Real.dist_eq] at htime
  have hS (u : ℕ → ℝ) :
      finiteSusceptible (L : ℝ) n u (horizon n) ≤
        finiteSusceptible (a : ℝ) n u (horizon n) := by
    exact finiteSusceptible_antitone (by positivity : 0 ≤ (a : ℝ))
      (by exact_mod_cast haL') n u (horizon n)
  have hlowcomp : uniformLaw.real
      {u | finiteSusceptible (a : ℝ) n u (horizon n) < fluidThreshold c n} ≤
      uniformLaw.real
        {u | finiteSusceptible (L : ℝ) n u (horizon n) < fluidThreshold c n} := by
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro u hu
    exact lt_of_le_of_lt (hS u) hu
  have hlow' := hlowcomp.trans_lt (hNlow n (by omega : Nlow ≤ n))
  have hclock' := hclock n (by omega : Nclock ≤ n) a haa₀ haL'
  calc
    uniformLaw.real {u | δ ≤ |(finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n -
          fluidSusceptible (a : ℝ) T|}
      ≤ uniformLaw.real
          {u | finiteSusceptible (a : ℝ) n u (horizon n) < fluidThreshold c n} +
        uniformLaw.real {u | δ / 2 ≤ |fluidClock (a : ℝ)
          ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
          (horizon n : ℝ) / n|} := by
          apply le_trans _ (measureReal_union_le _ _)
          apply measureReal_mono (h₂ := measure_ne_top _ _)
          intro u hu
          by_cases hb : finiteSusceptible (a : ℝ) n u (horizon n) < fluidThreshold c n
          · exact Or.inl hb
          · apply Or.inr
            have hSpos : 0 < finiteSusceptible (a : ℝ) n u (horizon n) :=
              (fluidThreshold_pos c n).trans_le (Nat.le_of_not_gt hb)
            have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
            have hx : (0 : ℝ) <
                (finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n := by
              positivity
            have ha : 1 < (a : ℝ) := ha₀.trans_le (by exact_mod_cast haa₀)
            have hinv := abs_sub_fluidSusceptible_le (t := T) ha hx
            have htri := abs_add_le
              (fluidClock (a : ℝ)
                ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
                (horizon n : ℝ) / n)
              ((horizon n : ℝ) / n - T)
            rw [sub_add_sub_cancel] at htri
            have hu' : δ ≤ |(finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n -
                  fluidSusceptible (a : ℝ) T| := hu
            change δ / 2 ≤ |fluidClock (a : ℝ)
              ((finiteSusceptible (a : ℝ) n u (horizon n) : ℝ) / n) -
                (horizon n : ℝ) / n|
            linarith only [hinv, htri, hu', htime]
    _ < η := by linarith only [hlow', hclock']

end HeightPaper.CountCoupling
