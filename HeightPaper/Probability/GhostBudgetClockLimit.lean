module

public import HeightPaper.Probability.GhostBudgetClockConcentration
public import HeightPaper.Probability.GhostBudgetTail

/-!
# Vanishing harmonic clock error of the continued susceptible budget

The positive susceptible barrier removes the stopping condition from the
stopped invariant concentration estimate.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace HeightPaper.CountCoupling

open Model

theorem finiteSusceptible_budgetClockError_above_tendsto_zero
    (a : ℝ≥0) (horizon : ℕ → ℕ)
    {T c : ℝ} (ha : 1 < (a : ℝ)) (hc : 0 < c)
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ uniformLaw.real
      {u | fluidThreshold c n ≤ finiteSusceptible (a : ℝ) n u (horizon n) ∧
        ε ≤ |budgetClockError (a / n) n
          (finiteSusceptible (a : ℝ) n u (horizon n)) (horizon n) / n|})
      atTop (𝓝 0) := by
  let rates : ℕ → ℝ≥0 := fun n ↦ a / n
  let threshold : ℕ → ℕ := fun n ↦ fluidThreshold c n
  let start : ℕ → State := fun n ↦ ghostBudgetStart n (horizon n)
  have hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 (a : ℝ)) := by
    apply (tendsto_const_nhds (x := (a : ℝ))).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [rates, NNReal.coe_div, NNReal.coe_natCast, div_mul_cancel₀ _ hnR]
  have hpressure : Tendsto (fun n ↦ (rates n : ℝ) * threshold n)
      atTop (𝓝 ((a : ℝ) * c)) :=
    tendsto_fluidThreshold_pressure rates hc.le hrates
  have htail := stoppedCountLaw_normalized_concentration rates threshold horizon start
    (mul_pos (zero_lt_one.trans ha) hc) hpressure hhorizon hε
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ htail
  filter_upwards with n
  rw [finiteSusceptible_budgetClockError_above_eq_stopped a n (horizon n)
    (threshold n) (fluidThreshold_pos c n)]
  exact measureReal_mono (h₂ := measure_ne_top _ _) (by
    intro s hs
    exact hs.2)

theorem finiteSusceptible_budgetClockError_tendsto_zero
    (a : ℝ≥0) (horizon : ℕ → ℕ)
    {T c : ℝ} (ha : 1 < (a : ℝ)) (hc : 0 < c) (hc1 : c < 1)
    (hbar : T < fluidBarrier (a : ℝ) c)
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ uniformLaw.real
      {u | ε ≤ |budgetClockError (a / n) n
        (finiteSusceptible (a : ℝ) n u (horizon n)) (horizon n) / n|})
      atTop (𝓝 0) := by
  have hlow := finiteSusceptible_below_fluidThreshold_tendsto_zero a horizon
    ha hc hc1 hbar hhorizon
  have habove := finiteSusceptible_budgetClockError_above_tendsto_zero
    a horizon ha hc hhorizon hε
  have hsum := hlow.add habove
  simp only [add_zero] at hsum
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards with n
  apply le_trans _ (measureReal_union_le _ _)
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro u hu
  by_cases hbelow : finiteSusceptible (a : ℝ) n u (horizon n) < fluidThreshold c n
  · exact Or.inl hbelow
  · exact Or.inr ⟨Nat.le_of_not_gt hbelow, hu⟩

end HeightPaper.CountCoupling
