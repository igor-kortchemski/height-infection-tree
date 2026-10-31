module

public import HeightPaper.Probability.GhostBudgetBarrierLimit

/-!
# Lower susceptible barrier for the unabsorbed budget process

The exact padded-tree marginal and the generic stopped-law comparison carry
the harmonic barrier estimate back to the common-uniform budget chain.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

theorem finiteSusceptible_below_eq_ghostStopped (l : ℝ≥0)
    (n H threshold : ℕ) (hthreshold : 0 < threshold) :
    uniformLaw.real {u | finiteSusceptible l n u H < threshold} =
      (Model.stoppedCountLaw (l / n) threshold
        (Model.ghostBudgetStart n H) H).toMeasure.real
          {s | s.susceptible < threshold} := by
  let B : Set ℕ := {a | a < threshold}
  let C : Set Model.State := {s | s.susceptible < threshold}
  have hbudget : Measurable (fun u : ℕ → ℝ ↦ finiteSusceptible (l : ℝ) n u H) :=
    measurable_finiteSusceptible (l : ℝ) n H
  have hlast :
      (Model.kernelPathMeasure (fun _ ↦ Model.step (l / n))
        (Model.ghostBudgetStart n H) H).map Model.FinitePath.last =
        (FinitePMF.kernelEvolve (PMF.pure (Model.ghostBudgetStart n H))
          (fun _ ↦ Model.step (l / n)) H).toMeasure := by
    simpa only [Model.FinitePath.eval_last] using
      Model.kernelPathMeasure_map_eval (fun _ ↦ Model.step (l / n))
        (Model.ghostBudgetStart n H) H H le_rfl
  have hmap := ghostBudgetTree_susceptible_law l n H le_rfl
  have hmeasure : uniformLaw.real {u | finiteSusceptible l n u H < threshold} =
      (FinitePMF.kernelEvolve (PMF.pure (Model.ghostBudgetStart n H))
        (fun _ ↦ Model.step (l / n)) H).toMeasure.real C := by
    calc
      _ = (uniformLaw.map (fun u ↦ finiteSusceptible (l : ℝ) n u H)).real B := by
        rw [Measure.real, Measure.real,
          Measure.map_apply hbudget (show MeasurableSet B from trivial)]
        rfl
      _ = ((Model.kernelPathMeasure (fun _ ↦ Model.step (l / n))
          (Model.ghostBudgetStart n H) H).map
          (fun q ↦ q.last.susceptible)).real B := congrArg (fun μ : Measure ℕ ↦ μ.real B) hmap
      _ = ((Model.kernelPathMeasure (fun _ ↦ Model.step (l / n))
          (Model.ghostBudgetStart n H) H).map Model.FinitePath.last).real C := by
        rw [Measure.real, Measure.real,
          Measure.map_apply (Model.FinitePath.measurable _)
            (show MeasurableSet C from trivial),
          Measure.map_apply (Model.FinitePath.measurable _)
            (show MeasurableSet B from trivial)]
        rfl
      _ = _ := by rw [hlast]
  rw [hmeasure]
  exact (congrArg ENNReal.toReal
    (Model.stoppedCountLaw_measure_below_start (l / n) threshold
      (Model.ghostBudgetStart n H) H hthreshold)).symm

theorem finiteSusceptible_below_fluidThreshold_tendsto_zero
    (a : ℝ≥0) (horizon : ℕ → ℕ)
    {T c : ℝ} (ha : 1 < (a : ℝ)) (hc : 0 < c) (hc1 : c < 1)
    (hbar : T < fluidBarrier (a : ℝ) c)
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    Tendsto (fun n ↦ uniformLaw.real
      {u | finiteSusceptible (a : ℝ) n u (horizon n) <
        fluidThreshold c n}) atTop (𝓝 0) := by
  let rates : ℕ → ℝ≥0 := fun n ↦ a / n
  have hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 (a : ℝ)) := by
    apply (tendsto_const_nhds (x := (a : ℝ))).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [rates, NNReal.coe_div, NNReal.coe_natCast, div_mul_cancel₀ _ hnR]
  have hstop := Model.ghostBudget_stopped_below_fluidThreshold_tendsto_zero
    rates horizon ha hc hc1 hbar hrates hhorizon
  apply hstop.congr'
  filter_upwards with n
  exact (finiteSusceptible_below_eq_ghostStopped a n (horizon n)
    (fluidThreshold c n) (fluidThreshold_pos c n)).symm

theorem finiteSusceptible_macroscopic_lower_fraction
    (a : ℝ≥0) {T : ℝ} (ha : 1 < (a : ℝ)) (hT : 0 < T) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      Tendsto (fun n ↦ uniformLaw.real
        {u | finiteSusceptible (a : ℝ) n u ⌊T * n⌋₊ <
          fluidThreshold c n}) atTop (𝓝 0) := by
  obtain ⟨c, hc, hc1, hbar⟩ :=
    Model.exists_ghostBudget_fluidBarrier (a : ℝ) T
      (zero_lt_one.trans ha) hT.le
  exact ⟨c, hc, hc1,
    finiteSusceptible_below_fluidThreshold_tendsto_zero a
      (fun n ↦ ⌊T * n⌋₊) ha hc hc1 hbar
      (tendsto_floor_fraction hT.le)⟩

end HeightPaper.CountCoupling
