module

public import HeightPaper.Analysis.FluidBarrier
public import HeightPaper.Analysis.LatePhase

/-!
# A deterministic lower threshold for the final infection pressure

The threshold lies strictly below the final fluid susceptible fraction, while
its limiting pressure is strictly above the lower comparison pressure. This
gives the unconditional barrier error needed when averaging outgrowth bounds.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal

namespace HeightPaper.Model

noncomputable def latePressureThreshold (l η : ℝ) (n : ℕ) : ℕ :=
  fluidThreshold ((offspringMean l - η / 2) / l) n

theorem latePressureThreshold_fraction_pos {l η : ℝ} (hl : 1 < l)
    (hηm : η < offspringMean l) : 0 < (offspringMean l - η / 2) / l := by
  apply div_pos _ (zero_lt_one.trans hl)
  linarith [offspringMean_pos hl]

theorem latePressureThreshold_fraction_lt_final {l η : ℝ} (hl : 1 < l)
    (hη : 0 < η) : (offspringMean l - η / 2) / l < finalSusceptibleFraction l := by
  unfold finalSusceptibleFraction
  apply (div_lt_div_iff_of_pos_right (zero_lt_one.trans hl)).mpr
  linarith

@[simp] theorem latePressureThreshold_pos (l η : ℝ) (n : ℕ) :
    0 < latePressureThreshold l η n := fluidThreshold_pos _ _

theorem tendsto_latePressureThreshold_pressure (rates : ℕ → ℝ≥0) {l η : ℝ}
    (hl : 1 < l) (hηm : η < offspringMean l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ (rates n : ℝ) * latePressureThreshold l η n)
      atTop (𝓝 (offspringMean l - η / 2)) := by
  have h := tendsto_fluidThreshold_pressure rates (latePressureThreshold_fraction_pos hl hηm).le hrates
  have heq : l * ((offspringMean l - η / 2) / l) = offspringMean l - η / 2 := by
    field_simp
  simpa only [latePressureThreshold, heq] using h

/-- The integer threshold eventually meets both the population and lower
comparison-pressure requirements of the finite outgrowth bound. -/
theorem eventually_latePressureThreshold_bounds (rates : ℕ → ℝ≥0) {l η : ℝ}
    (hl : 1 < l) (hη : 0 < η) (hηm : η < offspringMean l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∀ᶠ n : ℕ in atTop, latePressureThreshold l η n ≤ n ∧
      offspringMean l - η < (rates n : ℝ) * latePressureThreshold l η n ∧
      1 / (1 + (rates n : ℝ) * latePressureThreshold l η n) ≤
        1 / (1 + offspringMean l - η) := by
  have hc := latePressureThreshold_fraction_pos hl hηm
  have hcf := latePressureThreshold_fraction_lt_final hl hη
  filter_upwards [eventually_fluidThreshold_le hc.le (hcf.trans (finalSusceptibleFraction_lt_one hl)),
    (tendsto_latePressureThreshold_pressure rates hl hηm hrates).eventually
      (Ioi_mem_nhds (show offspringMean l - η < offspringMean l - η / 2 by linarith))] with n hn hp
  refine ⟨hn, hp, ?_⟩
  apply one_div_le_one_div_of_le (by linarith : 0 < 1 + offspringMean l - η)
  linarith

/-- The lower susceptible barrier fails with vanishing probability on every
linear horizon, including when no survival event is imposed. -/
theorem evolve_below_latePressureThreshold_tendsto_zero
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l η T : ℝ}
    (hl : 1 < l) (hη : 0 < η) (hηm : η < offspringMean l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
      {s | s.susceptible < latePressureThreshold l η n}) atTop (𝓝 0) :=
  evolve_below_fluidThreshold_tendsto_zero rates horizon hl
    (latePressureThreshold_fraction_pos hl hηm)
    (latePressureThreshold_fraction_lt_final hl hη) hrates hhorizon

end HeightPaper.Model
