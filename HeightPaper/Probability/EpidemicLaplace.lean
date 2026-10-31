module

public import HeightPaper.Probability.EpidemicLaplaceLower
public import HeightPaper.Probability.EpidemicLaplaceIntegration
public import HeightPaper.Model.Cutoff

/-!
# Real Laplace asymptotics of the epidemic active profile

The actual upper and lower estimates and the active-count limit are combined
here. These results have only the paper's rate scaling and the indicated
interior time and tilt restrictions as hypotheses.
-/

public section

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace HeightPaper.Model

/-- The full active profile has logarithmic exponent `1 + γ(exp x - 1)` at
any interior positive tilt and any pre-extinction macroscopic time. -/
theorem evolve_activeWeight_log_concentration
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T x : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp x) s) / Real.log n -
          (1 + growthFactor l * (Real.exp x - 1))|}) atTop (𝓝 0) :=
  evolve_activeWeight_log_concentration_of_lower rates horizon hl hT hx.1.le hrates hhorizon
    (path_normalizedLaplace_log_lower rates horizon hl hT hx hrates hhorizon)

/-- The exact real profile input at the manuscript's floored cutoff. -/
theorem sourceCutoff_activeWeight_log_concentration
    (rates : ℕ → ℝ≥0) {l δ x : ℝ} (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp x) s) / Real.log n -
          (1 + growthFactor l * (Real.exp x - 1))|}) atTop (𝓝 0) := by
  have htime : (1 - δ) * fluidExtinctionTime l ∈ Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [fluidExtinctionTime_pos hl, hδ.1]
  exact evolve_activeWeight_log_concentration rates (fun n ↦ sourceCutoff l δ n)
    hl htime hx hrates (tendsto_floor_fraction htime.1.le)

end HeightPaper.Model
