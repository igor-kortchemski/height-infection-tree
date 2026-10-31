module

public import HeightPaper.Probability.EpidemicProfileUpper
public import HeightPaper.Model.Cutoff

/-! # State-law and source-cutoff forms of the actual early height bound -/

public section

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace HeightPaper.Model

theorem evolve_normalizedLaplace_log_upper
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T x : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l)) (hx : 0 ≤ x)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ Real.log (realNormalizedLaplace x s) / Real.log n -
          growthFactor l * (Real.exp x - 1)}) atTop (𝓝 0) := by
  intro ε hε
  apply (path_normalizedLaplace_log_upper rates horizon hl hT hx hrates hhorizon ε hε).congr
  intro n
  simpa only [FinitePath.eval_last, Set.mem_ofPred_eq] using pathMeasure_event_at (rates n) n (horizon n)
    (horizon n) le_rfl {s | s.active.Nonempty ∧
      ε ≤ Real.log (realNormalizedLaplace x s) / Real.log n - growthFactor l * (Real.exp x - 1)}

theorem evolve_height_div_log_upper
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s |
        s.active.Nonempty ∧ growthFactor l * Real.exp (profileRoot l) + ε ≤
          (height s : ℝ) / Real.log n}) atTop (𝓝 0) := by
  intro ε hε
  apply (path_height_div_log_upper rates horizon hl hT hrates hhorizon ε hε).congr
  intro n
  simpa only [FinitePath.eval_last, Set.mem_ofPred_eq] using pathMeasure_event_at (rates n) n (horizon n)
    (horizon n) le_rfl {s | s.active.Nonempty ∧ growthFactor l * Real.exp (profileRoot l) + ε ≤
      (height s : ℝ) / Real.log n}

/-- The exact old-tree upper-height input required by the full mesh assembly. -/
theorem sourceCutoff_height_upper
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {b : ℝ} (hb : growthFactor l * Real.exp (profileRoot l) < b) :
    Tendsto (fun n ↦ (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real {s |
      s.active.Nonempty ∧ b < (height s : ℝ) / Real.log n}) atTop (𝓝 0) := by
  have htime : (1 - δ) * fluidExtinctionTime l ∈ Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [fluidExtinctionTime_pos hl, hδ.1]
  have hlim := evolve_height_div_log_upper rates (fun n ↦ sourceCutoff l δ n) hl htime hrates
    (tendsto_floor_fraction htime.1.le) (b - growthFactor l * Real.exp (profileRoot l)) (sub_pos.mpr hb)
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hlim
  intro n
  apply measureReal_mono _ (measure_ne_top _ _)
  intro s hs
  exact ⟨hs.1, by linarith [hs.2]⟩

end HeightPaper.Model
