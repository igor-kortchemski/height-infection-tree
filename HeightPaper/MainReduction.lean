module

public import HeightPaper.Main
public import HeightPaper.Probability.SourceSurvival
public import HeightPaper.Probability.EarlyExtinctionTightness

/-!
# Integrating the proved survival probability

The source cutoff probability and early-extinction height negligibility are
discharged for every allowed rate sequence. The final reduction has only the
surviving-height estimate as an input. A full unscaled early-height weak limit
is a stronger source obligation retained separately.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace HeightPaper

/-- The main limit from two height estimates, with the epidemic's survival
probability supplied by its proved kernel analysis. -/
theorem main_limit_of_source_height_estimates (l : ℝ) (hl : 1 < l) (rates : ℕ → ℝ≥0)
    (hrates : Tendsto (fun n : ℕ ↦ (n : ℝ) * (rates n : ℝ)) atTop (𝓝 l))
    (hextinction : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (Model.terminalStateMeasure (rates n) n).real
        {ω | ω ∉ Model.sourceSurvivalEvent l δ n ∧
          ε ≤ |(Model.height ω : ℝ) / Real.log n|}) atTop (𝓝 0))
    (hheight : ∀ ε > (0 : ℝ), ∃ δ ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun n ↦ (Model.terminalStateMeasure (rates n) n).real
        {ω | ω ∈ Model.sourceSurvivalEvent l δ n ∧
          ε ≤ |(Model.height ω : ℝ) / Real.log n - mainCoefficient l|})
        atTop (𝓝 0)) :
    Tendsto (fun n ↦ normalizedHeightLaw (rates n) n) atTop
      (𝓝 (heightLimitLaw l hl (mainCoefficient l))) := by
  have hr : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l) := by
    simpa only [mul_comm] using hrates
  have h := tendstoInDistribution_of_survival_estimates_at_each_scale
    (mainCoefficient l) (survivalParameter l hl)
    (μ := fun n ↦ Model.terminalStateMeasure (rates n) n)
    (H := fun n ω ↦ (Model.height ω : ℝ) / Real.log n)
    (fun _ ↦ (Model.measurable_state _).aemeasurable)
    (by
      intro ε hε
      obtain ⟨δ, hδ, hheightδ⟩ := hheight ε hε
      exact ⟨Model.sourceSurvivalEvent l δ, Model.measurableSet_sourceSurvivalEvent l δ,
        Model.sourceSurvivalEvent_probability_tendsto rates hl hδ hr, hheightδ,
        hextinction δ hδ ε hε⟩)
  have hprob (n : ℕ) :
      (⟨(Model.terminalStateMeasure (rates n) n).map
        (fun ω ↦ (Model.height ω : ℝ) / Real.log n), inferInstance⟩ : ProbabilityMeasure ℝ) =
        normalizedHeightLaw (rates n) n :=
    Subtype.ext (Model.terminalStateMeasure_map_normalizedHeight (rates n) n)
  simpa only [hprob, Measure.map_id, heightLimitLaw] using h.tendsto

/-- The main theorem now reduces solely to the height estimate on surviving
outbreaks. The survival probability and early-extinction contribution are
proved from the epidemic kernel for every allowed rate sequence. -/
theorem main_limit_of_surviving_height (l : ℝ) (hl : 1 < l) (rates : ℕ → ℝ≥0)
    (hrates : Tendsto (fun n : ℕ ↦ (n : ℝ) * (rates n : ℝ)) atTop (𝓝 l))
    (hheight : ∀ ε > (0 : ℝ), ∃ δ ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun n ↦ (Model.terminalStateMeasure (rates n) n).real
        {ω | ω ∈ Model.sourceSurvivalEvent l δ n ∧
          ε ≤ |(Model.height ω : ℝ) / Real.log n - mainCoefficient l|})
        atTop (𝓝 0)) :
    Tendsto (fun n ↦ normalizedHeightLaw (rates n) n) atTop
      (𝓝 (heightLimitLaw l hl (mainCoefficient l))) := by
  apply main_limit_of_source_height_estimates l hl rates hrates _ hheight
  intro δ hδ ε hε
  apply Model.sourceExtinction_height_div_log_tendsto_zero rates hl hδ _ hε
  simpa only [mul_comm] using hrates

end HeightPaper
