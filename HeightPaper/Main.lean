module

public import HeightPaper.Analysis.Critical
public import HeightPaper.Model.Cutoff
public import HeightPaper.Probability.LimitLaw
public import HeightPaper.Probability.Tightness

/-!
# The main height-limit statement and its probabilistic reduction

`MainTheoremStatement` is the exact target for `thm:main`, using the embedded
infection-tree law described in equation `eq:transitions` and Algorithm 1.
This module records the target and conditional integration steps.
`HeightPaper.MainTheorem` proves the target after discharging all stochastic
inputs for the epidemic.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology Asymptotics NNReal

namespace HeightPaper

/-- The actual terminal infection-tree height, normalized as in `thm:main`.
The values at `n = 0` and `n = 1` use Lean's total real division and are irrelevant
to the limit at infinity. -/
noncomputable def normalizedHeightLaw (rate : ℝ≥0) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨(Model.heightLaw rate n).toMeasure.map (fun h : ℕ ↦ (h : ℝ) / Real.log n), inferInstance⟩

/-- The source main theorem, retaining every asymptotically scaled rate sequence
and the full Bernoulli mixture. Its proof is `HeightPaper.mainTheorem`
in the downstream `MainTheorem` module. -/
def MainTheoremStatement : Prop :=
  ∀ (l : ℝ) (hl : 1 < l) (rates : ℕ → ℝ≥0),
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (rates n : ℝ)) atTop (𝓝 l) →
    Tendsto (fun n ↦ normalizedHeightLaw (rates n) n) atTop
      (𝓝 (heightLimitLaw l hl (mainCoefficient l)))

/-- The equivalent target written with the paper's asymptotic-equivalence
hypothesis. This equivalence is used by the final asymptotic-form theorem. -/
theorem mainTheoremStatement_iff_asymptotic :
    MainTheoremStatement ↔
      ∀ (l : ℝ) (hl : 1 < l) (rates : ℕ → ℝ≥0),
        (fun n ↦ (rates n : ℝ)) ~[atTop] (fun n : ℕ ↦ l / n) →
        Tendsto (fun n ↦ normalizedHeightLaw (rates n) n) atTop
          (𝓝 (heightLimitLaw l hl (mainCoefficient l))) := by
  constructor
  · intro h l hl rates hr
    exact h l hl rates ((rate_asymptotic_iff_scaled_tendsto (by linarith)).mp hr)
  · intro h l hl rates hr
    exact h l hl rates ((rate_asymptotic_iff_scaled_tendsto (by linarith)).mpr hr)

/-- Conditional integration of the final height proof with the concrete epidemic
law. Survival probabilities, surviving height concentration, and the finite
weak limit on early extinction are explicit remaining hypotheses. The cutoff
may depend on the tolerance. This is not a proof of `MainTheoremStatement`. -/
theorem main_limit_of_cutoff_estimates (l : ℝ) (hl : 1 < l) (rates : ℕ → ℝ≥0)
    (hcutoff : ∀ ε > (0 : ℝ), ∃ s : ℕ → Set Model.State,
      (∀ n, MeasurableSet (s n)) ∧
      Tendsto (fun n ↦ (Model.terminalStateMeasure (rates n) n).real (s n))
        atTop (𝓝 (1 - 1 / l)) ∧
      Tendsto (fun n ↦ (Model.terminalStateMeasure (rates n) n).real
        {ω | ω ∈ s n ∧ ε ≤ |(Model.height ω : ℝ) / Real.log n - mainCoefficient l|})
        atTop (𝓝 0) ∧
      ∃ ν : ProbabilityMeasure ℝ,
        TendstoInDistribution
          (fun n ↦ (s n)ᶜ.indicator (fun ω ↦ (Model.height ω : ℝ)))
          atTop id (fun n ↦ Model.terminalStateMeasure (rates n) n) (ν : Measure ℝ)) :
    Tendsto (fun n ↦ normalizedHeightLaw (rates n) n) atTop
      (𝓝 (heightLimitLaw l hl (mainCoefficient l))) := by
  have h := height_limit_of_cutoff_estimates (mainCoefficient l) (survivalParameter l hl)
    (μ := fun n ↦ Model.terminalStateMeasure (rates n) n)
    (H := fun _ ω ↦ (Model.height ω : ℝ))
    (fun _ ↦ (Model.measurable_state _).aemeasurable) hcutoff
  have hmaps (n : ℕ) :
      (Model.terminalStateMeasure (rates n) n).map
          (fun ω ↦ (Model.height ω : ℝ) / Real.log n) =
        (normalizedHeightLaw (rates n) n : Measure ℝ) :=
    Model.terminalStateMeasure_map_normalizedHeight (rates n) n
  have hprob (n : ℕ) :
      (⟨(Model.terminalStateMeasure (rates n) n).map
        (fun ω ↦ (Model.height ω : ℝ) / Real.log n), inferInstance⟩ : ProbabilityMeasure ℝ) =
        normalizedHeightLaw (rates n) n := Subtype.ext (hmaps n)
  simpa only [hprob, Measure.map_id, heightLimitLaw] using h.tendsto

/-- The paper's final reduction with its actual floored cutoff event. The first
two hypotheses are the needed consequences of `lem:limflu`; the last is the
surviving-height estimate `eq:toprove`. All are still obligations for the
epidemic, rather than additional assumptions of `MainTheoremStatement`. -/
theorem main_limit_of_source_estimates (l : ℝ) (hl : 1 < l) (rates : ℕ → ℝ≥0)
    (hsurvival : ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun n ↦ (Model.terminalStateMeasure (rates n) n).real
        (Model.sourceSurvivalEvent l δ n)) atTop (𝓝 (1 - 1 / l)))
    (hextinction : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∃ ν : ProbabilityMeasure ℝ,
      TendstoInDistribution
        (fun n ↦ (Model.sourceSurvivalEvent l δ n)ᶜ.indicator
          (fun ω ↦ (Model.height ω : ℝ))) atTop id
        (fun n ↦ Model.terminalStateMeasure (rates n) n) (ν : Measure ℝ))
    (hheight : ∀ ε > (0 : ℝ), ∃ δ ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun n ↦ (Model.terminalStateMeasure (rates n) n).real
        {ω | ω ∈ Model.sourceSurvivalEvent l δ n ∧
          ε ≤ |(Model.height ω : ℝ) / Real.log n - mainCoefficient l|})
        atTop (𝓝 0)) :
    Tendsto (fun n ↦ normalizedHeightLaw (rates n) n) atTop
      (𝓝 (heightLimitLaw l hl (mainCoefficient l))) := by
  apply main_limit_of_cutoff_estimates l hl rates
  intro ε hε
  obtain ⟨δ, hδ, hheightδ⟩ := hheight ε hε
  exact ⟨Model.sourceSurvivalEvent l δ,
    Model.measurableSet_sourceSurvivalEvent l δ, hsurvival δ hδ,
    hheightδ, hextinction δ hδ⟩

end HeightPaper
