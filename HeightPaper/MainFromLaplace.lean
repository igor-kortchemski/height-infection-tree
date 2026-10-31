module

public import HeightPaper.MainReduction
public import HeightPaper.Model.SourceHeightFromLaplace

/-!
# The main theorem reduced to the actual Laplace profile

All model, extinction, fluid, and height-comparison inputs are discharged.
The remaining Laplace-profile assumption is stated explicitly and is not
asserted as proved by this reduction.
-/

public section

open Filter MeasureTheory
open scoped Topology NNReal

namespace HeightPaper

theorem main_limit_of_laplace (l : ℝ) (hl : 1 < l) (rates : ℕ → ℝ≥0)
    (hrates : Tendsto (fun n : ℕ ↦ (n : ℝ) * (rates n : ℝ)) atTop (𝓝 l))
    (hLap : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ v ∈ Set.Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (Model.evolve (rates n) n (Model.sourceCutoff l δ n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (Model.activeWeight (Real.exp v) s) / Real.log n -
          (1 + growthFactor l * (Real.exp v - 1))|}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ normalizedHeightLaw (rates n) n) atTop
      (𝓝 (heightLimitLaw l hl (mainCoefficient l))) := by
  apply main_limit_of_surviving_height l hl rates hrates
  exact Model.sourceSurvival_height_concentration_of_laplace rates hl
    (by simpa only [mul_comm] using hrates) hLap

end HeightPaper
