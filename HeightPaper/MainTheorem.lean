module

public import HeightPaper.MainFromLaplace
public import HeightPaper.Probability.EpidemicLaplace

/-!
# The height of the infection tree: the main theorem

The source theorem `thm:main` is proved for every nonnegative infection-rate
sequence asymptotic to `l/n`, with `l > 1`. All intermediate stochastic inputs
in the earlier reductions are discharged for the concrete epidemic kernel.
-/

public section

open Filter MeasureTheory
open scoped Topology NNReal Asymptotics

namespace HeightPaper

/-- The source main limit for an arbitrary asymptotically scaled rate sequence. -/
theorem main_limit (l : ℝ) (hl : 1 < l) (rates : ℕ → ℝ≥0)
    (hrates : Tendsto (fun n : ℕ ↦ (n : ℝ) * (rates n : ℝ)) atTop (𝓝 l)) :
    Tendsto (fun n ↦ normalizedHeightLaw (rates n) n) atTop
      (𝓝 (heightLimitLaw l hl (mainCoefficient l))) := by
  apply main_limit_of_laplace l hl rates hrates
  intro δ hδ x hx
  exact Model.sourceCutoff_activeWeight_log_concentration rates hl hδ hx
    (by simpa only [mul_comm] using hrates)

/-- A proof of the unchanged complete target recorded before proof development. -/
theorem mainTheorem : MainTheoremStatement := main_limit

/-- The same limit under the asymptotic-equivalence hypothesis printed in the paper. -/
theorem main_limit_of_asymptotic (l : ℝ) (hl : 1 < l) (rates : ℕ → ℝ≥0)
    (hrates : (fun n ↦ (rates n : ℝ)) ~[atTop] (fun n : ℕ ↦ l / n)) :
    Tendsto (fun n ↦ normalizedHeightLaw (rates n) n) atTop
      (𝓝 (heightLimitLaw l hl (mainCoefficient l))) :=
  mainTheoremStatement_iff_asymptotic.mp mainTheorem l hl rates hrates

end HeightPaper
