module

public import HeightPaper.Model.FullHeightFromProfile
public import HeightPaper.Probability.PrecutoffHeight
public import HeightPaper.Probability.SourceSurvivalTransfer
public import HeightPaper.Analysis.Critical

/-! # The source surviving-height estimate from actual Laplace asymptotics

This result discharges the pre-cutoff height, finite depth mesh, random root
counts, outgrowth tails, pressure estimates, and cutoff convention. The sole
remaining analytic input is the actual real-Laplace profile asymptotics.
-/

public section

open Filter Set MeasureTheory
open scoped Topology NNReal

namespace HeightPaper.Model

/-- The source estimate holds for every sufficiently late fixed cutoff, with
one cutoff range chosen for each tolerance as in equation `eq:toprove`. -/
theorem eventually_sourceSurvival_height_concentration_of_laplace
    (rates : ℕ → ℝ≥0) {l : ℝ} (hl : 1 < l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hLap : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp v) s) / Real.log n -
          (1 + growthFactor l * (Real.exp v - 1))|}) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      Tendsto (fun n ↦ (terminalStateMeasure (rates n) n).real
        {s | s ∈ sourceSurvivalEvent l δ n ∧
          ε ≤ |(height s : ℝ) / Real.log n - mainCoefficient l|}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨δ₀, hδ₀, hconcentration⟩ := eventually_cutoff_fullHeight_concentration_of_profile
    rates hl hrates hLap (fun δ hδ b hb ↦ sourceCutoff_height_upper rates hl hδ hrates hb) hε
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδsmall
  have hδ : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδsmall.1, hδsmall.2.trans (hδ₀.2.trans (by norm_num))⟩
  have hbad : Tendsto (fun n ↦ (continuationSampleLaw
      (evolve (rates n) n (sourceCutoff l δ n)) (rates n) (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
      {s | s.cutoff.active.Nonempty ∧ s.final ∈
        {s : State | ε ≤ |(height s : ℝ) / Real.log n - mainCoefficient l|}}) atTop (𝓝 0) := by
    simpa only [mainCoefficient_eq_heightCoefficient hl, Set.mem_ofPred_eq] using hconcentration δ hδsmall
  simpa only [Set.mem_ofPred_eq] using sourceSurvival_event_tendsto_zero_of_continuation_active rates
    (fun n ↦ {s | ε ≤ |(height s : ℝ) / Real.log n - mainCoefficient l|}) hl hδ hrates hbad

/-- The exact surviving-height input of the main theorem's integration step,
conditional only on the actual Laplace-profile asymptotics at fixed cutoffs. -/
theorem sourceSurvival_height_concentration_of_laplace
    (rates : ℕ → ℝ≥0) {l : ℝ} (hl : 1 < l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hLap : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp v) s) / Real.log n -
          (1 + growthFactor l * (Real.exp v - 1))|}) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), ∃ δ ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun n ↦ (terminalStateMeasure (rates n) n).real
        {s | s ∈ sourceSurvivalEvent l δ n ∧
          ε ≤ |(height s : ℝ) / Real.log n - mainCoefficient l|}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨δ₀, hδ₀, hconcentration⟩ := eventually_sourceSurvival_height_concentration_of_laplace
    rates hl hrates hLap ε hε
  let δ := δ₀ / 2
  have hδsmall : δ ∈ Ioo (0 : ℝ) δ₀ := ⟨half_pos hδ₀.1, half_lt_self hδ₀.1⟩
  have hδ : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδsmall.1, hδsmall.2.trans (hδ₀.2.trans (by norm_num))⟩
  exact ⟨δ, hδ, hconcentration δ hδsmall⟩

end HeightPaper.Model
