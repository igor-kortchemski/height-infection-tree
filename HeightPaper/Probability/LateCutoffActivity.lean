module

public import HeightPaper.Probability.SourceSurvival

/-!
# The cutoff activity convention

Source survival uses activity immediately before the floored cutoff. The
outgrowth decomposition uses the active roots at the cutoff itself. Their
probability difference tends to zero, with the endpoint convention kept exact.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

theorem SupportedPath.sourceSurvival_of_cutoff_active {rate : ℝ≥0} {n : ℕ}
    {path : ℕ → State} {l δ : ℝ} (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hp : SupportedPath rate n (2 * n + 1) path) (hcut : 0 < sourceCutoff l δ n)
    (ha : (path (sourceCutoff l δ n)).active.Nonempty) :
    path (2 * n + 1) ∈ sourceSurvivalEvent l δ n := by
  apply (sourceSurvivalEvent_iff_active hl hδ hp hcut).mpr
  by_contra h
  have hz := Finset.not_nonempty_iff_eq_empty.mp h
  have heq := hp.absorbed_stable (by omega : sourceCutoff l δ n - 1 ≤ sourceCutoff l δ n)
    (sourceCutoff_le_steps hl hδ n) hz
  rw [heq, hz] at ha
  exact Finset.not_nonempty_empty ha

theorem sourceSurvival_cutoff_active_probability_eq {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (rate : ℝ≥0) (n : ℕ) (hcut : 0 < sourceCutoff l δ n) :
    (pathMeasure rate n (2 * n + 1)).real
      {p | p.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        (p.eval (sourceCutoff l δ n)).active.Nonempty} =
      (evolve rate n (sourceCutoff l δ n)).toMeasure.real {s | s.active.Nonempty} := by
  rw [← pathMeasure_event_at rate n (2 * n + 1) (sourceCutoff l δ n) (sourceCutoff_le_steps hl hδ n)]
  apply measureReal_congr
  filter_upwards [ae_supportedPath rate n (2 * n + 1)] with p hp
  apply propext
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hp.sourceSurvival_of_cutoff_active hl hδ hcut h, h⟩⟩

theorem sourceSurvival_cutoff_inactive_probability_eq {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (rate : ℝ≥0) (n : ℕ) (hcut : 0 < sourceCutoff l δ n) :
    (pathMeasure rate n (2 * n + 1)).real
      {p | p.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        ¬(p.eval (sourceCutoff l δ n)).active.Nonempty} =
      (terminalStateMeasure rate n).real (sourceSurvivalEvent l δ n) -
        (evolve rate n (sourceCutoff l δ n)).toMeasure.real {s | s.active.Nonempty} := by
  have hh := measureReal_inter_add_sdiff₀ (μ := pathMeasure rate n (2 * n + 1))
    (s := {p | p.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n})
    (t := {p | (p.eval (sourceCutoff l δ n)).active.Nonempty})
    (show MeasurableSet {p : FinitePath (2 * n + 1) |
      (p.eval (sourceCutoff l δ n)).active.Nonempty} from trivial).nullMeasurableSet
  change (pathMeasure rate n (2 * n + 1)).real
      {p | p.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧ (p.eval (sourceCutoff l δ n)).active.Nonempty} +
    (pathMeasure rate n (2 * n + 1)).real
      {p | p.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧ ¬(p.eval (sourceCutoff l δ n)).active.Nonempty} =
    (pathMeasure rate n (2 * n + 1)).real {p | p.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n} at hh
  rw [sourceSurvival_cutoff_active_probability_eq hl hδ rate n hcut,
    pathMeasure_event_at rate n (2 * n + 1) (2 * n + 1) le_rfl] at hh
  change _ = (evolve rate n (2 * n + 1)).toMeasure.real _ - _
  linarith

/-- The distinction between activity at the cutoff and source survival has
vanishing probability under the actual joint epidemic law. -/
theorem sourceSurvival_cutoff_inactive_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {p | p.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        ¬(p.eval (sourceCutoff l δ n)).active.Nonempty}) atTop (𝓝 0) := by
  let T := (1 - δ) * fluidExtinctionTime l
  have hT0 : 0 < T := mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
  have hTt : T < fluidExtinctionTime l := by
    dsimp [T]
    nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  have htime : Tendsto (fun n : ℕ ↦ (sourceCutoff l δ n : ℝ) / n) atTop (𝓝 T) :=
    tendsto_floor_fraction hT0.le
  have hext := evolve_extinction_tendsto_reciprocal rates (sourceCutoff l δ) hl ⟨hT0, hTt⟩ hrates htime
  have hactive : Tendsto (fun n ↦ (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
      {s | s.active.Nonempty}) atTop (𝓝 (1 - 1 / l)) := by
    simp_rw [evolve_active_probability_eq]
    exact tendsto_const_nhds.sub hext
  have hd := (sourceSurvivalEvent_probability_tendsto rates hl hδ hrates).sub hactive
  simp only [sub_self] at hd
  apply hd.congr'
  filter_upwards [sourceCutoff_pos_eventually hl hδ] with n hn
  exact (sourceSurvival_cutoff_inactive_probability_eq hl hδ (rates n) n hn).symm

end HeightPaper.Model
