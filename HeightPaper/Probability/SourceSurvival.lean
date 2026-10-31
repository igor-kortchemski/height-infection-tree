module

public import HeightPaper.Probability.ExtinctionLimit
public import HeightPaper.Model.Cutoff

/-!
# The paper's actual cutoff survival probability

The terminal-state cutoff event is identified with the earlier active
coordinate under the actual finite path law. Its limiting probability follows
from the extinction theorem without a coupling hypothesis.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal

namespace HeightPaper.Model

theorem evolve_active_probability_eq (rate : ℝ≥0) (n k : ℕ) :
    (evolve rate n k).toMeasure.real {s | s.active.Nonempty} =
      1 - (evolve rate n k).toMeasure.real {s | infectious s = 0} := by
  have heq : {s : State | s.active.Nonempty} = {s : State | infectious s = 0}ᶜ := by
    ext s
    simp only [mem_ofPred_eq, mem_compl_iff, infectious, Finset.card_eq_zero,
      Finset.nonempty_iff_ne_empty]
  rw [heq, measureReal_compl (show MeasurableSet {s : State | infectious s = 0} from trivial)]
  simp

/-- Exact finite-population identification of the paper's terminal-state
cutoff probability with survival just before the cutoff event. -/
theorem sourceSurvivalEvent_probability_eq {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (rate : ℝ≥0) (n : ℕ)
    (hcut : 0 < sourceCutoff l δ n) :
    (terminalStateMeasure rate n).real (sourceSurvivalEvent l δ n) =
      1 - (evolve rate n (sourceCutoff l δ n - 1)).toMeasure.real {s | infectious s = 0} := by
  rw [← evolve_active_probability_eq]
  change (evolve rate n (2 * n + 1)).toMeasure.real (sourceSurvivalEvent l δ n) = _
  rw [← pathMeasure_event_at rate n (2 * n + 1) (2 * n + 1) le_rfl,
    ← pathMeasure_event_at rate n (2 * n + 1) (sourceCutoff l δ n - 1)
      (by have := sourceCutoff_le_steps hl hδ n; omega)]
  apply measureReal_congr
  filter_upwards [ae_supportedPath rate n (2 * n + 1)] with p hp
  exact propext (sourceSurvivalEvent_iff_active hl hδ hp hcut)

/-- The source's Bernoulli survival probability is derived for every rate
sequence allowed by its scaling assumption. -/
theorem sourceSurvivalEvent_probability_tendsto
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ (terminalStateMeasure (rates n) n).real (sourceSurvivalEvent l δ n))
      atTop (𝓝 (1 - 1 / l)) := by
  let T := (1 - δ) * fluidExtinctionTime l
  have hT0 : 0 < T := mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
  have hTt : T < fluidExtinctionTime l := by
    dsimp [T]
    nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  have hfloor : Tendsto (fun n : ℕ ↦ (sourceCutoff l δ n : ℝ) / n) atTop (𝓝 T) :=
    tendsto_floor_fraction hT0.le
  have htime : Tendsto (fun n : ℕ ↦ ((sourceCutoff l δ n - 1 : ℕ) : ℝ) / n)
      atTop (𝓝 T) := by
    have hh := hfloor.sub (tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [sourceCutoff_pos_eventually hl hδ] with n hn
    rw [Nat.cast_sub (by omega : 1 ≤ sourceCutoff l δ n), Nat.cast_one, sub_div]
  have hext := evolve_extinction_tendsto_reciprocal rates
    (fun n ↦ sourceCutoff l δ n - 1) hl ⟨hT0, hTt⟩ hrates htime
  apply ((tendsto_const_nhds (x := (1 : ℝ))).sub hext).congr'
  filter_upwards [sourceCutoff_pos_eventually hl hδ] with n hn
  exact (sourceSurvivalEvent_probability_eq hl hδ (rates n) n hn).symm

end HeightPaper.Model
