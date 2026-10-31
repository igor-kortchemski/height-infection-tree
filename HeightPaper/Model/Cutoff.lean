module

public import HeightPaper.Analysis.FluidParameters
public import HeightPaper.Model.Paths
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# The source's macroscopic survival cutoff

The terminal vertex count recovers the first extinction time. Consequently the
source event can be expressed on the terminal state space, without choosing a
new path law or assuming a stochastic fluid limit.
-/

@[expose] public section

open Filter
open scoped Topology NNReal

namespace HeightPaper.Model

/-- The integer cutoff used in the proof of `thm:main`. -/
noncomputable def sourceCutoff (l δ : ℝ) (n : ℕ) : ℕ :=
  ⌊(1 - δ) * fluidExtinctionTime l * n⌋₊

/-- Survival to the source cutoff, expressed using the terminal tree size.
On supported terminal states, `2 * vertices - 1` is the first extinction time. -/
def sourceSurvivalEvent (l δ : ℝ) (n : ℕ) : Set State :=
  {s | sourceCutoff l δ n ≤ 2 * s.vertices - 1}

theorem measurableSet_sourceSurvivalEvent (l δ : ℝ) (n : ℕ) :
    MeasurableSet (sourceSurvivalEvent l δ n) := trivial

theorem sourceCutoff_le_steps {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) : sourceCutoff l δ n ≤ 2 * n + 1 := by
  have ht := fluidExtinctionTime_lt_two hl
  have ht0 := fluidExtinctionTime_pos hl
  have hc : (1 - δ) * fluidExtinctionTime l ≤ 2 := by nlinarith [hδ.1, hδ.2]
  apply Nat.floor_le_of_le
  exact_mod_cast (show (1 - δ) * fluidExtinctionTime l * (n : ℝ) ≤
    ((2 * n + 1 : ℕ) : ℝ) by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-- The cutoff is positive eventually, so no exceptional small index affects
the asymptotic event used in the paper. -/
theorem sourceCutoff_pos_eventually {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) : ∀ᶠ n in atTop, 0 < sourceCutoff l δ n := by
  have hc : 0 < (1 - δ) * fluidExtinctionTime l :=
    mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
  have hlim : Tendsto (fun n : ℕ ↦ (1 - δ) * fluidExtinctionTime l * (n : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.const_mul_atTop hc
  filter_upwards [hlim.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
  exact Nat.floor_pos.mpr hn

/-- On any supported full path, the terminal-state survival event is exactly
nonextinction immediately before the cutoff event. -/
theorem sourceSurvivalEvent_iff_active {rate : ℝ≥0} {n : ℕ} {path : ℕ → State}
    {l δ : ℝ} (hl : 1 < l) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : SupportedPath rate n (2 * n + 1) path) (hcut : 0 < sourceCutoff l δ n) :
    path (2 * n + 1) ∈ sourceSurvivalEvent l δ n ↔
      (path (sourceCutoff l δ n - 1)).active.Nonempty :=
  hp.cutoff_survival_iff le_rfl hcut (sourceCutoff_le_steps hl hδ n)

end HeightPaper.Model
