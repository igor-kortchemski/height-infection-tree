module

public import HeightPaper.Probability.EpidemicNormalizer
public import HeightPaper.Probability.EventWordAveraging
public import HeightPaper.Probability.LogFirstMoment
public import HeightPaper.Model.ProfileUpperBounds

/-!
# Actual epidemic profile and pre-cutoff height upper bounds

Conditioning on a positive observed event word supplies the prescribed
first-moment bounds. Finite partition averaging and the proved product
asymptotics then give unconditional upper-tail limits on endpoint activity.
-/

public section

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace HeightPaper.Model

theorem pathMeasure_normalizedProfile_goodNormalizer_tail_le (rate : ℝ≥0) (n N : ℕ)
    {w B D : ℝ} (hw : 1 ≤ w) (hB : 0 < B) (hD : 0 < D) :
    (pathMeasure rate n N).real {p | p.last.active.Nonempty ∧
      observedNormalizer w p.eval N ≤ B ∧ D ≤ activeWeight w p.last / (infectious p.last : ℝ)} ≤
      B / D := by
  apply pathMeasure_positive_eventWord_bound rate n N
    (fun events ↦ realNormalizer w events 1 N ≤ B)
    (fun _ ↦ {p | D ≤ activeWeight w p.last / (infectious p.last : ℝ)})
    (div_nonneg hB.le hD.le)
  intro events hpos hC
  exact (prescribedPath_normalizedProfile_tail_le (zero_le_one.trans hw) hD events n N hpos).trans
    (div_le_div_of_nonneg_right hC hD.le)

theorem pathMeasure_height_goodNormalizer_tail_le (rate : ℝ≥0) (n N : ℕ)
    {x B H : ℝ} (hx : 0 ≤ x) (hB : 0 < B) :
    (pathMeasure rate n N).real {p | p.last.active.Nonempty ∧
      observedNormalizer (Real.exp x) p.eval N ≤ B ∧ H ≤ (height p.last : ℝ)} ≤
      (1 + Real.exp x * N * B) / Real.exp (x * H) := by
  apply pathMeasure_positive_eventWord_bound rate n N
    (fun events ↦ realNormalizer (Real.exp x) events 1 N ≤ B)
    (fun _ ↦ {p | H ≤ (height p.last : ℝ)}) (by positivity)
  intro events hpos hC
  exact (prescribedPath_real_height_tail_le hx events n N hpos).trans
    (div_le_div_of_nonneg_right
      (add_le_add_right (mul_le_mul_of_nonneg_left hC (by positivity)) 1)
      (Real.exp_nonneg _))

/-- The actual normalized active Laplace profile has no excessive logarithmic
growth; the matching lower estimate is a separate obligation. -/
theorem path_normalizedLaplace_log_upper
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T x : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l)) (hx : 0 ≤ x)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (pathMeasure (rates n) n (horizon n)).real {p |
        p.last.active.Nonempty ∧ ε ≤ Real.log (realNormalizedLaplace x p.last) / Real.log n -
          growthFactor l * (Real.exp x - 1)}) atTop (𝓝 0) := by
  apply log_upper_tail_of_normalizer
    (fun n ↦ pathMeasure (rates n) n (horizon n))
    (fun _ ↦ {p | p.last.active.Nonempty})
    (fun n p ↦ observedNormalizer (Real.exp x) p.eval (horizon n))
    (fun _ p ↦ realNormalizedLaplace x p.last)
  · intro n p _
    exact zero_lt_one.trans_le (one_le_realNormalizer (Real.one_le_exp_iff.mpr hx) _ _ _)
  · intro n p hp
    exact zero_lt_one.trans_le (one_le_realNormalizedLaplace hx p.last hp)
  · exact path_observedNormalizer_log_concentration rates horizon hl hT
      (Real.one_le_exp_iff.mpr hx) hrates hhorizon
  · intro n B D hB hD
    exact pathMeasure_normalizedProfile_goodNormalizer_tail_le (rates n) n (horizon n)
      (Real.one_le_exp_iff.mpr hx) hB hD

/-- Height before any fixed pre-extinction fluid time stays below the early
profile frontier. This uses the total tree, including recovered vertices. -/
theorem path_height_div_log_upper
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (pathMeasure (rates n) n (horizon n)).real {p |
        p.last.active.Nonempty ∧ growthFactor l * Real.exp (profileRoot l) + ε ≤
          (height p.last : ℝ) / Real.log n}) atTop (𝓝 0) := by
  apply height_upper_tail_of_normalizer
    (fun n ↦ pathMeasure (rates n) n (horizon n))
    (fun _ ↦ {p | p.last.active.Nonempty})
    (fun n p ↦ observedNormalizer (Real.exp (profileRoot l)) p.eval (horizon n))
    (fun _ p ↦ (height p.last : ℝ)) horizon
    (profileRoot_pos hl) (mul_pos (growthFactor_pos hl) (Real.exp_pos _))
    (profileRoot_height_balance hl) hhorizon
  · intro n p _
    exact zero_lt_one.trans_le
      (one_le_realNormalizer (Real.one_le_exp_iff.mpr (profileRoot_pos hl).le) _ _ _)
  · exact path_observedNormalizer_log_concentration rates horizon hl hT
      (Real.one_le_exp_iff.mpr (profileRoot_pos hl).le) hrates hhorizon
  · intro n B H hB
    exact pathMeasure_height_goodNormalizer_tail_le (rates n) n (horizon n)
      (profileRoot_pos hl).le hB

end HeightPaper.Model
