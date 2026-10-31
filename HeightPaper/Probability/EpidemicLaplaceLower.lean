module

public import HeightPaper.Probability.EpidemicProfileLower
public import HeightPaper.Model.ProfileLowerGrid
public import HeightPaper.Analysis.CountSlopeChoice

/-!
# The actual epidemic lower Laplace profile

A finite tilt bootstrap works in one neighborhood of the ideal normalizer
slope. Sharp count parameters can be chosen inside that neighborhood and
arbitrarily close to the exact slope. Averaging and a final deterministic
squeeze give the source exponent for every interior positive tilt.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

/-- The normalized real Laplace profile has the matching lower logarithmic
exponent under the actual epidemic law. No stochastic limit is assumed. -/
theorem path_normalizedLaplace_log_lower
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T x : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (pathMeasure (rates n) n (horizon n)).real
      {p | p.last.active.Nonempty ∧
        ε ≤ growthFactor l * (Real.exp x - 1) -
          Real.log (realNormalizedLaplace x p.last) / Real.log n}) atTop (𝓝 0) := by
  obtain ⟨η, hη, hgrid⟩ := exists_goodProduct_uniformProfileLower hl hx.1 hx.2
  intro ε hε
  have hd : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hx.1)
  let θ := min η (ε / (4 * (Real.exp x - 1)))
  have hθ : 0 < θ := lt_min hη (div_pos hε (by positivity))
  obtain ⟨lo, hi, hlo, hloD, hhiD, _, hlowClose, huppClose⟩ := exists_count_slopes_near_growthFactor hl hθ
  have hlowη := hlowClose.trans_le (min_le_left η (ε / (4 * (Real.exp x - 1))))
  have huppη := huppClose.trans_le (min_le_left η (ε / (4 * (Real.exp x - 1))))
  let a := (Real.exp x - 1) * ((1 + 1 / hi) / 2)
  have hU : ∀ c > (0 : ℝ), ∀ A B : ℝ → ℝ,
      (∀ w ≥ (1 : ℝ), 0 < A w ∧ 0 < B w) → ∀ K : ℕ, 1 ≤ K →
      UniformProfileLower (GoodProductWord ((1 + 1 / hi) / 2) ((1 + 1 / lo) / 2) c A B K) x a := by
    intro c hc A B hAB K _
    exact hgrid _ _ hlowη huppη c A B K hc hAB
  have hlim := path_normalizedLaplace_log_lower_of_uniform rates horizon hl hT hx.1.le hlo hloD hhiD
    hrates hhorizon hU (ε / 2) (half_pos hε)
  have hclose : growthFactor l * (Real.exp x - 1) - a < ε / 4 := by
    have hh := hlowClose.trans_le (min_le_right η (ε / (4 * (Real.exp x - 1))))
    have hh' := (abs_lt.mp hh).1
    have hmul := mul_lt_mul_of_pos_right hh' hd
    have heq : (ε / (4 * (Real.exp x - 1))) * (Real.exp x - 1) = ε / 4 := by
      field_simp
    dsimp only [a]
    nlinarith only [hmul, heq]
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hlim
  intro n
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro p hp
  refine ⟨hp.1, ?_⟩
  linarith only [hp.2, hclose, hε]

end HeightPaper.Model
