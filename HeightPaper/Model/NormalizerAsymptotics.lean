module

public import HeightPaper.Model.ObservedEvents
public import HeightPaper.Analysis.HarmonicScale

/-!
# Normalizer asymptotics from actual reciprocal-count estimates

Harmonic telescoping and the quadratic logarithm remainder isolate the precise
count estimates required for the real profile normalizer. The filter version
also applies to vanishing exceptional probabilities on surviving histories.
-/

@[expose] public section

open Filter
open scoped Topology BigOperators NNReal

namespace HeightPaper.Model

noncomputable def pathReciprocalSum (path : ℕ → State) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, 1 / (infectious (path k) : ℝ)

noncomputable def pathReciprocalSquareSum (path : ℕ → State) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, 1 / (infectious (path k) : ℝ) ^ 2

noncomputable def observedBirthSum (path : ℕ → State) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, birthReciprocal (observedBirth path) 1 k

noncomputable def observedNormalizer (w : ℝ) (path : ℕ → State) (N : ℕ) : ℝ :=
  realNormalizer w (observedBirth path) 1 N

variable {ι : Type*} {ℓ : Filter ι}
    (path : ι → ℕ → State) (population horizon : ι → ℕ) (rate : ι → ℝ≥0)
    (scale : ι → ℝ) (hscale : Tendsto scale ℓ atTop)
    (hsupport : ∀ᶠ i in ℓ, SupportedPath (rate i) (population i) (horizon i) (path i) ∧
      (path i (horizon i)).active.Nonempty)
    {a r : ℝ}
    (hfinal : Tendsto (fun i ↦ Real.log (infectious (path i (horizon i))) / scale i) ℓ (𝓝 a))
    (hreciprocal : Tendsto (fun i ↦ pathReciprocalSum (path i) (horizon i) / scale i) ℓ (𝓝 r))
    (hsquare : Tendsto (fun i ↦ pathReciprocalSquareSum (path i) (horizon i) / scale i) ℓ (𝓝 0))

include hscale hsupport hfinal hreciprocal hsquare

/-- The birth reciprocal coefficient is half the sum of the harmonic boundary
coefficient and the total reciprocal coefficient. -/
theorem observedBirthSum_ratio_tendsto :
    Tendsto (fun i ↦ observedBirthSum (path i) (horizon i) / scale i)
      ℓ (𝓝 ((a + r) / 2)) := by
  let D : ι → ℝ := fun i ↦ (harmonic (infectious (path i (horizon i))) : ℝ) - 1 +
    pathReciprocalSum (path i) (horizon i) - 2 * observedBirthSum (path i) (horizon i)
  have hD : Tendsto (fun i ↦ D i / scale i) ℓ (𝓝 0) := by
    apply squeeze_zero' _ _ hsquare
    · filter_upwards [hsupport, hscale.eventually_gt_atTop 0] with i hi hs
      exact div_nonneg (hi.1.observed_birth_sum_error_bounds hi.2).1 hs.le
    · filter_upwards [hsupport, hscale.eventually_gt_atTop 0] with i hi hs
      apply div_le_div_of_nonneg_right _ hs.le
      simpa only [D, pathReciprocalSum, observedBirthSum, pathReciprocalSquareSum,
        div_pow, one_pow] using (hi.1.observed_birth_sum_error_bounds hi.2).2
  have hh := tendsto_harmonic_ratio_of_log_ratio
    (fun i ↦ infectious (path i (horizon i))) scale hscale hfinal
  have ht := (((hh.sub (hscale.const_div_atTop 1)).add hreciprocal).sub hD).div_const 2
  simp only [sub_zero] at ht
  convert ht using 1
  funext i
  dsimp only [D]
  ring

/-- Real normalizer logarithms have the corresponding coefficient. All
quadratic errors are bounded by the actual reciprocal-square sum. -/
theorem observedNormalizer_log_ratio_tendsto {w : ℝ} (hw : 1 ≤ w) :
    Tendsto (fun i ↦ Real.log (observedNormalizer w (path i) (horizon i)) / scale i)
      ℓ (𝓝 ((w - 1) * ((a + r) / 2))) := by
  have hB := observedBirthSum_ratio_tendsto path population horizon rate scale hscale
    hsupport hfinal hreciprocal hsquare
  have herror : Tendsto (fun i ↦
      (Real.log (observedNormalizer w (path i) (horizon i)) -
        (w - 1) * observedBirthSum (path i) (horizon i)) / scale i) ℓ (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    have hbound := hsquare.const_mul ((w - 1) ^ 2)
    rw [mul_zero] at hbound
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) _ hbound
    filter_upwards [hsupport, hscale.eventually_gt_atTop 0] with i hi hs
    have hsq : (∑ k ∈ Finset.range (horizon i),
        (birthReciprocal (observedBirth (path i)) 1 k) ^ 2) ≤
        pathReciprocalSquareSum (path i) (horizon i) := by
      apply Finset.sum_le_sum
      intro k hk
      have hpos := hi.1.observedWalk_pos hi.2 (Finset.mem_range.mp hk).le
      have hb := birthReciprocal_le_count_inv (observedBirth (path i)) 1 k hpos
      rw [hi.1.observedWalk_eq hi.2 (Finset.mem_range.mp hk).le] at hb
      simpa only [div_pow, one_pow] using
        pow_le_pow_left₀ (birthReciprocal_nonneg (observedBirth (path i)) 1 k) hb 2
    have hrem := (realNormalizer_log_remainder hw (observedBirth (path i)) 1 (horizon i)).trans
      (mul_le_mul_of_nonneg_left hsq (sq_nonneg (w - 1)))
    rw [abs_div, abs_of_pos hs]
    exact (div_le_div_of_nonneg_right hrem hs.le).trans_eq (by ring)
  have ht := herror.add (hB.const_mul (w - 1))
  rw [zero_add] at ht
  convert ht using 1
  funext i
  ring

end HeightPaper.Model
