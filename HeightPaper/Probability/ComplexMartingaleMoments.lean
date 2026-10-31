module

public import HeightPaper.Probability.MartingaleMoments
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.MeanInequalities

/-!
# Complex finite-kernel martingale moments

Real and imaginary parts reduce the complex moment estimate to the proved
scalar inequality. The bound uses averaged increments, so it applies to the
random profile factors of the tree process.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.FinitePMF

theorem complex_norm_rpow_le_parts (z : ℂ) {p : ℝ} (hp : 1 ≤ p) :
    ‖z‖ ^ p ≤ (2 : ℝ) ^ (p - 1) * (|RCLike.re z| ^ p + |RCLike.im z| ^ p) := by
  have hsum : (|z.re| + |z.im|) ^ p ≤
      (2 : ℝ) ^ (p - 1) * (|z.re| ^ p + |z.im| ^ p) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
      ⟨|z.re|, abs_nonneg _⟩ ⟨|z.im|, abs_nonneg _⟩ hp
  simpa only [RCLike.re_eq_complex_re, RCLike.im_eq_complex_im] using
    (Real.rpow_le_rpow (norm_nonneg z) (Complex.norm_le_abs_re_add_abs_im z)
      (zero_le_one.trans hp)).trans hsum

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A complex finite-kernel martingale satisfies a p-th moment bound with an
explicit constant, for `1 < p ≤ 2`. The increment hypothesis is already averaged
over the current state, and is required only through the stated horizon. -/
theorem kernelEvolve_norm_rpow_le_integrated (initial : PMF α) (K : ℕ → α → PMF α)
    (hi : initial.support.Finite) (hK : ∀ k s, (K k s).support.Finite)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure))
    (F : ℕ → α → ℂ) (B : ℕ → ℝ) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (N : ℕ)
    (hmean : ∀ k < N, ∀ s ∈ (kernelEvolve initial K k).support,
      (∫ t, F (k + 1) t ∂(K k s).toMeasure) = F k s)
    (hincrement : ∀ k < N,
      (∫ s, ∫ t, ‖F (k + 1) t - F k s‖ ^ p ∂(K k s).toMeasure
        ∂(kernelEvolve initial K k).toMeasure) ≤ B k)
    (a : ℂ) :
    (∫ s, ‖F N s - a‖ ^ p ∂(kernelEvolve initial K N).toMeasure) ≤
      (2 : ℝ) ^ p * ((∫ s, ‖F 0 s - a‖ ^ p ∂initial.toMeasure) +
        4 * ∑ j ∈ Finset.range N, B j) := by
  have hnonneg : 0 ≤ p := by linarith
  have hcoord (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, |L z| ≤ ‖z‖) :
      (∫ s, |L (F N s) - L a| ^ p ∂(kernelEvolve initial K N).toMeasure) ≤
        (∫ s, ‖F 0 s - a‖ ^ p ∂initial.toMeasure) + 4 * ∑ j ∈ Finset.range N, B j := by
    have hh := kernelEvolve_abs_rpow_le_integrated initial K hi hK hm
      (fun k s ↦ L (F k s)) B hp hp2 N
      (fun k hk s hs ↦ by
        rw [L.integral_comp_comm (integrable_of_finite_support _ (hK k s) _), hmean k hk s hs])
      (fun k hk ↦ ?_) (L a)
    · refine hh.trans ?_
      apply add_le_add _ le_rfl
      apply integral_mono (integrable_of_finite_support _ hi _)
        (integrable_of_finite_support _ hi _)
      intro s
      change |L (F 0 s) - L a| ^ p ≤ ‖F 0 s - a‖ ^ p
      rw [← map_sub]
      exact Real.rpow_le_rpow (abs_nonneg _) (hL _) hnonneg
    · refine le_trans ?_ (hincrement k hk)
      apply integral_mono (integrable_of_finite_support _
        (kernelEvolve_support_finite initial K hi hK k) _)
        (integrable_of_finite_support _ (kernelEvolve_support_finite initial K hi hK k) _)
      intro s
      apply integral_mono (integrable_of_finite_support _ (hK k s) _)
        (integrable_of_finite_support _ (hK k s) _)
      intro t
      change |L (F (k + 1) t) - L (F k s)| ^ p ≤ ‖F (k + 1) t - F k s‖ ^ p
      rw [← map_sub]
      exact Real.rpow_le_rpow (abs_nonneg _) (hL _) hnonneg
  have hre := hcoord RCLike.reCLM RCLike.abs_re_le_norm
  have him := hcoord RCLike.imCLM RCLike.abs_im_le_norm
  have hμ := kernelEvolve_support_finite initial K hi hK N
  have hC : 0 ≤ (2 : ℝ) ^ (p - 1) := Real.rpow_nonneg (by norm_num) _
  have htwo : (2 : ℝ) ^ (p - 1) * 2 = (2 : ℝ) ^ p := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring
  calc
    _ ≤ ∫ s, (2 : ℝ) ^ (p - 1) *
        (|RCLike.re (F N s - a)| ^ p + |RCLike.im (F N s - a)| ^ p)
        ∂(kernelEvolve initial K N).toMeasure :=
      integral_mono (integrable_of_finite_support _ hμ _) (integrable_of_finite_support _ hμ _)
        (fun s ↦ complex_norm_rpow_le_parts (F N s - a) hp.le)
    _ = (2 : ℝ) ^ (p - 1) *
        ((∫ s, |RCLike.re (F N s) - RCLike.re a| ^ p ∂(kernelEvolve initial K N).toMeasure) +
          ∫ s, |RCLike.im (F N s) - RCLike.im a| ^ p ∂(kernelEvolve initial K N).toMeasure) := by
      simp_rw [map_sub]
      rw [integral_const_mul, integral_add (integrable_of_finite_support _ hμ _)
        (integrable_of_finite_support _ hμ _)]
    _ ≤ (2 : ℝ) ^ (p - 1) *
        (2 * ((∫ s, ‖F 0 s - a‖ ^ p ∂initial.toMeasure) +
          4 * ∑ j ∈ Finset.range N, B j)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [RCLike.reCLM_apply, RCLike.imCLM_apply, two_mul] using add_le_add hre him
    _ = _ := by rw [← mul_assoc, htwo]

end HeightPaper.FinitePMF
