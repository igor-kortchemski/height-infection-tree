module

public import HeightPaper.Analysis.MomentRemainder
public import HeightPaper.Probability.FinitePMF
public import HeightPaper.Probability.KernelIteration

/-!
# Finite martingale moment bounds

The linear term in the scalar moment remainder cancels under a zero-mean
increment. These results prove the moment inequality used by the real-Laplace
profile route, instead of importing it as an assumption.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.FinitePMF

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Jensen's linear remainder cancels under the actual finite expectation.
The numerical constant four is uniform over the full range `1 < p ≤ 2`. -/
theorem integral_abs_rpow_le_of_mean (μ : PMF α) (hμ : μ.support.Finite)
    (f : α → ℝ) {a p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hmean : ∫ x, f x ∂μ.toMeasure = a) :
    (∫ x, |f x| ^ p ∂μ.toMeasure) ≤
      |a| ^ p + 4 * ∫ x, |f x - a| ^ p ∂μ.toMeasure := by
  have hbound : (∫ x, |f x| ^ p ∂μ.toMeasure) ≤
      ∫ x, |a| ^ p + momentSlope p a * (f x - a) + 4 * |f x - a| ^ p ∂μ.toMeasure :=
    integral_mono (integrable_of_finite_support μ hμ _) (integrable_of_finite_support μ hμ _)
      (fun _ ↦ abs_rpow_le_linear_add_remainder hp hp2)
  have heq : (∫ x, |a| ^ p + momentSlope p a * (f x - a) +
      4 * |f x - a| ^ p ∂μ.toMeasure) =
      |a| ^ p + 4 * ∫ x, |f x - a| ^ p ∂μ.toMeasure := by
    rw [integral_add (integrable_of_finite_support μ hμ _) (integrable_of_finite_support μ hμ _),
      integral_add (integrable_const _) (integrable_of_finite_support μ hμ _),
      integral_const_mul, integral_const_mul,
      integral_sub (integrable_of_finite_support μ hμ _) (integrable_const _), hmean]
    simp
  exact hbound.trans_eq heq

/-- The one-step moment estimate may be centered at any earlier fixed value,
as required for a martingale difference between two distinct times. -/
theorem integral_abs_rpow_sub_le_of_mean (μ : PMF α) (hμ : μ.support.Finite)
    (f : α → ℝ) {a p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (b : ℝ)
    (hmean : ∫ x, f x ∂μ.toMeasure = a) :
    (∫ x, |f x - b| ^ p ∂μ.toMeasure) ≤
      |a - b| ^ p + 4 * ∫ x, |f x - a| ^ p ∂μ.toMeasure := by
  have hh := integral_abs_rpow_le_of_mean μ hμ (fun x ↦ f x - b) hp hp2
    (show (∫ x, f x - b ∂μ.toMeasure) = a - b by
      rw [integral_sub (integrable_of_finite_support μ hμ _) (integrable_const _), hmean]
      simp)
  simpa only [sub_sub_sub_cancel_right] using hh

/-- Iterating the one-step inequality gives a martingale moment bound for
actual time-dependent finite kernels. Mean preservation is required only at
reachable states. This is the real-valued replacement for the cited martingale
increment inequality, with a harmless uniform constant four. -/
theorem kernelEvolve_abs_rpow_le (initial : PMF α) (K : ℕ → α → PMF α)
    (hi : initial.support.Finite) (hK : ∀ k s, (K k s).support.Finite)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure))
    (F : ℕ → α → ℝ) (B : ℕ → ℝ) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hmean : ∀ k s, s ∈ (kernelEvolve initial K k).support →
      (∫ t, F (k + 1) t ∂(K k s).toMeasure) = F k s)
    (hincrement : ∀ k s, s ∈ (kernelEvolve initial K k).support →
      (∫ t, |F (k + 1) t - F k s| ^ p ∂(K k s).toMeasure) ≤ B k)
    (a : ℝ) (k : ℕ) :
    (∫ s, |F k s - a| ^ p ∂(kernelEvolve initial K k).toMeasure) ≤
      (∫ s, |F 0 s - a| ^ p ∂initial.toMeasure) + 4 * ∑ j ∈ Finset.range k, B j := by
  induction k with
  | zero => simp [kernelEvolve]
  | succ k ih =>
    rw [kernelEvolve_integral_succ initial K hi hK hm]
    have hs := kernelEvolve_support_finite initial K hi hK k
    calc
      _ ≤ ∫ s, |F k s - a| ^ p + 4 * B k ∂(kernelEvolve initial K k).toMeasure := by
        apply integral_mono_ae (integrable_of_finite_support _ hs _)
          (integrable_of_finite_support _ hs _)
        apply ae_of_forall_mem_support
        intro s hmem
        exact (integral_abs_rpow_sub_le_of_mean (K k s) (hK k s) (F (k + 1))
          hp hp2 a (hmean k s hmem)).trans (by linarith [hincrement k s hmem])
      _ = (∫ s, |F k s - a| ^ p ∂(kernelEvolve initial K k).toMeasure) + 4 * B k := by
        rw [integral_add (integrable_of_finite_support _ hs _) (integrable_const _)]
        simp
      _ ≤ _ := by rw [Finset.sum_range_succ]; linarith

/-- The increment estimate may be imposed only after averaging over the
current state. This accommodates profile-dependent conditional bounds without
asserting a uniform bound over all trees. Only steps before `N` are required. -/
theorem kernelEvolve_abs_rpow_le_integrated (initial : PMF α) (K : ℕ → α → PMF α)
    (hi : initial.support.Finite) (hK : ∀ k s, (K k s).support.Finite)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure))
    (F : ℕ → α → ℝ) (B : ℕ → ℝ) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (N : ℕ)
    (hmean : ∀ k < N, ∀ s ∈ (kernelEvolve initial K k).support,
      (∫ t, F (k + 1) t ∂(K k s).toMeasure) = F k s)
    (hincrement : ∀ k < N,
      (∫ s, ∫ t, |F (k + 1) t - F k s| ^ p ∂(K k s).toMeasure
        ∂(kernelEvolve initial K k).toMeasure) ≤ B k)
    (a : ℝ) :
    (∫ s, |F N s - a| ^ p ∂(kernelEvolve initial K N).toMeasure) ≤
      (∫ s, |F 0 s - a| ^ p ∂initial.toMeasure) + 4 * ∑ j ∈ Finset.range N, B j := by
  induction N with
  | zero => simp [kernelEvolve]
  | succ N ih =>
      have ih' := ih (fun k hk ↦ hmean k (by omega)) (fun k hk ↦ hincrement k (by omega))
      rw [kernelEvolve_integral_succ initial K hi hK hm]
      have hs := kernelEvolve_support_finite initial K hi hK N
      calc
        _ ≤ ∫ s, |F N s - a| ^ p +
            4 * ∫ t, |F (N + 1) t - F N s| ^ p ∂(K N s).toMeasure
              ∂(kernelEvolve initial K N).toMeasure := by
          apply integral_mono_ae (integrable_of_finite_support _ hs _)
            (integrable_of_finite_support _ hs _)
          apply ae_of_forall_mem_support
          intro s hmem
          exact integral_abs_rpow_sub_le_of_mean (K N s) (hK N s) (F (N + 1))
            hp hp2 a (hmean N (by omega) s hmem)
        _ = (∫ s, |F N s - a| ^ p ∂(kernelEvolve initial K N).toMeasure) +
            4 * ∫ s, ∫ t, |F (N + 1) t - F N s| ^ p ∂(K N s).toMeasure
              ∂(kernelEvolve initial K N).toMeasure := by
          rw [integral_add (integrable_of_finite_support _ hs _)
            (integrable_of_finite_support _ hs _), integral_const_mul]
        _ ≤ _ := by
          rw [Finset.sum_range_succ]
          linarith [hincrement N (by omega)]

end HeightPaper.FinitePMF
