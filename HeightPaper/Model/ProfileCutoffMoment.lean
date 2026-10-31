module

public import HeightPaper.Model.ComplexProfileMoments
public import HeightPaper.Model.FiniteNormalizerBounds

/-! # The explicit prefix constant in the shifted Jensen bound -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.Model

theorem realNormalizer_le_pow {v : ℝ} (hv : 1 ≤ v)
    (events : ℕ → Bool) (i₀ k : ℕ) : realNormalizer v events i₀ k ≤ v ^ k := by
  unfold realNormalizer
  calc
    _ ≤ ∏ _i ∈ Finset.range k, v := by
      apply Finset.prod_le_prod₀
      · intro i _
        have := mul_nonneg (sub_nonneg.mpr hv) (birthReciprocal_nonneg events i₀ i)
        linarith
      · intro i _
        have := mul_le_mul_of_nonneg_left (birthReciprocal_le_one events i₀ i)
          (sub_nonneg.mpr hv)
        linarith
    _ = _ := by simp

theorem realNormalizer_split (v : ℝ) (events : ℕ → Bool) (i₀ : ℕ)
    {J k : ℕ} (hJk : J ≤ k) :
    realNormalizer v events i₀ k =
      realNormalizer v events i₀ J * realNormalizerFrom v events i₀ J k := by
  exact (Finset.prod_range_mul_prod_Ico _ hJk).symm

theorem realNormalizerFrom_nonneg {v : ℝ} (hv : 0 ≤ v)
    (events : ℕ → Bool) (i₀ J k : ℕ) : 0 ≤ realNormalizerFrom v events i₀ J k := by
  apply Finset.prod_nonneg
  intro i _
  have ha := birthReciprocal_nonneg events i₀ i
  have hb := birthReciprocal_le_one events i₀ i
  nlinarith [mul_nonneg hv ha]

theorem realNormalizer_le_max_pow {v : ℝ} (hv : 0 ≤ v)
    (events : ℕ → Bool) (i₀ k : ℕ) : realNormalizer v events i₀ k ≤ (max 1 v) ^ k := by
  unfold realNormalizer
  calc
    _ ≤ ∏ _i ∈ Finset.range k, max 1 v := by
      apply Finset.prod_le_prod₀
      · intro i _
        have ha := birthReciprocal_nonneg events i₀ i
        have hb := birthReciprocal_le_one events i₀ i
        nlinarith [mul_nonneg hv ha]
      · intro i _
        by_cases hv1 : 1 ≤ v
        · have h := mul_le_mul_of_nonneg_left (birthReciprocal_le_one events i₀ i)
            (sub_nonneg.mpr hv1)
          have hmax := le_max_right (1 : ℝ) v
          linarith
        · have h := mul_nonpos_of_nonpos_of_nonneg (by linarith : v - 1 ≤ 0)
            (birthReciprocal_nonneg events i₀ i)
          have hmax := le_max_left (1 : ℝ) v
          linarith
    _ = _ := by simp

/-- The Jensen prefix bound also covers negative real tilts, where the
weight norm can be less than one. -/
theorem prescribedPath_shifted_moment_le_max_prefix (w : ℂ)
    (events : ℕ → Bool) (n k J : ℕ) (hJk : J ≤ k)
    {p : ℝ} (hp : 1 ≤ p)
    (hpos : ∀ i ≤ k, 0 < prescribedWalk events 1 i) :
    (∫ q, ‖normalizedActiveWeight w q.last /
      prescribedNormalizerFrom w events 1 J k‖ ^ p
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) k) ≤
      (realNormalizerFrom (‖w‖ ^ p) events 1 J k /
        ‖prescribedNormalizerFrom w events 1 J k‖ ^ p) * (max 1 (‖w‖ ^ p)) ^ J := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hv : 0 ≤ ‖w‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hC : prescribedNormalizerFrom w events 1 J k = 0
  · simp only [hC, div_zero, norm_zero, Real.zero_rpow hp0.ne', integral_zero, zero_mul,
      le_refl]
  · have h := prescribedPath_shifted_normalized_moment_le w events (initial n) k J hp
      (by simpa only [infectious_initial] using hpos)
      (by simpa only [infectious_initial] using hC)
    simp only [infectious_initial, normalizedActiveWeight_initial, one_mul,
      prescribedNormalizer_ofReal, Complex.ofReal_re] at h
    apply h.trans
    rw [realNormalizer_split _ _ _ hJk]
    calc
      _ ≤ ((max 1 (‖w‖ ^ p)) ^ J * realNormalizerFrom (‖w‖ ^ p) events 1 J k) /
          ‖prescribedNormalizerFrom w events 1 J k‖ ^ p := by
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
        exact mul_le_mul_of_nonneg_right (realNormalizer_le_max_pow hv events 1 J)
          (realNormalizerFrom_nonneg hv events 1 J k)
      _ = _ := by ring

/-- The retained random prefix in the shifted Jensen estimate is bounded by
the explicit deterministic factor `(‖w‖ ^ p) ^ J`. No safe-product assumption
is necessary, because a zero denominator makes both sides zero. -/
theorem prescribedPath_shifted_moment_le_prefix (w : ℂ) (hw : 1 ≤ ‖w‖)
    (events : ℕ → Bool) (n k J : ℕ) (hJk : J ≤ k)
    {p : ℝ} (hp : 1 ≤ p)
    (hpos : ∀ i ≤ k, 0 < prescribedWalk events 1 i) :
    (∫ q, ‖normalizedActiveWeight w q.last /
      prescribedNormalizerFrom w events 1 J k‖ ^ p
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) k) ≤
      (realNormalizerFrom (‖w‖ ^ p) events 1 J k /
        ‖prescribedNormalizerFrom w events 1 J k‖ ^ p) * (‖w‖ ^ p) ^ J := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hv : 1 ≤ ‖w‖ ^ p := Real.one_le_rpow hw hp0.le
  by_cases hC : prescribedNormalizerFrom w events 1 J k = 0
  · simp only [hC, div_zero, norm_zero, Real.zero_rpow hp0.ne', integral_zero, zero_mul,
      le_refl]
  · have h := prescribedPath_shifted_normalized_moment_le w events (initial n) k J hp
      (by simpa only [infectious_initial] using hpos)
      (by simpa only [infectious_initial] using hC)
    simp only [infectious_initial, normalizedActiveWeight_initial, one_mul,
      prescribedNormalizer_ofReal, Complex.ofReal_re] at h
    apply h.trans
    rw [realNormalizer_split _ _ _ hJk]
    calc
      _ ≤ ((‖w‖ ^ p) ^ J * realNormalizerFrom (‖w‖ ^ p) events 1 J k) /
          ‖prescribedNormalizerFrom w events 1 J k‖ ^ p := by
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
        exact mul_le_mul_of_nonneg_right (realNormalizer_le_pow hv events 1 J)
          (realNormalizerFrom_pos hv events 1 J k).le
      _ = _ := by ring

end HeightPaper.Model
