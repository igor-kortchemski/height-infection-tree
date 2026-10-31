module

public import HeightPaper.Model.InfiniteProfileLp
public import HeightPaper.Model.ProfileCutoffMoment

/-!
# Removing the cutoff from profile normalization

When the real part of the weight is at least one, every normalizer prefix
has modulus at least one. Shifted profile tail bounds therefore also bound
the corresponding unshifted tails, without comparing random cutoffs.
-/

@[expose] public section

open scoped BigOperators

namespace HeightPaper.Model

theorem prescribedNormalizer_split (w : ℂ) (events : ℕ → Bool) (i₀ : ℕ)
    {J k : ℕ} (hJk : J ≤ k) :
    prescribedNormalizer w events i₀ k =
      prescribedNormalizer w events i₀ J * prescribedNormalizerFrom w events i₀ J k := by
  rw [← prescribedNormalizerFrom_zero, ← prescribedNormalizerFrom_zero]
  unfold prescribedNormalizerFrom
  simp only [Nat.Ico_zero_eq_range]
  exact (Finset.prod_range_mul_prod_Ico _ hJk).symm

theorem one_le_norm_prescribedNormalizerFrom {w : ℂ} (hw : 1 ≤ w.re)
    (events : ℕ → Bool) (i₀ J k : ℕ) :
    1 ≤ ‖prescribedNormalizerFrom w events i₀ J k‖ := by
  rw [prescribedNormalizerFrom_eq_birthReciprocal, norm_prod]
  apply Finset.one_le_prod₀
  intro i _
  have ha := birthReciprocal_nonneg events i₀ i
  have hre : 1 ≤ (1 + (w - 1) * (birthReciprocal events i₀ i : ℂ)).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.sub_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hw) ha)
  exact hre.trans (Complex.re_le_norm _)

theorem one_le_norm_prescribedNormalizer {w : ℂ} (hw : 1 ≤ w.re)
    (events : ℕ → Bool) (i₀ k : ℕ) :
    1 ≤ ‖prescribedNormalizer w events i₀ k‖ := by
  rw [← prescribedNormalizerFrom_zero]
  exact one_le_norm_prescribedNormalizerFrom hw events i₀ 0 k

theorem prescribedNormalizedProfile_zero_eq_div_prefix (w : ℂ) (events : ℕ → Bool)
    (s₀ s : State) {J k : ℕ} (hJk : J ≤ k) :
    prescribedNormalizedProfile w events s₀ 0 k s =
      prescribedNormalizedProfile w events s₀ J k s /
        prescribedNormalizer w events (infectious s₀) J := by
  simp only [prescribedNormalizedProfile, prescribedNormalizerFrom_zero]
  rw [prescribedNormalizer_split w events (infectious s₀) hJk, div_div]
  rw [mul_comm]

theorem norm_unshifted_profile_difference_le {w : ℂ} (hw : 1 ≤ w.re)
    (events : ℕ → Bool) (s₀ s t : State) {J j k : ℕ} (hJj : J ≤ j) (hJk : J ≤ k) :
    ‖prescribedNormalizedProfile w events s₀ 0 k s -
      prescribedNormalizedProfile w events s₀ 0 j t‖ ≤
      ‖prescribedNormalizedProfile w events s₀ J k s -
        prescribedNormalizedProfile w events s₀ J j t‖ := by
  rw [prescribedNormalizedProfile_zero_eq_div_prefix w events s₀ s hJk,
    prescribedNormalizedProfile_zero_eq_div_prefix w events s₀ t hJj, ← sub_div, norm_div]
  exact div_le_self (norm_nonneg _) (one_le_norm_prescribedNormalizer hw events _ J)

theorem norm_unshifted_limit_difference_le {w : ℂ} (hw : 1 ≤ w.re)
    (events : ℕ → Bool) (s₀ s : State) {J k : ℕ} (hJk : J ≤ k) (L : ℂ) :
    ‖L / prescribedNormalizer w events (infectious s₀) J -
      prescribedNormalizedProfile w events s₀ 0 k s‖ ≤
      ‖L - prescribedNormalizedProfile w events s₀ J k s‖ := by
  rw [prescribedNormalizedProfile_zero_eq_div_prefix w events s₀ s hJk, ← sub_div, norm_div]
  exact div_le_self (norm_nonneg _) (one_le_norm_prescribedNormalizer hw events _ J)

end HeightPaper.Model
