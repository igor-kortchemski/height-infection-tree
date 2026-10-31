module

public import HeightPaper.Model.PrescribedPath
public import HeightPaper.Analysis.ProfileProduct

/-!
# Real prescribed-profile normalizers

The complex product at a real positive weight is a real product. Nonnegative
tilts need no zero-avoidance cutoff. The logarithmic remainder is expressed in
the actual prescribed active-count walk, ready for its stochastic estimates.
-/

@[expose] public section

open scoped BigOperators

namespace HeightPaper.Model

/-- Reciprocal post-birth count, zero at recovery epochs. -/
noncomputable def birthReciprocal (events : ℕ → Bool) (i₀ k : ℕ) : ℝ :=
  if events k then 1 / ((prescribedWalk events i₀ k : ℝ) + 1) else 0

theorem birthReciprocal_nonneg (events : ℕ → Bool) (i₀ k : ℕ) :
    0 ≤ birthReciprocal events i₀ k := by
  unfold birthReciprocal
  split_ifs <;> positivity

/-- The same profile normalizer, expressed entirely over the reals. -/
noncomputable def realNormalizer (w : ℝ) (events : ℕ → Bool) (i₀ N : ℕ) : ℝ :=
  ∏ k ∈ Finset.range N, (1 + (w - 1) * birthReciprocal events i₀ k)

@[simp] theorem realNormalizer_zero (w : ℝ) (events : ℕ → Bool) (i₀ : ℕ) :
    realNormalizer w events i₀ 0 = 1 := by simp [realNormalizer]

theorem realNormalizer_succ (w : ℝ) (events : ℕ → Bool) (i₀ N : ℕ) :
    realNormalizer w events i₀ (N + 1) = realNormalizer w events i₀ N *
      (1 + (w - 1) * birthReciprocal events i₀ N) := by
  exact Finset.prod_range_succ _ _

theorem prescribedNormalizer_ofReal (w : ℝ) (events : ℕ → Bool) (i₀ N : ℕ) :
    prescribedNormalizer (w : ℂ) events i₀ N = (realNormalizer w events i₀ N : ℂ) := by
  induction N with
  | zero => simp [prescribedNormalizer]
  | succ N ih =>
      rw [prescribedNormalizer, ih, realNormalizer_succ, Complex.ofReal_mul]
      congr 1
      cases h : events N <;>
        simp [prescribedProfileFactor, birthReciprocal, h, div_eq_mul_inv]

theorem one_le_realNormalizer {w : ℝ} (hw : 1 ≤ w) (events : ℕ → Bool) (i₀ N : ℕ) :
    1 ≤ realNormalizer w events i₀ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [realNormalizer_succ]
      apply one_le_mul_of_one_le_of_one_le ih
      have := mul_nonneg (sub_nonneg.mpr hw) (birthReciprocal_nonneg events i₀ N)
      linarith

theorem realNormalizer_mono {w : ℝ} (hw : 1 ≤ w) (events : ℕ → Bool) (i₀ : ℕ) :
    Monotone (realNormalizer w events i₀) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [realNormalizer_succ]
  apply le_mul_of_one_le_right (zero_le_one.trans (one_le_realNormalizer hw events i₀ N))
  have := mul_nonneg (sub_nonneg.mpr hw) (birthReciprocal_nonneg events i₀ N)
  linarith

/-- The exact prescribed product satisfies the quadratic logarithmic bound. -/
theorem realNormalizer_log_remainder {w : ℝ} (hw : 1 ≤ w)
    (events : ℕ → Bool) (i₀ N : ℕ) :
    |Real.log (realNormalizer w events i₀ N) -
      (w - 1) * ∑ k ∈ Finset.range N, birthReciprocal events i₀ k| ≤
      (w - 1) ^ 2 * ∑ k ∈ Finset.range N, (birthReciprocal events i₀ k) ^ 2 :=
  abs_log_prod_one_add_sub_le _ _ (sub_nonneg.mpr hw)
    (fun k _ ↦ birthReciprocal_nonneg events i₀ k)

end HeightPaper.Model
