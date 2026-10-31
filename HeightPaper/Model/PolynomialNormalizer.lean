module

public import HeightPaper.Model.RealNormalizer
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polynomial bounds for the real product normalizer

Uniform birth-reciprocal bounds and a bounded square sum give absolute
polynomial bounds. Constants remain explicit so the result can be applied
simultaneously to the two weights in a profile-moment estimate.
-/

public section

open scoped BigOperators

namespace HeightPaper.Model

theorem realNormalizer_polynomial_bounds {w base lo hi C D : ℝ}
    (hw : 1 ≤ w) (hbase : 0 < base) (events : ℕ → Bool) (i₀ N : ℕ)
    (hlower : lo * Real.log base - C ≤ ∑ k ∈ Finset.range N, birthReciprocal events i₀ k)
    (hupper : (∑ k ∈ Finset.range N, birthReciprocal events i₀ k) ≤ hi * Real.log base + C)
    (hsquare : (∑ k ∈ Finset.range N, (birthReciprocal events i₀ k) ^ 2) ≤ D) :
    Real.exp (-((w - 1) * C + (w - 1) ^ 2 * D)) * base ^ ((w - 1) * lo) ≤
        realNormalizer w events i₀ N ∧
      realNormalizer w events i₀ N ≤
        Real.exp ((w - 1) * C + (w - 1) ^ 2 * D) * base ^ ((w - 1) * hi) := by
  have hrem := (realNormalizer_log_remainder hw events i₀ N).trans
    (mul_le_mul_of_nonneg_left hsquare (sq_nonneg (w - 1)))
  have hmulL := mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr hw)
  have hmulU := mul_le_mul_of_nonneg_left hupper (sub_nonneg.mpr hw)
  have hb := abs_le.mp hrem
  have hpos : 0 < realNormalizer w events i₀ N :=
    zero_lt_one.trans_le (one_le_realNormalizer hw events i₀ N)
  constructor
  · calc
      _ = Real.exp (-((w - 1) * C + (w - 1) ^ 2 * D) +
          Real.log base * ((w - 1) * lo)) := by
        rw [Real.rpow_def_of_pos hbase, Real.exp_add]
      _ ≤ Real.exp (Real.log (realNormalizer w events i₀ N)) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hb.1, hmulL]
      _ = _ := Real.exp_log hpos
  · calc
      _ = Real.exp (Real.log (realNormalizer w events i₀ N)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp ((w - 1) * C + (w - 1) ^ 2 * D +
          Real.log base * ((w - 1) * hi)) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hb.2, hmulU]
      _ = _ := by rw [Real.rpow_def_of_pos hbase, Real.exp_add]

end HeightPaper.Model
