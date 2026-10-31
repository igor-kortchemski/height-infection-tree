module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Quantitative tails for profile moment sums

The shifted integer power sum is bounded uniformly in its terminal time.
The explicit decay power is used when the initial cutoff grows with the
population size.
-/

public section

open scoped BigOperators

namespace HeightPaper

theorem sum_Ico_succ_rpow_le {a : ℝ} (ha : a < -1) {j N : ℕ}
    (hj : 1 ≤ j) (hjN : j ≤ N) :
    ∑ k ∈ Finset.Ico j N, ((k + 1 : ℕ) : ℝ) ^ a ≤
      (j : ℝ) ^ (a + 1) / (-a - 1) := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hjN' : (j : ℝ) ≤ N := by exact_mod_cast hjN
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ a) (Set.Icc (j : ℝ) N) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : a ≤ 0)).mono
      (fun x hx ↦ lt_of_lt_of_le hjpos hx.1)
  calc
    _ ≤ ∫ x in (j : ℝ)..N, x ^ a := hanti.sum_le_integral_Ico hjN
    _ = ((N : ℝ) ^ (a + 1) - (j : ℝ) ^ (a + 1)) / (a + 1) := by
      apply integral_rpow
      right
      refine ⟨ne_of_lt ha, ?_⟩
      rw [Set.uIcc_of_le hjN']
      exact fun h ↦ (not_le_of_gt hjpos) h.1
    _ = ((j : ℝ) ^ (a + 1) - (N : ℝ) ^ (a + 1)) / (-a - 1) := by
      rw [show -a - 1 = -(a + 1) by ring, div_neg]
      rw [← neg_div, neg_sub]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact sub_le_self _ (Real.rpow_nonneg (Nat.cast_nonneg N) _)

end HeightPaper
