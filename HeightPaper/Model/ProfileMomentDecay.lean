module

public import HeightPaper.Model.ProfileMomentBounds
public import HeightPaper.Analysis.ProfileMomentTail

/-!
# Quantitative decay of finite profile martingale differences

The hypotheses are explicit deterministic count and product bounds on a
prescribed event word. The conclusion is an estimate under that word's actual
random-tree history law, with constants uniform in the terminal time.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.Model

theorem prescribedPath_profile_moment_polynomial_le {w p A B c a b : ℝ}
    (hw : 1 ≤ w) (hp : 1 < p) (hp2 : p ≤ 2) (hA : 0 < A) (hB : 0 ≤ B)
    (hc : 0 < c) (hexp : b - p * (a + 1) < -1)
    (events : ℕ → Bool) (n N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events 1 i)
    (hClower : ∀ k ∈ Finset.Ico j N,
      A * ((k + 1 : ℕ) : ℝ) ^ a ≤ realNormalizer w events 1 (k + 1))
    (hCupper : ∀ k ∈ Finset.Ico j N,
      realNormalizer (w ^ p) events 1 k ≤ B * ((k + 1 : ℕ) : ℝ) ^ b)
    (hcount : ∀ k ∈ Finset.Ico j N,
      c * (k + 1 : ℕ) ≤ (prescribedWalk events 1 (k + 1) : ℝ)) :
    (∫ q, ‖normalizedActiveWeight (w : ℂ) q.last /
          prescribedNormalizer (w : ℂ) events 1 N -
        normalizedActiveWeight (w : ℂ) (q.eval j) /
          prescribedNormalizer (w : ℂ) events 1 j‖ ^ p
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N) ≤
      (4 * (2 : ℝ) ^ p) * ((w / (A * c)) ^ p * (2 : ℝ) ^ p * B) *
        ((j : ℝ) ^ (b - p * (a + 1) + 1) / (-(b - p * (a + 1)) - 1)) := by
  have hp0 : 0 ≤ p := by linarith
  have hwp : 1 ≤ w ^ p := Real.one_le_rpow hw hp0
  have hC : prescribedNormalizer (w : ℂ) events 1 N ≠ 0 := by
    rw [prescribedNormalizer_ofReal, ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_realNormalizer hw events 1 N))
  have hmoment := prescribedPath_profile_moment_sub_le (w : ℂ) events (initial n) N j
    hjN hp hp2 (by simpa only [infectious_initial] using hpos)
    (by simpa only [infectious_initial] using hC)
  simp only [infectious_initial] at hmoment
  refine hmoment.trans ?_
  have hconstant : 0 ≤ (w / (A * c)) ^ p * (2 : ℝ) ^ p * B :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by norm_num) _)) hB
  calc
    _ ≤ (4 * (2 : ℝ) ^ p) *
        ∑ k ∈ Finset.Ico j N,
          ((w / (A * c)) ^ p * (2 : ℝ) ^ p * B) *
            ((k + 1 : ℕ) : ℝ) ^ (b - p * (a + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k hk
      apply (prescribedShiftedMomentBound_real_le hw hp0 events n k
        (hpos (k + 1) (by have := (Finset.mem_Ico.mp hk).2; omega))).trans
      exact profile_moment_ratio_le (zero_le_one.trans hw) hp0 hA hB hc
        (by positivity) (zero_le_one.trans (one_le_realNormalizer hwp events 1 k))
        (hClower k hk) (hcount k hk) (hCupper k hk)
    _ = (4 * (2 : ℝ) ^ p) * ((w / (A * c)) ^ p * (2 : ℝ) ^ p * B) *
        ∑ k ∈ Finset.Ico j N, ((k + 1 : ℕ) : ℝ) ^ (b - p * (a + 1)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Ico_succ_rpow_le hexp hj hjN)
      (mul_nonneg (by positivity) hconstant)

end HeightPaper.Model
