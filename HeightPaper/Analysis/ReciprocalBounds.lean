module

public import HeightPaper.Analysis.HarmonicScale
public import HeightPaper.Analysis.ReciprocalAsymptotics

/-! # Finite logarithmic bounds for reciprocal sums -/

public section

open scoped BigOperators

namespace HeightPaper

theorem reciprocal_Ico_log_bounds {K N : ℕ} (hKN : K ≤ N) :
    Real.log N - ((harmonic K : ℝ) + 1) ≤
        ∑ k ∈ Finset.Ico K N, 1 / (k : ℝ) ∧
      (∑ k ∈ Finset.Ico K N, 1 / (k : ℝ)) ≤ Real.log N + 1 := by
  have hsumN : (∑ k ∈ Finset.range N, 1 / (k : ℝ)) =
      (harmonic N : ℝ) - 1 / (N : ℝ) := by
    rw [harmonic_real_eq_sum_range, Finset.sum_range_succ]
    simp only [one_div]
    ring
  have hsumK : (∑ k ∈ Finset.range K, 1 / (k : ℝ)) =
      (harmonic K : ℝ) - 1 / (K : ℝ) := by
    rw [harmonic_real_eq_sum_range, Finset.sum_range_succ]
    simp only [one_div]
    ring
  have hsum := Finset.sum_range_add_sum_Ico (fun k : ℕ ↦ 1 / (k : ℝ)) hKN
  have hninv : 1 / (N : ℝ) ≤ 1 := by
    by_cases hn : N = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn1
  have hkinv : 0 ≤ 1 / (K : ℝ) := by positivity
  have hprefix : 0 ≤ ∑ k ∈ Finset.range K, 1 / (k : ℝ) := by positivity
  have hn := harmonic_sub_log_bounds N
  rw [hsumN] at hsum
  constructor
  · rw [hsumK] at hsum
    linarith only [hn.1, hninv, hkinv, hsum]
  · have hninv0 : 0 ≤ 1 / (N : ℝ) := by positivity
    linarith only [hn.2, hninv0, hprefix, hsum]

end HeightPaper
