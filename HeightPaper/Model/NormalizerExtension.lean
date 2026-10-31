module

public import HeightPaper.Model.BirthHarmonic

/-! # Extending early polynomial normalizers across a bounded reciprocal tail -/

public section

open scoped BigOperators

namespace HeightPaper.Model

theorem realNormalizer_le_mul_exp_tail {w L : ℝ} (hw : 1 ≤ w)
    (events : ℕ → Bool) (i₀ : ℕ) {E N : ℕ} (hEN : E ≤ N)
    (htail : (∑ k ∈ Finset.Ico E N, birthReciprocal events i₀ k) ≤ L) :
    realNormalizer w events i₀ N ≤
      realNormalizer w events i₀ E * Real.exp ((w - 1) * L) := by
  have hf (k : ℕ) : 0 ≤ 1 + (w - 1) * birthReciprocal events i₀ k := by
    have := mul_nonneg (sub_nonneg.mpr hw) (birthReciprocal_nonneg events i₀ k)
    linarith
  have hproduct : (∏ k ∈ Finset.Ico E N, (1 + (w - 1) * birthReciprocal events i₀ k)) ≤
      Real.exp ((w - 1) * L) := by
    calc
      _ ≤ ∏ k ∈ Finset.Ico E N, Real.exp ((w - 1) * birthReciprocal events i₀ k) := by
        apply Finset.prod_le_prod₀ (fun k _ ↦ hf k)
        intro k _
        simpa only [add_comm] using Real.add_one_le_exp ((w - 1) * birthReciprocal events i₀ k)
      _ = Real.exp ((w - 1) * ∑ k ∈ Finset.Ico E N, birthReciprocal events i₀ k) := by
        rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htail (sub_nonneg.mpr hw))
  unfold realNormalizer
  rw [← Finset.prod_range_mul_prod_Ico _ hEN]
  exact mul_le_mul_of_nonneg_left hproduct (Finset.prod_nonneg fun k _ ↦ hf k)

/-- Bounded late reciprocal mass changes only the multiplicative constants. -/
theorem realNormalizer_polynomial_extension {w A B a α β L : ℝ}
    (hw : 1 ≤ w) (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (events : ℕ → Bool) (i₀ : ℕ) {E N : ℕ} (hEN : E ≤ N)
    (hscale : a * (N : ℝ) ≤ E)
    (hlower : A * (E : ℝ) ^ α ≤ realNormalizer w events i₀ E)
    (hupper : realNormalizer w events i₀ E ≤ B * (E : ℝ) ^ β)
    (htail : (∑ k ∈ Finset.Ico E N, birthReciprocal events i₀ k) ≤ L) :
    (A * a ^ α) * (N : ℝ) ^ α ≤ realNormalizer w events i₀ N ∧
      realNormalizer w events i₀ N ≤ (B * Real.exp ((w - 1) * L)) * (N : ℝ) ^ β := by
  constructor
  · calc
      _ = A * (a * (N : ℝ)) ^ α := by rw [Real.mul_rpow ha.le (Nat.cast_nonneg N)]; ring
      _ ≤ A * (E : ℝ) ^ α :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hscale hα) hA
      _ ≤ realNormalizer w events i₀ E := hlower
      _ ≤ _ := realNormalizer_mono hw events i₀ hEN
  · calc
      _ ≤ realNormalizer w events i₀ E * Real.exp ((w - 1) * L) :=
        realNormalizer_le_mul_exp_tail hw events i₀ hEN htail
      _ ≤ (B * (E : ℝ) ^ β) * Real.exp ((w - 1) * L) :=
        mul_le_mul_of_nonneg_right hupper (Real.exp_nonneg _)
      _ ≤ (B * (N : ℝ) ^ β) * Real.exp ((w - 1) * L) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg E) (by exact_mod_cast hEN) hβ) hB
      _ = _ := by ring

end HeightPaper.Model
