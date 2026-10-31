module

public import HeightPaper.Model.CountNormalizerBounds
public import HeightPaper.Model.NormalizerExtension

/-! # Uniform product estimates through a macroscopic terminal time -/

public section

open scoped BigOperators

namespace HeightPaper.Model

/-- Early linear count barriers and a bounded later reciprocal sum give
absolute polynomial bounds at every prefix after a fixed starting index. -/
theorem exists_global_normalizer_constants {lo hi w a L : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi) (hw : 1 ≤ w) (ha : 0 < a)
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (events : ℕ → Bool) (E N : ℕ), K ≤ E → E ≤ N →
      a * (N : ℝ) ≤ E →
      (∀ k ≤ N, 0 < prescribedWalk events 1 k) →
      (∀ k ∈ Finset.Icc K E, lo * k ≤ (prescribedWalk events 1 k : ℝ)) →
      (∀ k ∈ Finset.Icc K E, (prescribedWalk events 1 k : ℝ) ≤ hi * k) →
      (∑ k ∈ Finset.Ico E N, 1 / (prescribedWalk events 1 k : ℝ)) ≤ L →
      ∀ k ∈ Finset.Icc K N,
        A * (k : ℝ) ^ ((w - 1) * ((1 + 1 / hi) / 2)) ≤ realNormalizer w events 1 k ∧
        realNormalizer w events 1 k ≤ B * (k : ℝ) ^ ((w - 1) * ((1 + 1 / lo) / 2)) := by
  obtain ⟨A, B, hA, hB, hbase⟩ := exists_count_normalizer_constants hlo hhi hw K hK
  let α := (w - 1) * ((1 + 1 / hi) / 2)
  let β := (w - 1) * ((1 + 1 / lo) / 2)
  let A' := min A (A * a ^ α)
  let B' := max B (B * Real.exp ((w - 1) * L))
  have hα : 0 ≤ α := mul_nonneg (sub_nonneg.mpr hw) (by positivity)
  have hβ : 0 ≤ β := mul_nonneg (sub_nonneg.mpr hw) (by positivity)
  refine ⟨A', B', lt_min hA (mul_pos hA (Real.rpow_pos_of_pos ha _)),
    hB.trans_le (le_max_left _ _), ?_⟩
  intro events E N hKE hEN hscale hpos hlow hupp htail k hk
  have hkK := (Finset.mem_Icc.mp hk).1
  have hkN := (Finset.mem_Icc.mp hk).2
  by_cases hkE : k ≤ E
  · have hb := hbase events k hkK (fun i hi ↦ hpos i (hi.trans hkN))
      (fun i hi ↦ hlow i (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans hkE⟩))
      (fun i hi ↦ hupp i (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans hkE⟩))
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg k) _)).trans hb.1,
      hb.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg k) _))⟩
  · have hEk : E ≤ k := by omega
    have hb := hbase events E hKE (fun i hi ↦ hpos i (hi.trans hEN)) hlow hupp
    have hpartial : (∑ i ∈ Finset.Ico E k, birthReciprocal events 1 i) ≤ L := by
      calc
        _ ≤ ∑ i ∈ Finset.Ico E k, 1 / (prescribedWalk events 1 i : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          exact birthReciprocal_le_count_inv events 1 i
            (hpos i ((Finset.mem_Ico.mp hi).2.le.trans hkN))
        _ ≤ ∑ i ∈ Finset.Ico E N, 1 / (prescribedWalk events 1 i : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hi).1, (Finset.mem_Ico.mp hi).2.trans_le hkN⟩
          · intro i _ _
            positivity
        _ ≤ L := htail
    have hscaleK : a * (k : ℝ) ≤ E :=
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hkN) ha.le).trans hscale
    have he := realNormalizer_polynomial_extension hw hA.le hB.le ha hα hβ events 1
      hEk hscaleK hb.1 hb.2 hpartial
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg k) _)).trans he.1,
      he.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg k) _))⟩

end HeightPaper.Model
