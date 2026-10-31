module

public import HeightPaper.Model.CountCoupling
public import Mathlib.Analysis.PSeries

/-!
# Comparing the birth-weighted reciprocal sums of the coupled walks

This is the deterministic summation-by-parts step in the finite-population
reciprocal estimate. All bounds retain their constants uniformly in the prefix.
-/

@[expose] public section

open scoped BigOperators

namespace HeightPaper.CountCoupling

noncomputable def birthReciprocalSum (S : ℕ → ℝ) (birth : ℕ → Bool) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (if birth i then (1 : ℝ) else 0) / S (i + 1)

theorem sum_succ_reciprocal_square_le_two (k : ℕ) :
    (∑ i ∈ Finset.range k, 1 / ((i + 1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
  have he : (∑ i ∈ Finset.range k, 1 / ((i + 1 : ℕ) : ℝ) ^ 2) =
      ∑ j ∈ Finset.Ioo 0 (k + 1), ((j : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_bij (fun i _ ↦ i + 1)
    · intro i hi
      simp only [Finset.mem_range] at hi
      exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
    · intro i hi j hj hij
      omega
    · intro j hj
      have hj' := Finset.mem_Ioo.mp hj
      exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro i _
      simp [one_div]
  rw [he]
  simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 (k + 1)

/-- Abel summation with a nonsingular boundary term, valid also at zero. -/
theorem sum_difference_div_succ (D : ℕ → ℝ) (hD : D 0 = 0) (k : ℕ) :
    (∑ i ∈ Finset.range k, (D (i + 1) - D i) / (i + 1 : ℕ)) =
      D k / (k + 1 : ℕ) +
        ∑ i ∈ Finset.range k, D (i + 1) / ((i + 1 : ℕ) * (i + 2 : ℕ) : ℕ) := by
  induction k with
  | zero => simp [hD]
  | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      push_cast
      have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring

theorem gap_div_succ_pair_le {D C : ℝ} (hC : 0 ≤ C) {n j : ℕ}
    (hn : 0 < n) (hj : 0 < j) (hD : D ≤ C * (1 + (j : ℝ) ^ 2 / n)) :
    D / ((j : ℝ) * (j + 1)) ≤ C * (1 / (j : ℝ) ^ 2 + 1 / n) := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (C * (1 + (j : ℝ) ^ 2 / n)) / ((j : ℝ) * (j + 1)) :=
      div_le_div_of_nonneg_right hD (by positivity)
    _ ≤ (C * (1 + (j : ℝ) ^ 2 / n)) / (j : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hjR)
      nlinarith
    _ = _ := by field_simp

/-- A quadratic count-gap envelope controls its harmonic increments. -/
theorem sum_gap_difference_div_le (D : ℕ → ℝ) (hD0 : D 0 = 0)
    {C : ℝ} (hC : 0 ≤ C) {n k : ℕ} (hn : 0 < n)
    (hD : ∀ j ≤ k, D j ≤ C * (1 + (j : ℝ) ^ 2 / n)) :
    (∑ i ∈ Finset.range k, (D (i + 1) - D i) / (i + 1 : ℕ)) ≤
      C * (3 + 2 * (k : ℝ) / n) := by
  rw [sum_difference_div_succ D hD0]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hend : D k / (k + 1 : ℕ) ≤ C * (1 + (k : ℝ) / n) := by
    calc
      _ ≤ (C * (1 + (k : ℝ) ^ 2 / n)) / (k + 1 : ℕ) :=
        div_le_div_of_nonneg_right (hD k le_rfl) (by positivity)
      _ ≤ _ := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k + 1 : ℕ))).mpr
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have he : (1 + (k : ℝ) / n) * (k + 1) - (1 + (k : ℝ) ^ 2 / n) =
            (k : ℝ) + k / n := by ring
        push_cast
        have hh : 1 + (k : ℝ) ^ 2 / n ≤ (1 + (k : ℝ) / n) * (k + 1) := by
          linarith [div_nonneg hk0 hnR.le]
        have hh' := mul_le_mul_of_nonneg_left hh hC
        nlinarith
  have hsum : (∑ i ∈ Finset.range k,
      D (i + 1) / ((i + 1 : ℕ) * (i + 2 : ℕ) : ℕ)) ≤ C * (2 + (k : ℝ) / n) := by
    calc
      _ ≤ ∑ i ∈ Finset.range k, C * (1 / ((i + 1 : ℕ) : ℝ) ^ 2 + 1 / n) := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := gap_div_succ_pair_le hC hn (Nat.zero_lt_succ i)
          (hD (i + 1) (by have := Finset.mem_range.mp hi; omega))
        convert hh using 1
        push_cast
        ring
      _ = C * ((∑ i ∈ Finset.range k, 1 / ((i + 1 : ℕ) : ℝ) ^ 2) + k / n) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [sum_succ_reciprocal_square_le_two k]) hC
  exact (add_le_add hend hsum).trans_eq (by ring)

/-- Pointwise comparison of the reciprocal denominators. -/
theorem reciprocal_difference_le {s sn j n M Mn C : ℝ}
    (hsn : 0 < sn) (hss : sn ≤ s) (hj : 0 < j) (hn : 0 < n)
    (hM : 0 ≤ M) (hMn : 0 ≤ Mn) (_hC : 0 ≤ C)
    (hMs : j / s ≤ M) (hMns : j / sn ≤ Mn)
    (hD : s - sn ≤ C * (1 + j ^ 2 / n)) :
    0 ≤ 1 / sn - 1 / s ∧ 1 / sn - 1 / s ≤ M * Mn * C * (1 / j ^ 2 + 1 / n) := by
  have hs := hsn.trans_le hss
  refine ⟨sub_nonneg.mpr (one_div_le_one_div_of_le hsn hss), ?_⟩
  have he : 1 / sn - 1 / s = (j / s) * (j / sn) * ((s - sn) / j ^ 2) := by
    field_simp
  rw [he]
  have hm := mul_le_mul hMs hMns (by positivity : 0 ≤ j / sn) hM
  calc
    _ ≤ (M * Mn) * ((s - sn) / j ^ 2) :=
      mul_le_mul_of_nonneg_right hm (div_nonneg (sub_nonneg.mpr hss) (sq_nonneg j))
    _ ≤ (M * Mn) * (C * (1 + j ^ 2 / n) / j ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hD (sq_nonneg j))
        (mul_nonneg hM hMn)
    _ = _ := by field_simp

/-- The finite and local birth-reciprocal sums differ by a bounded quantity
on full finite survival. Every prefix uses the same four envelope constants. -/
theorem birthReciprocalSum_difference_le {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : 0 < n)
    (u : ℕ → ℝ) (H : ℕ) {M Mn C T : ℝ}
    (hM : 0 ≤ M) (hMn : 0 ≤ Mn) (hC : 0 ≤ C) (_hT : 0 ≤ T)
    (hpos : ∀ j ≤ H, 0 < (finiteWalk l n u j : ℝ))
    (hlocal : ∀ j ≤ H, (j : ℝ) / localWalk l u j ≤ M)
    (hfinite : ∀ j ≤ H, (j : ℝ) / finiteWalk l n u j ≤ Mn)
    (hgap : ∀ j ≤ H, (localWalk l u j : ℝ) - finiteWalk l n u j ≤
      C * (1 + (j : ℝ) ^ 2 / n))
    (hHT : (H : ℝ) / n ≤ T) {k : ℕ} (hk : k ≤ H) :
    |birthReciprocalSum (fun j ↦ (finiteWalk l n u j : ℝ)) (finiteBirth l n u) k -
      birthReciprocalSum (fun j ↦ (localWalk l u j : ℝ)) (localBirth l u) k| ≤
      M * (Mn + 1) * C * (2 + T) := by
  let S : ℕ → ℝ := fun j ↦ localWalk l u j
  let Sn : ℕ → ℝ := fun j ↦ finiteWalk l n u j
  let D : ℕ → ℝ := fun j ↦ S j - Sn j
  let B : ℕ → ℝ := fun i ↦ if localBirth l u i then 1 else 0
  let Bn : ℕ → ℝ := fun i ↦ if finiteBirth l n u i then 1 else 0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkn : (k : ℝ) / n ≤ T :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hk) hnR.le).trans hHT
  have horder (j : ℕ) : Sn j ≤ S j :=
    Int.cast_le.mpr (walk_sandwich hl hn u j).2
  have hbirth (i : ℕ) : 0 ≤ Bn i ∧ Bn i ≤ B i ∧ B i ≤ 1 := by
    have h := finiteBirth_implies_local hl hn u i
    dsimp [B, Bn]
    cases hf : finiteBirth l n u i <;> cases hb : localBirth l u i <;> simp_all
  have hstep (i : ℕ) : D (i + 1) - D i = 2 * (B i - Bn i) := by
    dsimp [D, S, Sn]
    simp only [localWalk, finiteWalk, Finset.sum_range_succ, Int.cast_add, Int.cast_one]
    dsimp [B, Bn]
    cases localBirth l u i <;> cases finiteBirth l n u i <;> simp <;> ring
  have hden (i : ℕ) (hi : i < k) :
      0 ≤ 1 / Sn (i + 1) - 1 / S (i + 1) ∧
      1 / Sn (i + 1) - 1 / S (i + 1) ≤
        M * Mn * C * (1 / ((i + 1 : ℕ) : ℝ) ^ 2 + 1 / n) := by
    have hiH : i + 1 ≤ H := by omega
    exact reciprocal_difference_le (hpos (i + 1) hiH) (horder (i + 1))
      (by positivity) hnR hM hMn hC (hlocal (i + 1) hiH)
      (hfinite (i + 1) hiH) (hgap (i + 1) hiH)
  have hsingle (i : ℕ) (hi : i < k) :
      |Bn i / Sn (i + 1) - B i / S (i + 1)| ≤
        (1 / Sn (i + 1) - 1 / S (i + 1)) + M * ((B i - Bn i) / (i + 1 : ℕ)) := by
    have hiH : i + 1 ≤ H := by omega
    have hsn := hpos (i + 1) hiH
    have hs : 0 < S (i + 1) := hsn.trans_le (horder (i + 1))
    have hj : (0 : ℝ) < (i + 1 : ℕ) := by positivity
    have hb := hbirth i
    have hdiff : 0 ≤ B i - Bn i := sub_nonneg.mpr hb.2.1
    have hrec : 1 / S (i + 1) ≤ M / (i + 1 : ℕ) := by
      apply (le_div_iff₀ hj).mpr
      simpa only [S, one_div, div_eq_mul_inv, one_mul, mul_comm] using hlocal (i + 1) hiH
    have hw : (B i - Bn i) / S (i + 1) ≤ M * ((B i - Bn i) / (i + 1 : ℕ)) := by
      have hh := mul_le_mul_of_nonneg_left hrec hdiff
      convert hh using 1 <;> ring
    have hbn : Bn i * (1 / Sn (i + 1) - 1 / S (i + 1)) ≤
        1 / Sn (i + 1) - 1 / S (i + 1) := by
      exact (mul_le_mul_of_nonneg_right (hb.2.1.trans hb.2.2) (hden i hi).1).trans_eq (one_mul _)
    have he : Bn i / Sn (i + 1) - B i / S (i + 1) =
        Bn i * (1 / Sn (i + 1) - 1 / S (i + 1)) - (B i - Bn i) / S (i + 1) := by ring
    rw [he, abs_le]
    have hd0 := (hden i hi).1
    have hbden := mul_nonneg hb.1 hd0
    have hwd := div_nonneg hdiff hs.le
    constructor <;> linarith
  have hdsum : (∑ i ∈ Finset.range k, (1 / Sn (i + 1) - 1 / S (i + 1))) ≤
      M * Mn * C * (2 + T) := by
    calc
      _ ≤ ∑ i ∈ Finset.range k,
          M * Mn * C * (1 / ((i + 1 : ℕ) : ℝ) ^ 2 + 1 / n) :=
        Finset.sum_le_sum (fun i hi ↦ (hden i (Finset.mem_range.mp hi)).2)
      _ = M * Mn * C *
          ((∑ i ∈ Finset.range k, 1 / ((i + 1 : ℕ) : ℝ) ^ 2) + k / n) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by linarith [sum_succ_reciprocal_square_le_two k]) (by positivity)
  have hbsum : (∑ i ∈ Finset.range k, (B i - Bn i) / (i + 1 : ℕ)) ≤ C * (2 + T) := by
    have hD0 : D 0 = 0 := by simp [D, S, Sn, localWalk]
    have hh := sum_gap_difference_div_le D hD0 hC hn
      (fun j hj ↦ hgap j (hj.trans hk))
    have he : (∑ i ∈ Finset.range k, (D (i + 1) - D i) / (i + 1 : ℕ)) =
        2 * ∑ i ∈ Finset.range k, (B i - Bn i) / (i + 1 : ℕ) := by
      simp_rw [hstep]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he] at hh
    have ht := mul_le_mul_of_nonneg_left hkn hC
    have hh' : 2 * (∑ i ∈ Finset.range k, (B i - Bn i) / (i + 1 : ℕ)) ≤
        3 * C + 2 * (C * ((k : ℝ) / n)) := by
      convert hh using 1
      ring
    nlinarith only [hh', ht, hC]
  change |(∑ i ∈ Finset.range k, Bn i / Sn (i + 1)) -
      ∑ i ∈ Finset.range k, B i / S (i + 1)| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range k, |Bn i / Sn (i + 1) - B i / S (i + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range k,
        ((1 / Sn (i + 1) - 1 / S (i + 1)) + M * ((B i - Bn i) / (i + 1 : ℕ))) :=
      Finset.sum_le_sum (fun i hi ↦ hsingle i (Finset.mem_range.mp hi))
    _ = (∑ i ∈ Finset.range k, (1 / Sn (i + 1) - 1 / S (i + 1))) +
        M * ∑ i ∈ Finset.range k, (B i - Bn i) / (i + 1 : ℕ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ M * Mn * C * (2 + T) + M * (C * (2 + T)) :=
      add_le_add hdsum (mul_le_mul_of_nonneg_left hbsum hM)
    _ = _ := by ring

end HeightPaper.CountCoupling
