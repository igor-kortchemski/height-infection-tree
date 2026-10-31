module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.PSeries

/-! # A power-sum bound uniform through the critical exponent -/

@[expose] public section

open scoped BigOperators

namespace HeightPaper

/-- A harmonic majorant keeps the bound uniform when the power crosses `-1`.
The logarithmic factor is retained at the critical exponent. -/
theorem sum_exp_log_Ico_le (a R : ℝ) (j k : ℕ) :
    (∑ i ∈ Finset.Ico j k, Real.exp (a * Real.log (i + 1 : ℕ) + R)) ≤
      Real.exp R * (1 + Real.log k) * Real.exp (max (a + 1) 0 * Real.log k) := by
  let B := Real.exp (max (a + 1) 0 * Real.log k)
  have hpoint (i : ℕ) (hi : i < k) :
      Real.exp (a * Real.log (i + 1 : ℕ) + R) ≤ Real.exp R * B * ((i + 1 : ℕ) : ℝ)⁻¹ := by
    have ht : (0 : ℝ) < (i + 1 : ℕ) := by positivity
    have hlog0 : 0 ≤ Real.log (i + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i))
    have hlog : Real.log (i + 1 : ℕ) ≤ Real.log k :=
      Real.log_le_log ht (by exact_mod_cast (Nat.succ_le_iff.mpr hi))
    have hab : (a + 1) * Real.log (i + 1 : ℕ) ≤ max (a + 1) 0 * Real.log k :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0).trans
        (mul_le_mul_of_nonneg_left hlog (le_max_right _ _))
    calc
      _ ≤ Real.exp (R + (max (a + 1) 0 * Real.log k - Real.log (i + 1 : ℕ))) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = _ := by rw [Real.exp_add, Real.exp_sub, Real.exp_log ht]; dsimp [B]; ring
  have hsum : (∑ i ∈ Finset.Ico j k, Real.exp (a * Real.log (i + 1 : ℕ) + R)) ≤
      Real.exp R * B * (harmonic k : ℝ) := by
    calc
      _ ≤ ∑ i ∈ Finset.range k, Real.exp (a * Real.log (i + 1 : ℕ) + R) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun i hi ↦ Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2)
          (fun i _ _ ↦ (Real.exp_pos _).le)
      _ ≤ ∑ i ∈ Finset.range k, Real.exp R * B * ((i + 1 : ℕ) : ℝ)⁻¹ :=
        Finset.sum_le_sum (fun i hi ↦ hpoint i (Finset.mem_range.mp hi))
      _ = _ := by simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]
  calc
    _ ≤ Real.exp R * B * (1 + Real.log k) :=
      hsum.trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log k) (by positivity))
    _ = _ := by dsimp [B]; ring

/-- Below the critical exponent, the exponential logarithmic power sum is
bounded independently of the terminal time. -/
theorem sum_exp_log_Ico_le_of_strict_decay {a η : ℝ}
    (hη : 0 < η) (ha : a ≤ -1 - η) (R : ℝ) (j k : ℕ) :
    (∑ i ∈ Finset.Ico j k,
      Real.exp (a * Real.log (i + 1 : ℕ) + R)) ≤
      Real.exp R * ∑' i : ℕ, ((i + 1 : ℕ) : ℝ) ^ (-1 - η) := by
  have hs : Summable (fun i : ℕ => ((i + 1 : ℕ) : ℝ) ^ (-1 - η)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun i : ℕ => (i : ℝ) ^ (-1 - η)) 1).mpr
        (Real.summable_nat_rpow.mpr (by linarith))
  have hterm (i : ℕ) :
      Real.exp (a * Real.log (i + 1 : ℕ) + R) ≤
        Real.exp R * ((i + 1 : ℕ) : ℝ) ^ (-1 - η) := by
    have hm : (0 : ℝ) < (i + 1 : ℕ) := by positivity
    have hlog : 0 ≤ Real.log (i + 1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i))
    rw [Real.rpow_def_of_pos hm, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left ha hlog
    linarith
  calc
    _ ≤ ∑ i ∈ Finset.Ico j k,
        Real.exp R * ((i + 1 : ℕ) : ℝ) ^ (-1 - η) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = Real.exp R * ∑ i ∈ Finset.Ico j k,
        ((i + 1 : ℕ) : ℝ) ^ (-1 - η) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (by positivity) _))
      (Real.exp_pos _).le

/-- On a doubled interval every term is within a fixed factor of the first
power, uniformly through positive and negative exponents. -/
theorem sum_rpow_Ico_double_le (a : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (∑ i ∈ Finset.Ico k (2 * k), ((i + 1 : ℕ) : ℝ) ^ a) ≤
      (k : ℝ) * max 1 ((2 : ℝ) ^ a) * (k : ℝ) ^ a := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hterm (i : ℕ) (hi : i ∈ Finset.Ico k (2 * k)) :
      ((i + 1 : ℕ) : ℝ) ^ a ≤ max 1 ((2 : ℝ) ^ a) * (k : ℝ) ^ a := by
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hi
    have hlo' : (k : ℝ) ≤ (i + 1 : ℕ) := by exact_mod_cast (by omega : k ≤ i + 1)
    have hhi' : ((i + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
      exact_mod_cast (by omega : i + 1 ≤ 2 * k)
    by_cases ha : 0 ≤ a
    · calc
        _ ≤ (2 * (k : ℝ)) ^ a := Real.rpow_le_rpow (by positivity) hhi' ha
        _ = (2 : ℝ) ^ a * (k : ℝ) ^ a := Real.mul_rpow (by norm_num) hkpos.le
        _ ≤ max 1 ((2 : ℝ) ^ a) * (k : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hkpos.le _)
    · have ha' : a ≤ 0 := le_of_not_ge ha
      calc
        _ ≤ (k : ℝ) ^ a := Real.rpow_le_rpow_of_nonpos hkpos hlo' ha'
        _ = 1 * (k : ℝ) ^ a := by ring
        _ ≤ max 1 ((2 : ℝ) ^ a) * (k : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hkpos.le _)
  calc
    _ ≤ ∑ _i ∈ Finset.Ico k (2 * k), max 1 ((2 : ℝ) ^ a) * (k : ℝ) ^ a :=
      Finset.sum_le_sum hterm
    _ = (k : ℝ) * max 1 ((2 : ℝ) ^ a) * (k : ℝ) ^ a := by
      have hsub : 2 * k - k = k := by omega
      simp [hsub, mul_assoc]

end HeightPaper
