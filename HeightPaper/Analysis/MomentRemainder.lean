module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Scalar moment remainders

The real profile route needs p-th moments with `1 < p ≤ 2`. The estimates here
control the nonlinear remainder after subtracting the linear term, which then
vanishes under a zero-mean martingale increment.
-/

@[expose] public section

open Set

namespace HeightPaper

theorem abs_rpow_sub_le {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) : |a ^ q - b ^ q| ≤ |a - b| ^ q := by
  wlog hab : b ≤ a generalizing a b
  · simpa only [abs_sub_comm] using this hb ha (le_of_not_ge hab)
  have hr := Real.rpow_add_le_add_rpow hb (sub_nonneg.mpr hab) hq hq1
  have hm := Real.rpow_le_rpow hb hab hq
  rw [add_sub_cancel] at hr
  rw [abs_of_nonneg (sub_nonneg.mpr hm), abs_of_nonneg (sub_nonneg.mpr hab)]
  linarith

/-- Taylor's first-order remainder on the nonnegative half-line, with an
explicit p-th-power bound and no unproved smoothness assumption. -/
theorem abs_rpow_remainder_le {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 1 < p) (hp2 : p ≤ 2) :
    |b ^ p - a ^ p - p * a ^ (p - 1) * (b - a)| ≤ p * |b - a| ^ p := by
  let g : ℝ → ℝ := fun t ↦ t ^ p - p * a ^ (p - 1) * t
  have hd (t : ℝ) : HasDerivAt g (p * (t ^ (p - 1) - a ^ (p - 1))) t := by
    convert (Real.hasDerivAt_rpow_const (Or.inr hp.le)).sub
      ((hasDerivAt_id t).const_mul (p * a ^ (p - 1))) using 1 <;> first | rfl | ring
  have hbound (t : ℝ) (ht : t ∈ Icc (min a b) (max a b)) :
      ‖p * (t ^ (p - 1) - a ^ (p - 1))‖ ≤ p * |b - a| ^ (p - 1) := by
    have ht0 : 0 ≤ t := (le_min ha hb).trans ht.1
    have hdist : |t - a| ≤ |b - a| := by
      rcases le_total a b with hab | hba
      · rw [min_eq_left hab, max_eq_right hab] at ht
        rw [abs_of_nonneg (sub_nonneg.mpr ht.1), abs_of_nonneg (sub_nonneg.mpr hab)]
        linarith [ht.2]
      · rw [min_eq_right hba, max_eq_left hba] at ht
        rw [abs_of_nonpos (sub_nonpos.mpr ht.2), abs_of_nonpos (sub_nonpos.mpr hba)]
        linarith [ht.1]
    have hh := (abs_rpow_sub_le ht0 ha (by linarith : 0 ≤ p - 1)
      (by linarith : p - 1 ≤ 1)).trans
      (Real.rpow_le_rpow (abs_nonneg _) hdist (by linarith))
    simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one hp)] using
      mul_le_mul_of_nonneg_left hh (le_trans zero_le_one hp.le)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ ↦ (hd t).hasDerivWithinAt) hbound (convex_Icc (min a b) (max a b))
    (show a ∈ Icc (min a b) (max a b) from ⟨min_le_left _ _, le_max_left _ _⟩)
    (show b ∈ Icc (min a b) (max a b) from ⟨min_le_right _ _, le_max_right _ _⟩)
  have heq : g b - g a = b ^ p - a ^ p - p * a ^ (p - 1) * (b - a) := by
    dsimp [g]
    ring
  rw [heq, Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hpow : |b - a| ^ (p - 1) * |b - a| = |b - a| ^ p := by
    rw [← Real.rpow_add_one' (abs_nonneg _) (by linarith : p - 1 + 1 ≠ 0)]
    congr 1
    ring
  simpa only [mul_assoc, hpow] using h

private theorem crossing_rpow_remainder_le {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 1 < p) (hp2 : p ≤ 2) :
    b ^ p - a ^ p + p * a ^ (p - 1) * (a + b) ≤ 4 * (a + b) ^ p := by
  have hs : 0 ≤ a + b := add_nonneg ha hb
  have hbpow := Real.rpow_le_rpow hb (le_add_of_nonneg_left ha) (zero_le_one.trans hp.le)
  have hapow := Real.rpow_le_rpow ha (le_add_of_nonneg_right hb)
    (sub_nonneg.mpr hp.le)
  have hmul : p * a ^ (p - 1) * (a + b) ≤ p * (a + b) ^ p := by
    calc
      _ ≤ p * (a + b) ^ (p - 1) * (a + b) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hapow
          (zero_le_one.trans hp.le)) hs
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add_one' hs (by linarith : p - 1 + 1 ≠ 0)]
        congr 2
        ring
  have ha0 := Real.rpow_nonneg ha p
  have hs0 := Real.rpow_nonneg hs p
  nlinarith

/-- The coefficient of the linear part of the real absolute p-th moment. -/
noncomputable def momentSlope (p a : ℝ) : ℝ :=
  if 0 ≤ a then p * a ^ (p - 1) else -p * (-a) ^ (p - 1)

/-- A scalar martingale moment inequality. The linear term vanishes after
conditional expectation. The universal constant four suffices for the full
range `1 < p ≤ 2`, including increments crossing zero. -/
theorem abs_rpow_le_linear_add_remainder {a b p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    |b| ^ p ≤ |a| ^ p + momentSlope p a * (b - a) + 4 * |b - a| ^ p := by
  by_cases ha : 0 ≤ a
  · rw [momentSlope, ite_eq_left ha, abs_of_nonneg ha]
    by_cases hb : 0 ≤ b
    · rw [abs_of_nonneg hb]
      have hh := (le_abs_self (b ^ p - a ^ p - p * a ^ (p - 1) * (b - a))).trans
        (abs_rpow_remainder_le ha hb hp hp2)
      have hd := Real.rpow_nonneg (abs_nonneg (b - a)) p
      nlinarith
    · have hb0 : b < 0 := lt_of_not_ge hb
      rw [abs_of_neg hb0, abs_of_nonpos (by linarith : b - a ≤ 0)]
      have hh := crossing_rpow_remainder_le ha (neg_nonneg.mpr hb0.le) hp hp2
      have heq : -(b - a) = a + -b := by ring
      rw [heq]
      nlinarith
  · have ha0 : a < 0 := lt_of_not_ge ha
    rw [momentSlope, ite_eq_right ha, abs_of_neg ha0]
    by_cases hb : 0 ≤ b
    · rw [abs_of_nonneg hb, abs_of_nonneg (by linarith : 0 ≤ b - a)]
      have hh := crossing_rpow_remainder_le (neg_nonneg.mpr ha0.le) hb hp hp2
      have heq : b - a = -a + b := by ring
      rw [heq]
      nlinarith
    · have hb0 : b < 0 := lt_of_not_ge hb
      rw [abs_of_neg hb0]
      have hh := (le_abs_self ((-b) ^ p - (-a) ^ p -
        p * (-a) ^ (p - 1) * ((-b) - (-a)))).trans
        (abs_rpow_remainder_le (neg_nonneg.mpr ha0.le) (neg_nonneg.mpr hb0.le) hp hp2)
      have heq : |(-b) - (-a)| = |b - a| := by rw [neg_sub_neg, abs_sub_comm]
      rw [heq] at hh
      have hd := Real.rpow_nonneg (abs_nonneg (b - a)) p
      nlinarith

end HeightPaper
