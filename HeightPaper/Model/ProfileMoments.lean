module

public import HeightPaper.Model.NormalizedProfile
public import Mathlib.Analysis.MeanInequalities

/-!
# Finite moment estimates for the profile martingale

Jensen's bound is proved for the actual normalized active profile. Centered
one-step formulas identify the profile martingale increment at a prescribed
infection or recovery. No asymptotic estimate is assumed in these identities.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace HeightPaper.Model

/-- Real-valued integration over the actual finite uniform parent law. -/
theorem uniformActive_integral_real (s : State) (h : s.active.Nonempty)
    (f : Fin s.vertices → ℝ) :
    (∫ v, f v ∂(uniformActive s h).toMeasure) =
      (∑ v ∈ s.active, f v) / (infectious s : ℝ) := by
  rw [PMF.integral_eq_sum]
  simp only [uniformActive_apply]
  simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_zero, ite_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.smul_sum]
  simp [infectious, div_eq_mul_inv, mul_comm]

theorem finite_average_norm_rpow_le {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → ℂ) {p : ℝ} (hp : 1 ≤ p) :
    ‖(∑ v ∈ s, f v) / (s.card : ℂ)‖ ^ p ≤
      (∑ v ∈ s, ‖f v‖ ^ p) / (s.card : ℝ) := by
  have hi : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have hip : 0 < (s.card : ℝ) ^ p := Real.rpow_pos_of_pos hi p
  have hj := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s
    (f := fun v ↦ ‖f v‖) hp (fun v _ ↦ norm_nonneg (f v))
  have hb : ‖∑ v ∈ s, f v‖ ^ p ≤
      (s.card : ℝ) ^ (p - 1) * ∑ v ∈ s, ‖f v‖ ^ p :=
    (Real.rpow_le_rpow (norm_nonneg _) (norm_sum_le _ _) (zero_le_one.trans hp)).trans hj
  rw [norm_div, Complex.norm_natCast, Real.div_rpow (norm_nonneg _) hi.le]
  calc
    _ ≤ ((s.card : ℝ) ^ (p - 1) * ∑ v ∈ s, ‖f v‖ ^ p) / (s.card : ℝ) ^ p :=
      div_le_div_of_nonneg_right hb hip.le
    _ = _ := by
      rw [Real.rpow_sub hi, Real.rpow_one]
      field_simp

/-- The Jensen estimate in the paper's profile moment argument, before
averaging over any epidemic history or imposing growth asymptotics. -/
theorem norm_normalizedActiveWeight_rpow_le (w : ℂ) (s : State)
    (h : s.active.Nonempty) {p : ℝ} (hp : 1 ≤ p) :
    ‖normalizedActiveWeight w s‖ ^ p ≤
      activeWeight (‖w‖ ^ p) s / (infectious s : ℝ) := by
  have he := finite_average_norm_rpow_le s.active h
    (fun v ↦ w ^ s.tree.depth v) hp
  simpa only [normalizedActiveWeight, activeWeight, infectious, norm_pow,
    ← Real.rpow_pow_comm (norm_nonneg w)] using he

theorem norm_normalizedLaplace_rpow_le (z : ℂ) (s : State)
    (h : s.active.Nonempty) {p : ℝ} (hp : 1 ≤ p) :
    ‖normalizedActiveWeight (Complex.exp z) s‖ ^ p ≤
      activeWeight (Real.exp (p * z.re)) s / (infectious s : ℝ) := by
  simpa only [Complex.norm_exp, ← Real.exp_mul, mul_comm z.re p] using
    norm_normalizedActiveWeight_rpow_le (Complex.exp z) s h hp

/-- The elementary two-term moment inequality, used with the centered profile
draw. It holds for every exponent at least one. -/
theorem norm_sub_rpow_le (a b : ℂ) {p : ℝ} (hp : 1 ≤ p) :
    ‖a - b‖ ^ p ≤ (2 : ℝ) ^ (p - 1) * (‖a‖ ^ p + ‖b‖ ^ p) := by
  have hsum : (‖a‖ + ‖b‖) ^ p ≤ (2 : ℝ) ^ (p - 1) * (‖a‖ ^ p + ‖b‖ ^ p) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ‖a‖₊ ‖b‖₊ hp
  exact (Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le a b) (zero_le_one.trans hp)).trans hsum

/-- A centered active-parent draw has its p-th moment bounded by twice the
Jensen moment, with the explicit power-of-two constant. -/
theorem uniform_centered_profile_moment_le (w : ℂ) (s : State)
    (h : s.active.Nonempty) {p : ℝ} (hp : 1 ≤ p) :
    (∫ v, ‖w ^ s.tree.depth v - normalizedActiveWeight w s‖ ^ p
      ∂(uniformActive s h).toMeasure) ≤
      (2 : ℝ) ^ p * (activeWeight (‖w‖ ^ p) s / (infectious s : ℝ)) := by
  have hi : 0 < (infectious s : ℝ) := by exact_mod_cast h.card_pos
  rw [uniformActive_integral_real]
  have hs : (∑ v ∈ s.active, ‖w ^ s.tree.depth v - normalizedActiveWeight w s‖ ^ p) ≤
      (2 : ℝ) ^ (p - 1) * (activeWeight (‖w‖ ^ p) s +
        (infectious s : ℝ) * ‖normalizedActiveWeight w s‖ ^ p) := by
    calc
      _ ≤ ∑ v ∈ s.active, (2 : ℝ) ^ (p - 1) *
          (‖w ^ s.tree.depth v‖ ^ p + ‖normalizedActiveWeight w s‖ ^ p) :=
        Finset.sum_le_sum fun v _ ↦ norm_sub_rpow_le _ _ hp
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        simp only [norm_pow, ← Real.rpow_pow_comm (norm_nonneg w),
          Finset.sum_const, nsmul_eq_mul, infectious, activeWeight]
  have hj := (le_div_iff₀ hi).mp (norm_normalizedActiveWeight_rpow_le w s h hp)
  have hnonneg : 0 ≤ (2 : ℝ) ^ (p - 1) := Real.rpow_nonneg (by norm_num) _
  have hb := hs.trans (mul_le_mul_of_nonneg_left
    (show activeWeight (‖w‖ ^ p) s + (infectious s : ℝ) *
      ‖normalizedActiveWeight w s‖ ^ p ≤ 2 * activeWeight (‖w‖ ^ p) s by nlinarith) hnonneg)
  have heq : (2 : ℝ) ^ (p - 1) * 2 = (2 : ℝ) ^ p := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring
  exact (div_le_div_of_nonneg_right hb hi.le).trans_eq (by rw [← mul_assoc, heq]; ring)

/-- Exact centered increment for a prescribed infection after updating the
product normalizer. The denominator is nonzero precisely in the usable regime. -/
theorem normalized_infect_centered_increment (w C : ℂ) (s : State)
    (h : s.active.Nonempty) (v : Fin s.vertices)
    (hC : C ≠ 0) (hIw : (infectious s : ℂ) + w ≠ 0) :
    normalizedActiveWeight w (infect s v) /
        (C * (1 + (w - 1) / ((infectious s : ℂ) + 1))) -
      normalizedActiveWeight w s / C =
        w * (w ^ s.tree.depth v - normalizedActiveWeight w s) /
          (C * ((infectious s : ℂ) + w)) := by
  have hi : (infectious s : ℂ) ≠ 0 := by exact_mod_cast h.card_pos.ne'
  have hip : (infectious s : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (infectious s)
  have hwI : w + (infectious s : ℂ) ≠ 0 := by simpa only [add_comm] using hIw
  have hf : 1 + (w - 1) / ((infectious s : ℂ) + 1) ≠ 0 := by
    have heq : 1 + (w - 1) / ((infectious s : ℂ) + 1) =
        ((infectious s : ℂ) + w) / ((infectious s : ℂ) + 1) := by field_simp; ring
    rw [heq]
    exact div_ne_zero hIw hip
  simp only [normalizedActiveWeight, activeWeight_infect, infectious_infect,
    Nat.cast_add, Nat.cast_one]
  field_simp [hC, hi, hip, hIw, hwI, hf]
  ring

/-- Exact centered increment for a prescribed recovery. Extinction is excluded
because the normalized active profile would then have denominator zero. -/
theorem normalized_recover_centered_increment (w C : ℂ) (s : State)
    (v : Fin s.vertices) (hv : v ∈ s.active) (hI : 1 < infectious s) (hC : C ≠ 0) :
    normalizedActiveWeight w (recover s v) / C - normalizedActiveWeight w s / C =
      -(w ^ s.tree.depth v - normalizedActiveWeight w s) /
        (C * ((infectious s : ℂ) - 1)) := by
  have hi : (infectious s : ℂ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hI).ne'
  have him : (infectious s : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hI.ne')
  simp only [normalizedActiveWeight, activeWeight_recover w hv, infectious_recover hv,
    Nat.cast_sub (Nat.one_le_of_lt hI), Nat.cast_one]
  field_simp
  ring

/-- Multiplying a centered parent draw by a deterministic complex coefficient
scales its moment by the p-th power of that coefficient's norm. -/
theorem uniform_scaled_centered_profile_moment_le (a w : ℂ) (s : State)
    (h : s.active.Nonempty) {p : ℝ} (hp : 1 ≤ p) :
    (∫ v, ‖a * (w ^ s.tree.depth v - normalizedActiveWeight w s)‖ ^ p
      ∂(uniformActive s h).toMeasure) ≤
      ‖a‖ ^ p * ((2 : ℝ) ^ p *
        (activeWeight (‖w‖ ^ p) s / (infectious s : ℝ))) := by
  simp_rw [norm_mul, Real.mul_rpow (norm_nonneg a) (norm_nonneg _)]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (uniform_centered_profile_moment_le w s h hp)
    (Real.rpow_nonneg (norm_nonneg a) p)

/-- A genuine p-th moment estimate for the one-step martingale increment at
a prescribed infection, under the uniform active-parent probability measure. -/
theorem uniform_infect_martingale_increment_moment_le (w C : ℂ) (s : State)
    (h : s.active.Nonempty) {p : ℝ} (hp : 1 ≤ p)
    (hC : C ≠ 0) (hIw : (infectious s : ℂ) + w ≠ 0) :
    (∫ v, ‖normalizedActiveWeight w (infect s v) /
        (C * (1 + (w - 1) / ((infectious s : ℂ) + 1))) -
        normalizedActiveWeight w s / C‖ ^ p ∂(uniformActive s h).toMeasure) ≤
      ‖w / (C * ((infectious s : ℂ) + w))‖ ^ p * ((2 : ℝ) ^ p *
        (activeWeight (‖w‖ ^ p) s / (infectious s : ℝ))) := by
  simp_rw [normalized_infect_centered_increment w C s h _ hC hIw,
    mul_div_right_comm w]
  exact uniform_scaled_centered_profile_moment_le _ w s h hp

/-- The recovery increment satisfies the analogous moment estimate before
extinction. Only active vertices occur under the sampling law. -/
theorem uniform_recover_martingale_increment_moment_le (w C : ℂ) (s : State)
    (h : s.active.Nonempty) {p : ℝ} (hp : 1 ≤ p)
    (hI : 1 < infectious s) (hC : C ≠ 0) :
    (∫ v, ‖normalizedActiveWeight w (recover s v) / C -
      normalizedActiveWeight w s / C‖ ^ p ∂(uniformActive s h).toMeasure) ≤
      ‖-1 / (C * ((infectious s : ℂ) - 1))‖ ^ p * ((2 : ℝ) ^ p *
        (activeWeight (‖w‖ ^ p) s / (infectious s : ℝ))) := by
  have heq : (∫ v, ‖normalizedActiveWeight w (recover s v) / C -
      normalizedActiveWeight w s / C‖ ^ p ∂(uniformActive s h).toMeasure) =
      ∫ v, ‖(-1 / (C * ((infectious s : ℂ) - 1))) *
        (w ^ s.tree.depth v - normalizedActiveWeight w s)‖ ^ p
        ∂(uniformActive s h).toMeasure := by
    rw [uniformActive_integral_real, uniformActive_integral_real]
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    rw [normalized_recover_centered_increment w C s v hv hI hC]
    congr 2
    ring
  rw [heq]
  exact uniform_scaled_centered_profile_moment_le _ w s h hp

end HeightPaper.Model
