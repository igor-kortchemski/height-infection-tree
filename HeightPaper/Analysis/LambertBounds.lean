module

public import HeightPaper.Analysis.Critical
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The two Lambert bounds in the appendix

The principal negative branch is specified by its range and inverse equation,
so the statements include the branch point without introducing a total Lambert
function. The first estimate uses the manuscript's inverse-exponential
comparison. The second follows from the stronger elementary reciprocal bound;
it does not certify the manuscript's Taylor-polynomial argument.
-/

public section

noncomputable section

open Set

namespace HeightPaper

/-- Existence and uniqueness of the principal negative Lambert inverse on its
whole real interval, including both endpoints. -/
theorem existsUnique_principalLambert_negative {x : ℝ}
    (hx : x ∈ Icc (-(1 / Real.exp 1)) 0) :
    ∃! w : ℝ, w ∈ Icc (-1) 0 ∧ w * Real.exp w = x := by
  have hrange : -x ∈ Icc (meanEquation 0) (meanEquation 1) := by
    simp only [meanEquation, neg_zero, Real.exp_zero, zero_mul, one_mul,
      Real.exp_neg, ← one_div]
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨m, hm, heq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    continuous_meanEquation.continuousOn hrange
  have hw : -m ∈ Icc (-1 : ℝ) 0 := by constructor <;> linarith [hm.1, hm.2]
  have hwx : -m * Real.exp (-m) = x := by
    dsimp [meanEquation] at heq
    linarith
  refine ⟨-m, ⟨hw, hwx⟩, ?_⟩
  intro w h
  exact principalLambert_negative_unique h.1 hw (h.2.trans hwx.symm)

private def lambertAux (u : ℝ) : ℝ :=
  1 + Real.exp (u - u ^ 2 / 3) * (-1 + u - 2 * u ^ 2 / 9)

private theorem hasDerivAt_lambertAux (u : ℝ) :
    HasDerivAt lambertAux
      (Real.exp (u - u ^ 2 / 3) * (u * (4 * u ^ 2 - 24 * u + 33) / 27)) u := by
  have hv := (hasDerivAt_id u).sub (((hasDerivAt_id u).pow 2).div_const 3)
  have hp := (((hasDerivAt_id u).const_add (-1)).sub
    ((((hasDerivAt_id u).pow 2).const_mul 2).div_const 9))
  convert (hv.exp.mul hp).const_add 1 using 1
  · rfl
  · dsimp
    ring

private theorem lambertAux_nonneg {u : ℝ} (hu : u ∈ Icc 0 (3 / 2 : ℝ)) :
    0 ≤ lambertAux u := by
  have hm : MonotoneOn lambertAux (Icc 0 (3 / 2 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_lambertAux x).continuousAt).continuousOn
    · intro x _
      exact (hasDerivAt_lambertAux x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc, mem_Ioo] at hx
      rw [(hasDerivAt_lambertAux x).deriv]
      apply mul_nonneg (Real.exp_pos _).le
      apply div_nonneg _ (by norm_num)
      apply mul_nonneg hx.1.le
      nlinarith [sq_nonneg (2 * x - 3)]
  have h := hm (by norm_num) hu hu.1
  simpa [lambertAux] using h

private def lambertComparison (u : ℝ) : ℝ :=
  u ^ 2 / 2 - 1 - (-1 + u - u ^ 2 / 3) * Real.exp (u - u ^ 2 / 3)

private theorem hasDerivAt_lambertComparison (u : ℝ) :
    HasDerivAt lambertComparison (u * lambertAux u) u := by
  have hv := (hasDerivAt_id u).sub (((hasDerivAt_id u).pow 2).div_const 3)
  convert ((((hasDerivAt_id u).pow 2).div_const 2).sub_const 1).sub
    ((hv.const_add (-1)).mul hv.exp) using 1
  · funext x
    dsimp [lambertComparison]
    ring
  · dsimp [lambertAux]
    ring

/-- The inverse-exponential comparison used in the proof of `lem:Lambert` (i).
Only the interval needed by the source bound is required. -/
theorem lambert_inverse_comparison {u : ℝ} (hu : u ∈ Icc 0 (3 / 2 : ℝ)) :
    (-1 + u - u ^ 2 / 3) * Real.exp (u - u ^ 2 / 3) ≤ u ^ 2 / 2 - 1 := by
  have hm : MonotoneOn lambertComparison (Icc 0 (3 / 2 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr fun x ↦
        (hasDerivAt_lambertComparison x).continuousAt).continuousOn
    · intro x _
      exact (hasDerivAt_lambertComparison x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc, mem_Ioo] at hx
      rw [(hasDerivAt_lambertComparison x).deriv]
      exact mul_nonneg hx.1.le (lambertAux_nonneg ⟨hx.1.le, hx.2.le⟩)
  have h := hm (by norm_num) hu hu.1
  simp only [lambertComparison, zero_pow (by norm_num : 2 ≠ 0), zero_div,
    sub_zero, Real.exp_zero, mul_one] at h
  linarith

/-- The first appendix bound, in a form with the square roots combined. The
range and inverse equation specify the principal Lambert value exactly. -/
theorem principalLambert_lower_bound_normalized {x w : ℝ}
    (hx : x ∈ Icc (-(1 / Real.exp 1)) 0) (hw : w ∈ Icc (-1) 0)
    (heq : w * Real.exp w = x) :
    -1 + Real.sqrt (2 * (Real.exp 1 * x + 1)) -
      (2 / 3 : ℝ) * (Real.exp 1 * x + 1) ≤ w := by
  have he : 0 < Real.exp (1 : ℝ) := Real.exp_pos _
  have hy : 0 ≤ Real.exp 1 * x + 1 := by
    have h := (div_le_iff₀ he).mp (show -1 / Real.exp 1 ≤ x by simpa only [neg_div] using hx.1)
    nlinarith
  have hy1 : Real.exp 1 * x + 1 ≤ 1 := by nlinarith [hx.2]
  let u := Real.sqrt (2 * (Real.exp 1 * x + 1))
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = 2 * (Real.exp 1 * x + 1) := Real.sq_sqrt (by positivity)
  have hu : u ≤ (3 / 2 : ℝ) := by nlinarith
  let b := -1 + u - u ^ 2 / 3
  have hb : b ∈ Icc (-1 : ℝ) 0 := by
    dsimp only [b]
    constructor
    · nlinarith [mul_nonneg hu0 (show 0 ≤ 3 - u by linarith)]
    · nlinarith [sq_nonneg (u - 3 / 2)]
  have hcomp := lambert_inverse_comparison ⟨hu0, hu⟩
  have hexp : Real.exp (u - u ^ 2 / 3) = Real.exp b * Real.exp 1 := by
    rw [← Real.exp_add]
    congr 1
    dsimp [b]
    ring
  rw [hexp] at hcomp
  have hbx : b * Real.exp b ≤ x := by
    apply (mul_le_mul_iff_right₀ he).mp
    dsimp only [b] at *
    nlinarith [hu2]
  have hbw : b ≤ w := by
    by_contra! h
    have hmean := meanEquation_strictMonoOn
      (show -b ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hb.1, hb.2])
      (show -w ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hw.1, hw.2])
      (by linarith : -b < -w)
    simp only [meanEquation, neg_neg] at hmean
    nlinarith
  dsimp only [b] at hbw
  dsimp only [u] at hu2 hbw
  nlinarith

/-- `lem:Lambert` (i), with exactly the two square roots printed in the paper. -/
theorem principalLambert_lower_bound {x w : ℝ}
    (hx : x ∈ Icc (-(1 / Real.exp 1)) 0) (hw : w ∈ Icc (-1) 0)
    (heq : w * Real.exp w = x) :
    -1 + Real.sqrt (2 * Real.exp 1) * Real.sqrt (x + 1 / Real.exp 1) -
      (2 / 3 : ℝ) * Real.exp 1 * (x + 1 / Real.exp 1) ≤ w := by
  have hscale : Real.exp 1 * (x + 1 / Real.exp 1) = Real.exp 1 * x + 1 := by
    field_simp [(Real.exp_pos (1 : ℝ)).ne']
  have hsqrt : Real.sqrt (2 * Real.exp 1) * Real.sqrt (x + 1 / Real.exp 1) =
      Real.sqrt (2 * (Real.exp 1 * x + 1)) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.exp (1 : ℝ))]
    congr 1
    nlinarith [hscale]
  rw [hsqrt, mul_assoc, hscale]
  exact principalLambert_lower_bound_normalized hx hw heq

/-- The elementary logarithmic inequality underlying a stronger bound than
`lem:Lambert` (ii). -/
theorem two_mul_log_le_sub_inv {l : ℝ} (hl : 1 ≤ l) :
    2 * Real.log l ≤ l - 1 / l := by
  let F : ℝ → ℝ := fun x ↦ x - 1 / x - 2 * Real.log x
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt F ((x - 1) ^ 2 / x ^ 2) x := by
    have h := ((hasDerivAt_id x).sub
      ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx.ne')).sub
      ((Real.hasDerivAt_log hx.ne').const_mul 2)
    convert h using 1
    · rfl
    · simp only [id_eq]
      field_simp
      ring
  have hm : MonotoneOn F (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro x hx
      exact (hd x (lt_of_lt_of_le zero_lt_one hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici, mem_Ioi] at hx
      exact (hd x (by linarith)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici, mem_Ioi] at hx
      rw [(hd x (by linarith)).deriv]
      positivity
  have h := hm (by simp) hl hl
  simp only [F, Real.log_one, mul_zero, div_one, sub_self] at h
  linarith

/-- Reflection about one increases the offspring inverse equation when the
reflection is taken by reciprocation. -/
theorem meanEquation_le_meanEquation_inv {l : ℝ} (hl : 1 ≤ l) :
    meanEquation l ≤ meanEquation (1 / l) := by
  have hl0 : 0 < l := lt_of_lt_of_le zero_lt_one hl
  apply (Real.log_le_log_iff (mul_pos hl0 (Real.exp_pos _))
    (mul_pos (one_div_pos.mpr hl0) (Real.exp_pos _))).mp
  simp only [Real.log_mul hl0.ne' (Real.exp_pos _).ne',
    Real.log_mul (one_div_pos.mpr hl0).ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_div one_ne_zero hl0.ne', Real.log_one]
  linarith [two_mul_log_le_sub_inv hl]

/-- A stronger elementary estimate for the principal value at `-l exp(-l)`.
The branch-point case `l = 1` is included. -/
theorem principalLambert_parameter_lower_bound_inv {l w : ℝ} (hl : 1 ≤ l)
    (hw : w ∈ Icc (-1) 0)
    (heq : w * Real.exp w = -l * Real.exp (-l)) :
    -(1 / l) ≤ w := by
  have hl0 : 0 < l := lt_of_lt_of_le zero_lt_one hl
  have hinv : 1 / l ∈ Icc (0 : ℝ) 1 :=
    ⟨(one_div_pos.mpr hl0).le, (div_le_one hl0).mpr hl⟩
  by_contra! h
  have hm := meanEquation_strictMonoOn hinv
    (show -w ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hw.1, hw.2])
    (by linarith : 1 / l < -w)
  have hi := meanEquation_le_meanEquation_inv hl
  simp only [meanEquation, neg_neg] at hm hi
  nlinarith

/-- The paper's square-root bound is weaker than the reciprocal bound. -/
theorem lambert_parameter_bound_le_neg_inv {l : ℝ} (hl : 1 ≤ l) :
    (l - 1) * Real.sqrt (2 - 2 * l + l ^ 2) - 2 + 2 * l - l ^ 2 ≤ -(1 / l) := by
  let h := l - 1
  let r := Real.sqrt (1 + h ^ 2)
  have hh : 0 ≤ h := sub_nonneg.mpr hl
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 1 + h ^ 2 := Real.sq_sqrt (by positivity)
  have hr1 : 1 ≤ r := by nlinarith
  have hrh : 0 < r + h := by linarith
  have hsum : 0 < 1 + h := by positivity
  have hid : 1 + h ^ 2 - h * r = r / (r + h) := by
    apply (eq_div_iff hrh.ne').mpr
    calc
      (1 + h ^ 2 - h * r) * (r + h) = r * (r ^ 2 - h ^ 2) := by
        rw [← hr2]
        ring
      _ = r := by rw [hr2]; ring
  have hb : 1 / (1 + h) ≤ 1 + h ^ 2 - h * r := by
    rw [hid]
    apply (div_le_div_iff₀ hsum hrh).mpr
    nlinarith [mul_nonneg hh (sub_nonneg.mpr hr1)]
  have hsqrt : Real.sqrt (2 - 2 * l + l ^ 2) = r := by
    dsimp only [r, h]
    congr 1
    ring
  rw [hsqrt]
  have hden : 1 + h = l := by dsimp [h]; ring
  rw [hden] at hb
  dsimp only [h] at hb
  nlinarith

/-- `lem:Lambert` (ii), including `l = 1`, in the exact principal-root encoding. -/
theorem principalLambert_parameter_lower_bound {l w : ℝ} (hl : 1 ≤ l)
    (hw : w ∈ Icc (-1) 0)
    (heq : w * Real.exp w = -l * Real.exp (-l)) :
    (l - 1) * Real.sqrt (2 - 2 * l + l ^ 2) - 2 + 2 * l - l ^ 2 ≤ w :=
  (lambert_parameter_bound_le_neg_inv hl).trans
    (principalLambert_parameter_lower_bound_inv hl hw heq)

/-- Specialization of the stronger bound to the project's offspring mean. -/
theorem offspringMean_le_inv {l : ℝ} (hl : 1 < l) : offspringMean l ≤ 1 / l := by
  have h := offspringMean_principal_lambert hl
  have hb := principalLambert_parameter_lower_bound_inv hl.le ⟨h.1.1.le, h.1.2.le⟩ h.2
  linarith

/-- The lower bound used by the paper's convexity argument for the critical
parameter, specialized to the formal offspring mean. -/
theorem offspringMean_lambert_parameter_lower_bound {l : ℝ} (hl : 1 < l) :
    (l - 1) * Real.sqrt (2 - 2 * l + l ^ 2) - 2 + 2 * l - l ^ 2 ≤
      -offspringMean l := by
  have h := offspringMean_principal_lambert hl
  exact principalLambert_parameter_lower_bound hl.le ⟨h.1.1.le, h.1.2.le⟩ h.2

/-- The polynomial sign used in the appendix's displayed second derivative
of the reciprocal offspring mean. -/
theorem offspringMean_reciprocal_curvature_numerator_nonneg {l : ℝ} (hl : 1 < l) :
    0 ≤ (-offspringMean l + 2 - 2 * l + l ^ 2) ^ 2 -
      (l - 1) ^ 2 * (2 - 2 * l + l ^ 2) := by
  have hD : 0 ≤ 2 - 2 * l + l ^ 2 := by nlinarith [sq_nonneg (l - 1)]
  have hs := Real.sq_sqrt hD
  have hb := offspringMean_lambert_parameter_lower_bound hl
  have hleft : 0 ≤ (l - 1) * Real.sqrt (2 - 2 * l + l ^ 2) := by positivity
  have hbound : (l - 1) * Real.sqrt (2 - 2 * l + l ^ 2) ≤
      -offspringMean l + 2 - 2 * l + l ^ 2 := by linarith
  have hsq := mul_self_le_mul_self hleft hbound
  apply sub_nonneg.mpr
  simpa only [← pow_two, mul_pow, hs] using hsq

end HeightPaper
