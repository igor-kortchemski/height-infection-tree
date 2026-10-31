module

public import HeightPaper.Analysis.LambertBounds
public import HeightPaper.Analysis.ParameterContinuity
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Topology.Order.LeftRight

/-!
# The paper's Lambert route to the critical parameter

Implicit differentiation of the two defining inverse equations gives the
appendix's curvature formulas. The Lambert estimate supplies the sign needed
for the reciprocal offspring mean. Boundary continuity, strict convexity, a
negative value, and the positive-infinity limit give an independent proof of
existence, uniqueness, and crossing orientation. A negative value at 5/4 replaces
the manuscript's near-one asymptotic calculation. The inherited exports and
their original alternative proofs are unchanged.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace HeightPaper

/-- Implicit differentiation of the offspring inverse equation. -/
theorem hasDerivAt_offspringMean {l : ℝ} (hl : 1 < l) :
    HasDerivAt offspringMean
      (offspringMean l * (1 - l) / (l * (1 - offspringMean l))) l := by
  have hl0 : l ≠ 0 := (lt_trans zero_lt_one hl).ne'
  have hm : 1 - offspringMean l ≠ 0 := (sub_pos.mpr (offspringMean_lt_one hl)).ne'
  have hd := HasDerivAt.of_comp_left (continuousAt_offspringMean hl)
    (hasDerivAt_meanEquation (offspringMean l)) (hasDerivAt_meanEquation l)
    (mul_ne_zero hm (Real.exp_pos _).ne')
    (show meanEquation ∘ offspringMean =ᶠ[𝓝 l] meanEquation by
      filter_upwards [eventually_gt_nhds hl] with x hx
      exact (offspringMean_spec hx).2)
  convert hd using 1
  have heq := (offspringMean_spec hl).2
  dsimp only [meanEquation] at heq
  field_simp [hl0, hm, (Real.exp_pos (-offspringMean l)).ne']
  have heq' := congrArg (fun t : ℝ ↦ t * (1 - l)) heq
  nlinarith

/-- Implicit differentiation of the profile-root inverse equation. -/
theorem hasDerivAt_profileRoot {l : ℝ} (hl : 1 < l) :
    HasDerivAt profileRoot ((1 - profileRoot l) / (l * profileRoot l)) l := by
  have hl0 : l ≠ 0 := (lt_trans zero_lt_one hl).ne'
  have hz : profileRoot l ≠ 0 := (profileRoot_pos hl).ne'
  have hf (z : ℝ) : HasDerivAt (fun x : ℝ ↦ (1 - x) * Real.exp x)
      (-z * Real.exp z) z := by
    convert ((hasDerivAt_id z).const_sub 1).mul (Real.hasDerivAt_exp z) using 1
    · rfl
    · dsimp
      ring
  have hd := HasDerivAt.of_comp_left (continuousAt_profileRoot hl)
    (hf (profileRoot l)) ((hasDerivAt_const l (1 : ℝ)).div (hasDerivAt_id l) hl0)
    (mul_ne_zero (neg_ne_zero.mpr hz) (Real.exp_pos _).ne')
    (show (fun x : ℝ ↦ (1 - x) * Real.exp x) ∘ profileRoot =ᶠ[𝓝 l]
        (fun x : ℝ ↦ 1 / x) by
      filter_upwards [eventually_gt_nhds hl] with x hx
      exact profileRoot_equation hx)
  convert hd using 1
  have heq := (eq_div_iff hl0).mp (profileRoot_equation hl)
  dsimp
  field_simp [hl0, hz, (Real.exp_pos (profileRoot l)).ne']
  have heq' := congrArg (fun t : ℝ ↦ t * l) heq
  nlinarith

/-- First derivative of the first term in the appendix's critical gap. -/
theorem hasDerivAt_reciprocal_offspringMean {l : ℝ} (hl : 1 < l) :
    HasDerivAt (fun x ↦ 1 / offspringMean x)
      ((l - 1) / (l * offspringMean l * (1 - offspringMean l))) l := by
  convert (hasDerivAt_const l (1 : ℝ)).div
    (hasDerivAt_offspringMean hl) (offspringMean_pos hl).ne' using 1
  field_simp [(lt_trans zero_lt_one hl).ne', (offspringMean_pos hl).ne',
    (sub_pos.mpr (offspringMean_lt_one hl)).ne']
  ring

/-- First derivative of the second term in the appendix's critical gap. -/
theorem hasDerivAt_neg_exp_profileRoot {l : ℝ} (hl : 1 < l) :
    HasDerivAt (fun x ↦ -Real.exp (profileRoot x))
      (-(1 / (l ^ 2 * profileRoot l))) l := by
  convert (hasDerivAt_profileRoot hl).exp.neg using 1
  have heq := (eq_div_iff (lt_trans zero_lt_one hl).ne').mp (profileRoot_equation hl)
  field_simp [(lt_trans zero_lt_one hl).ne', (profileRoot_pos hl).ne']
  nlinarith

/-- Rational form of the first curvature formula in the appendix. Its
numerator is exactly the polynomial controlled by `lem:Lambert` (ii). -/
theorem hasDerivAt_reciprocal_offspringMean_slope {l : ℝ} (hl : 1 < l) :
    HasDerivAt
      (fun x ↦ (x - 1) / (x * offspringMean x * (1 - offspringMean x)))
      (((-offspringMean l + 2 - 2 * l + l ^ 2) ^ 2 -
          (l - 1) ^ 2 * (2 - 2 * l + l ^ 2)) /
        (l ^ 2 * offspringMean l * (1 - offspringMean l) ^ 3)) l := by
  have hd := ((hasDerivAt_id l).sub_const 1).div
    (((hasDerivAt_id l).mul (hasDerivAt_offspringMean hl)).mul
      ((hasDerivAt_offspringMean hl).const_sub 1))
    (mul_ne_zero (mul_ne_zero (lt_trans zero_lt_one hl).ne' (offspringMean_pos hl).ne')
      (sub_pos.mpr (offspringMean_lt_one hl)).ne')
  convert hd using 1
  · rfl
  · dsimp
    field_simp [(lt_trans zero_lt_one hl).ne', (offspringMean_pos hl).ne',
      (sub_pos.mpr (offspringMean_lt_one hl)).ne']
    ring

/-- The other curvature formula in the appendix, expressed using the profile
root rather than its Lambert value minus one. -/
theorem hasDerivAt_neg_exp_profileRoot_slope {l : ℝ} (hl : 1 < l) :
    HasDerivAt (fun x ↦ -(1 / (x ^ 2 * profileRoot x)))
      ((2 * (profileRoot l) ^ 2 - profileRoot l + 1) /
        (l ^ 3 * (profileRoot l) ^ 3)) l := by
  have hd := ((hasDerivAt_const l (1 : ℝ)).div
    (((hasDerivAt_id l).pow 2).mul (hasDerivAt_profileRoot hl))
    (mul_ne_zero (pow_ne_zero _ (lt_trans zero_lt_one hl).ne') (profileRoot_pos hl).ne')).neg
  convert hd using 1
  · rfl
  · dsimp
    field_simp [(lt_trans zero_lt_one hl).ne', (profileRoot_pos hl).ne']
    ring

/-- The Lambert bound proves convexity of the reciprocal offspring mean,
which is the substantive use of that bound in the paper's appendix. -/
theorem convexOn_reciprocal_offspringMean :
    ConvexOn ℝ (Ioi 1) (fun l ↦ 1 / offspringMean l) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 1)
    (f' := fun l ↦ (l - 1) / (l * offspringMean l * (1 - offspringMean l)))
    (f'' := fun l ↦ ((-offspringMean l + 2 - 2 * l + l ^ 2) ^ 2 -
      (l - 1) ^ 2 * (2 - 2 * l + l ^ 2)) /
      (l ^ 2 * offspringMean l * (1 - offspringMean l) ^ 3))
  · intro l hl
    exact (hasDerivAt_reciprocal_offspringMean hl).continuousAt.continuousWithinAt
  · intro l hl
    rw [interior_Ioi, mem_Ioi] at hl
    exact (hasDerivAt_reciprocal_offspringMean hl).hasDerivWithinAt
  · intro l hl
    rw [interior_Ioi, mem_Ioi] at hl
    exact (hasDerivAt_reciprocal_offspringMean_slope hl).hasDerivWithinAt
  · intro l hl
    rw [interior_Ioi, mem_Ioi] at hl
    apply div_nonneg (offspringMean_reciprocal_curvature_numerator_nonneg hl)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (offspringMean_pos hl).le)
      (pow_nonneg (sub_pos.mpr (offspringMean_lt_one hl)).le _)

/-- Convexity of the other summand in the paper's critical gap. -/
theorem convexOn_neg_exp_profileRoot :
    ConvexOn ℝ (Ioi 1) (fun l ↦ -Real.exp (profileRoot l)) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 1)
    (f' := fun l ↦ -(1 / (l ^ 2 * profileRoot l)))
    (f'' := fun l ↦ (2 * (profileRoot l) ^ 2 - profileRoot l + 1) /
      (l ^ 3 * (profileRoot l) ^ 3))
  · intro l hl
    exact (hasDerivAt_neg_exp_profileRoot hl).continuousAt.continuousWithinAt
  · intro l hl
    rw [interior_Ioi, mem_Ioi] at hl
    exact (hasDerivAt_neg_exp_profileRoot hl).hasDerivWithinAt
  · intro l hl
    rw [interior_Ioi, mem_Ioi] at hl
    exact (hasDerivAt_neg_exp_profileRoot_slope hl).hasDerivWithinAt
  · intro l hl
    rw [interior_Ioi, mem_Ioi] at hl
    apply div_nonneg
    · nlinarith [sq_nonneg (2 * profileRoot l - 1)]
    · exact mul_nonneg (pow_nonneg (lt_trans zero_lt_one hl).le _)
        (pow_nonneg (profileRoot_pos hl).le _)

/-- The convexity step of the manuscript's proof of `prop:lc` (i). -/
theorem convexOn_lambert_critical_gap :
    ConvexOn ℝ (Ioi 1) (fun l ↦ 1 / offspringMean l - Real.exp (profileRoot l)) := by
  simpa only [Pi.add_def, sub_eq_add_neg] using
    convexOn_reciprocal_offspringMean.add convexOn_neg_exp_profileRoot

/-- A lower bound which verifies the paper's positive-infinity endpoint. -/
theorem lambert_critical_gap_lower_bound {l : ℝ} (hl : 1 < l) :
    l - Real.exp 1 ≤ 1 / offspringMean l - Real.exp (profileRoot l) := by
  have hml := (le_div_iff₀ (lt_trans zero_lt_one hl)).mp (offspringMean_le_inv hl)
  have hli : l ≤ 1 / offspringMean l := by
    apply (le_div_iff₀ (offspringMean_pos hl)).mpr
    nlinarith
  have he := Real.exp_le_exp.mpr (profileRoot_lt_one hl).le
  linarith

/-- The positive-infinity limit used by the appendix's critical-parameter proof. -/
theorem tendsto_lambert_critical_gap_atTop :
    Tendsto (fun l ↦ 1 / offspringMean l - Real.exp (profileRoot l)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_ge_atTop (b + Real.exp 1)] with l hl hbl
  linarith [lambert_critical_gap_lower_bound hl]

/-- Symmetric displacement from the maximum of the offspring inverse equation
favours the supercritical side. -/
theorem meanEquation_reflection_le {h : ℝ} (hh : 0 ≤ h) :
    meanEquation (1 - h) ≤ meanEquation (1 + h) := by
  let F : ℝ → ℝ := fun x ↦ meanEquation (1 + x) - meanEquation (1 - x)
  have hd (x : ℝ) : HasDerivAt F
      (x * (Real.exp (-(1 - x)) - Real.exp (-(1 + x)))) x := by
    convert ((hasDerivAt_meanEquation (1 + x)).comp x
      ((hasDerivAt_id x).const_add 1)).sub
      ((hasDerivAt_meanEquation (1 - x)).comp x
        ((hasDerivAt_id x).const_sub 1)) using 1
    · rfl
    · ring
  have hm : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
      (continuous_iff_continuousAt.mpr fun x ↦ (hd x).continuousAt).continuousOn
    · intro x _
      exact (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici, mem_Ioi] at hx
      rw [(hd x).deriv]
      apply mul_nonneg hx.le
      apply sub_nonneg.mpr
      exact Real.exp_le_exp.mpr (by linarith)
  have h := hm (by simp) hh hh
  dsimp only [F] at h
  simp only [add_zero, sub_zero, sub_self] at h
  exact sub_nonneg.mp h

/-- A simple lower estimate for the offspring mean, also valid near the
critical branching point. -/
theorem two_sub_parameter_le_offspringMean {l : ℝ} (hl : 1 < l) :
    2 - l ≤ offspringMean l := by
  by_cases hlow : 2 - l ≤ 0
  · exact hlow.trans (offspringMean_pos hl).le
  have hc : meanEquation (2 - l) ≤ meanEquation l := by
    convert meanEquation_reflection_le (show 0 ≤ l - 1 by linarith) using 1 <;>
      congr 1 <;> ring
  by_contra! h
  have hm := meanEquation_strictMonoOn
    ⟨(offspringMean_pos hl).le, (offspringMean_lt_one hl).le⟩
    (show 2 - l ∈ Icc (0 : ℝ) 1 by constructor <;> linarith) h
  rw [(offspringMean_spec hl).2] at hm
  exact (not_lt_of_ge hc) hm

/-- Application of `lem:Lambert` (i) to the paper's profile root. -/
theorem profileRoot_lambert_lower_bound {l : ℝ} (hl : 1 < l) :
    Real.sqrt (2 * (1 - 1 / l)) - (2 / 3 : ℝ) * (1 - 1 / l) ≤ profileRoot l := by
  have he : 0 < Real.exp (1 : ℝ) := Real.exp_pos _
  have hl0 : 0 < l := lt_trans zero_lt_one hl
  have hx : -(1 / (Real.exp 1 * l)) ∈ Icc (-(1 / Real.exp 1)) 0 := by
    constructor
    · apply neg_le_neg
      exact one_div_le_one_div_of_le he (by nlinarith)
    · exact neg_nonpos.mpr (one_div_nonneg.mpr (mul_pos he hl0).le)
  have hp := profileRoot_principal_lambert hl
  have h := principalLambert_lower_bound_normalized hx ⟨hp.1.1.le, hp.1.2.le⟩ hp.2
  have hid : Real.exp 1 * -(1 / (Real.exp 1 * l)) + 1 = 1 - 1 / l := by
    field_simp [he.ne', hl0.ne']
    ring
  rw [hid] at h
  linarith

/-- An explicit negative value of the appendix's gap. The proof uses the
first Lambert bound, avoiding an unformalized asymptotic expansion at one. -/
theorem lambert_critical_gap_neg_at_five_fourths :
    1 / offspringMean (5 / 4) - Real.exp (profileRoot (5 / 4)) < 0 := by
  have hl : (1 : ℝ) < 5 / 4 := by norm_num
  have hm : (3 / 4 : ℝ) ≤ offspringMean (5 / 4) := by
    have h := two_sub_parameter_le_offspringMean hl
    linarith
  have hi : 1 / offspringMean (5 / 4) ≤ (4 / 3 : ℝ) := by
    apply (div_le_iff₀ (offspringMean_pos hl)).mpr
    linarith
  have hz : Real.sqrt (2 / 5 : ℝ) - 2 / 15 ≤ profileRoot (5 / 4) := by
    convert profileRoot_lambert_lower_bound hl using 1
    norm_num
  have hz' : (1 / 3 : ℝ) < profileRoot (5 / 4) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 / 5),
      Real.sqrt_nonneg (2 / 5 : ℝ)]
  have he := Real.add_one_le_exp (profileRoot (5 / 4))
  linarith

/-- Existence of a critical parameter by the Lambert-bound route. This proof
uses the negative value and positive endpoint established above, independently
of the inherited construction through `criticalEquation`. -/
theorem exists_criticalParameter_from_lambert :
    ∃ l : ℝ, 1 < l ∧ offspringMean l = Real.exp (-profileRoot l) := by
  let F : ℝ → ℝ := fun l ↦ 1 / offspringMean l - Real.exp (profileRoot l)
  let b : ℝ := Real.exp 1 + 1
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  have hab : (5 / 4 : ℝ) ≤ b := by dsimp [b]; linarith
  have hb : 1 < b := by dsimp [b]; linarith
  have hF : ContinuousOn F (Icc (5 / 4) b) := by
    intro l hl
    have hl1 : 1 < l := by linarith [hl.1]
    exact ((hasDerivAt_reciprocal_offspringMean hl1).add
      (hasDerivAt_neg_exp_profileRoot hl1)).continuousAt.continuousWithinAt
  have hleft : F (5 / 4) ≤ 0 := lambert_critical_gap_neg_at_five_fourths.le
  have hright : 0 ≤ F b := by
    have h := lambert_critical_gap_lower_bound hb
    dsimp only [F, b] at *
    linarith
  obtain ⟨l, hl, hFl⟩ := intermediate_value_Icc hab hF ⟨hleft, hright⟩
  have hl1 : 1 < l := by linarith [hl.1]
  refine ⟨l, hl1, ?_⟩
  have hg : 1 / offspringMean l = Real.exp (profileRoot l) := by
    dsimp only [F] at hFl
    linarith
  have hmul := (div_eq_iff (offspringMean_pos hl1).ne').mp hg
  rw [Real.exp_neg, ← one_div]
  apply (eq_div_iff (Real.exp_pos _).ne').mpr
  nlinarith

/-- A quadratic upper bound for the inverse profile equation near its maximum. -/
theorem profile_inverse_equation_le_quadratic {z : ℝ} (hz : 0 ≤ z) :
    (1 - z) * Real.exp z ≤ 1 - z ^ 2 / 2 := by
  let F : ℝ → ℝ := fun x ↦ 1 - x ^ 2 / 2 - (1 - x) * Real.exp x
  have hd (x : ℝ) : HasDerivAt F (x * (Real.exp x - 1)) x := by
    convert (((((hasDerivAt_id x).pow 2).div_const 2).const_sub 1).sub
      (((hasDerivAt_id x).const_sub 1).mul (Real.hasDerivAt_exp x))) using 1
    · rfl
    · dsimp
      ring
  have hm : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
      (continuous_iff_continuousAt.mpr fun x ↦ (hd x).continuousAt).continuousOn
    · intro x _
      exact (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici, mem_Ioi] at hx
      rw [(hd x).deriv]
      exact mul_nonneg hx.le (sub_nonneg.mpr (Real.one_le_exp hx.le))
  have h := hm (by simp) hz hz
  simp only [F, zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero,
    Real.exp_zero, mul_one, sub_self] at h
  linarith

/-- A bound sufficient for the profile root's right limit at the branch point. -/
theorem profileRoot_le_sqrt_parameter {l : ℝ} (hl : 1 < l) :
    profileRoot l ≤ Real.sqrt (2 * (l - 1)) := by
  have h := profile_inverse_equation_le_quadratic (profileRoot_pos hl).le
  rw [profileRoot_equation hl] at h
  have hi : 2 - l ≤ 1 / l := by
    apply (le_div_iff₀ (lt_trans zero_lt_one hl)).mpr
    nlinarith [sq_nonneg (l - 1)]
  apply Real.le_sqrt_of_sq_le
  linarith

/-- Right continuity of the principal offspring branch at the branch point. -/
theorem tendsto_offspringMean_one_right :
    Tendsto offspringMean (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun l : ℝ ↦ 2 - l) (h := fun _ ↦ (1 : ℝ))
  · have hc : Continuous (fun l : ℝ ↦ 2 - l) := by fun_prop
    convert (hc.tendsto 1).mono_left
      (show (𝓝[>] (1 : ℝ)) ≤ 𝓝 1 from nhdsWithin_le_nhds) using 1
    norm_num
  · exact tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with l hl
    exact two_sub_parameter_le_offspringMean hl
  · filter_upwards [self_mem_nhdsWithin] with l hl
    exact (offspringMean_lt_one hl).le

/-- Right continuity of the positive profile root at the branch point. -/
theorem tendsto_profileRoot_one_right :
    Tendsto profileRoot (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℝ ↦ (0 : ℝ)) (h := fun l ↦ Real.sqrt (2 * (l - 1)))
  · exact tendsto_const_nhds
  · have hc : Continuous (fun l : ℝ ↦ Real.sqrt (2 * (l - 1))) := by fun_prop
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with l hl
    exact (profileRoot_pos hl).le
  · filter_upwards [self_mem_nhdsWithin] with l hl
    exact profileRoot_le_sqrt_parameter hl

/-- The paper's critical gap, with its correct value at the branch point.
The inherited `offspringMean` is only specified on `l > 1`, so this extension
is kept separate from the frozen parameters. -/
@[expose] def lambertCriticalGap (l : ℝ) : ℝ :=
  if l = 1 then 0 else 1 / offspringMean l - Real.exp (profileRoot l)

@[simp] theorem lambertCriticalGap_one : lambertCriticalGap 1 = 0 := by
  simp [lambertCriticalGap]

theorem lambertCriticalGap_of_gt_one {l : ℝ} (hl : 1 < l) :
    lambertCriticalGap l = 1 / offspringMean l - Real.exp (profileRoot l) := by
  simp [lambertCriticalGap, hl.ne']

theorem hasDerivAt_lambertCriticalGap {l : ℝ} (hl : 1 < l) :
    HasDerivAt lambertCriticalGap
      ((l - 1) / (l * offspringMean l * (1 - offspringMean l)) +
        -(1 / (l ^ 2 * profileRoot l))) l := by
  apply ((hasDerivAt_reciprocal_offspringMean hl).add
    (hasDerivAt_neg_exp_profileRoot hl)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hl] with x hx
  simpa only [Pi.add_apply, sub_eq_add_neg] using lambertCriticalGap_of_gt_one hx

/-- The boundary value used in the source convexity argument is justified by
limits of both inverse roots, without changing their inherited definitions. -/
theorem continuousOn_lambertCriticalGap : ContinuousOn lambertCriticalGap (Ici 1) := by
  intro l hl
  rcases (show 1 ≤ l from hl).eq_or_lt with h | hl
  · subst l
    apply continuousWithinAt_Ioi_iff_Ici.mp
    change Tendsto lambertCriticalGap (𝓝[>] (1 : ℝ)) (𝓝 (lambertCriticalGap 1))
    rw [lambertCriticalGap_one]
    have hg : Tendsto (fun l ↦ 1 / offspringMean l - Real.exp (profileRoot l))
        (𝓝[>] (1 : ℝ)) (𝓝 (1 / (1 : ℝ) - Real.exp 0)) :=
      (tendsto_const_nhds.div tendsto_offspringMean_one_right (by norm_num)).sub
        (Real.continuous_exp.tendsto 0 |>.comp tendsto_profileRoot_one_right)
    have heq : (fun l ↦ 1 / offspringMean l - Real.exp (profileRoot l)) =ᶠ[𝓝[>] (1 : ℝ)]
        lambertCriticalGap := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (lambertCriticalGap_of_gt_one hx).symm
    simpa using hg.congr' heq
  · exact (hasDerivAt_lambertCriticalGap hl).continuousAt.continuousWithinAt

/-- The curvature computation in the appendix actually gives strict convexity,
including the continuous branch-point extension. -/
theorem strictConvexOn_lambertCriticalGap : StrictConvexOn ℝ (Ici 1) lambertCriticalGap := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 1) continuousOn_lambertCriticalGap
  intro l hl
  rw [interior_Ici, mem_Ioi] at hl
  have hdf : deriv lambertCriticalGap =ᶠ[𝓝 l]
      (fun x ↦ (x - 1) / (x * offspringMean x * (1 - offspringMean x)) +
        -(1 / (x ^ 2 * profileRoot x))) := by
    filter_upwards [eventually_gt_nhds hl] with x hx
    exact (hasDerivAt_lambertCriticalGap hx).deriv
  have hsecond := ((hasDerivAt_reciprocal_offspringMean_slope hl).add
    (hasDerivAt_neg_exp_profileRoot_slope hl)).congr_of_eventuallyEq hdf
  change 0 < deriv (deriv lambertCriticalGap) l
  rw [hsecond.deriv]
  apply add_pos_of_nonneg_of_pos
  · apply div_nonneg (offspringMean_reciprocal_curvature_numerator_nonneg hl)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (offspringMean_pos hl).le)
      (pow_nonneg (sub_pos.mpr (offspringMean_lt_one hl)).le _)
  · apply div_pos
    · nlinarith [sq_nonneg (2 * profileRoot l - 1)]
    · exact mul_pos (pow_pos (lt_trans zero_lt_one hl) _) (pow_pos (profileRoot_pos hl) _)

/-- The source critical equation is exactly the zero equation for its gap. -/
theorem lambertCriticalGap_eq_zero_iff {l : ℝ} (hl : 1 < l) :
    lambertCriticalGap l = 0 ↔ offspringMean l = Real.exp (-profileRoot l) := by
  rw [lambertCriticalGap_of_gt_one hl]
  constructor
  · intro h
    have hg : 1 / offspringMean l = Real.exp (profileRoot l) := by linarith
    have hm := (div_eq_iff (offspringMean_pos hl).ne').mp hg
    rw [Real.exp_neg, ← one_div]
    apply (eq_div_iff (Real.exp_pos _).ne').mpr
    nlinarith
  · intro h
    rw [h, Real.exp_neg]
    simp

/-- Uniqueness by the paper's convexity route: two zeros above one would form
three distinct zeros together with the branch point. -/
theorem lambertCriticalGap_zero_unique {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hFa : lambertCriticalGap a = 0) (hFb : lambertCriticalGap b = 0) : a = b := by
  have hordered {x y : ℝ} (hx : 1 < x) (hxy : x < y)
      (hFx : lambertCriticalGap x = 0) (hFy : lambertCriticalGap y = 0) : False := by
    have h := strictConvexOn_lambertCriticalGap.slope_strict_mono_adjacent
      (show (1 : ℝ) ∈ Ici 1 by simp) (show y ∈ Ici 1 from (hx.trans hxy).le) hx hxy
    simp only [hFx, hFy, lambertCriticalGap_one, sub_self, zero_div, lt_self_iff_false] at h
  rcases lt_trichotomy a b with h | h | h
  · exact (hordered ha h hFa hFb).elim
  · exact h
  · exact (hordered hb h hFb hFa).elim

/-- A complete existence-and-uniqueness proof through the appendix's Lambert
bounds and convex gap, independent of the inherited `criticalEquation` route. -/
theorem existsUnique_criticalParameter_from_lambert :
    ∃! l : ℝ, 1 < l ∧ offspringMean l = Real.exp (-profileRoot l) := by
  obtain ⟨l, hl, heq⟩ := exists_criticalParameter_from_lambert
  refine ⟨l, ⟨hl, heq⟩, ?_⟩
  intro x hx
  exact lambertCriticalGap_zero_unique hx.1 hl
    ((lambertCriticalGap_eq_zero_iff hx.1).mpr hx.2)
    ((lambertCriticalGap_eq_zero_iff hl).mpr heq)

/-- Strict negativity between the branch point and any positive zero. -/
theorem lambertCriticalGap_neg_before_zero {c l : ℝ} (hl : 1 < l) (hlc : l < c)
    (hc : lambertCriticalGap c = 0) : lambertCriticalGap l < 0 := by
  have h := strictConvexOn_lambertCriticalGap.slope_strict_mono_adjacent
    (show (1 : ℝ) ∈ Ici 1 by simp) (show c ∈ Ici 1 from (hl.trans hlc).le) hl hlc
  rw [lambertCriticalGap_one, hc, sub_zero, zero_sub] at h
  have hm := (div_lt_div_iff₀ (sub_pos.mpr hl) (sub_pos.mpr hlc)).mp h
  by_contra! hg
  have hn := mul_nonneg hg (show 0 ≤ c - 1 by linarith)
  nlinarith

/-- Strict positivity after any positive zero. -/
theorem lambertCriticalGap_pos_after_zero {c l : ℝ} (hc1 : 1 < c) (hcl : c < l)
    (hc : lambertCriticalGap c = 0) : 0 < lambertCriticalGap l := by
  have h := strictConvexOn_lambertCriticalGap.slope_strict_mono_adjacent
    (show (1 : ℝ) ∈ Ici 1 by simp) (show l ∈ Ici 1 from (hc1.trans hcl).le) hc1 hcl
  simp only [lambertCriticalGap_one, hc, sub_self, zero_div, sub_zero] at h
  exact (div_pos_iff_of_pos_right (sub_pos.mpr hcl)).mp h

/-- Existence, uniqueness, and crossing orientation from the Lambert route. -/
theorem existsUnique_lambert_critical_crossing :
    ∃! c : ℝ, 1 < c ∧ lambertCriticalGap c = 0 ∧
      (∀ l, 1 < l → l < c → lambertCriticalGap l < 0) ∧
      (∀ l, c < l → 0 < lambertCriticalGap l) := by
  obtain ⟨c, hc, _⟩ := existsUnique_criticalParameter_from_lambert
  have hcz := (lambertCriticalGap_eq_zero_iff hc.1).mpr hc.2
  refine ⟨c, ⟨hc.1, hcz, ?_, ?_⟩, ?_⟩
  · intro l hl hlc
    exact lambertCriticalGap_neg_before_zero hl hlc hcz
  · intro l hcl
    exact lambertCriticalGap_pos_after_zero hc.1 hcl hcz
  · intro l hl
    exact lambertCriticalGap_zero_unique hl.1 hc.1 hl.2.1 hcz

/-- The exponential factor in the manuscript's reciprocal-curvature formula
is the reciprocal-mean factor used in the rational form above. -/
theorem exp_parameter_sub_offspringMean {l : ℝ} (hl : 1 < l) :
    Real.exp (l - offspringMean l) = l / offspringMean l := by
  apply (eq_div_iff (offspringMean_pos hl).ne').mpr
  calc
    Real.exp (l - offspringMean l) * offspringMean l =
        (offspringMean l * Real.exp (-offspringMean l)) * Real.exp l := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ = (l * Real.exp (-l)) * Real.exp l := by
      rw [show offspringMean l * Real.exp (-offspringMean l) = l * Real.exp (-l) from
        (offspringMean_spec hl).2]
    _ = l := by rw [Real.exp_neg]; field_simp

/-- Literally the reciprocal-curvature expression displayed in the appendix,
with the principal Lambert value replaced by `-offspringMean l`. -/
theorem hasDerivAt_reciprocal_offspringMean_slope_paper {l : ℝ} (hl : 1 < l) :
    HasDerivAt
      (fun x ↦ (x - 1) / (x * offspringMean x * (1 - offspringMean x)))
      (Real.exp (l - offspringMean l) / (l ^ 3 * (1 - offspringMean l) ^ 3) *
        ((-offspringMean l + 2 - 2 * l + l ^ 2) ^ 2 -
          (l - 1) ^ 2 * (2 - 2 * l + l ^ 2))) l := by
  apply (hasDerivAt_reciprocal_offspringMean_slope hl).congr_deriv
  rw [exp_parameter_sub_offspringMean hl]
  field_simp [(lt_trans zero_lt_one hl).ne', (offspringMean_pos hl).ne',
    (sub_pos.mpr (offspringMean_lt_one hl)).ne']

/-- The preserved critical parameter is the zero characterized by the new
Lambert-route proof. -/
theorem lambertCriticalGap_criticalParameter : lambertCriticalGap criticalParameter = 0 :=
  (lambertCriticalGap_eq_zero_iff criticalParameter_gt_one).mpr criticalParameter_spec

/-- The lower-parameter crossing inequality, now obtained from the source gap's
strict convexity. -/
theorem exp_neg_profileRoot_lt_offspringMean_lambert {l : ℝ} (hl : 1 < l)
    (hc : l < criticalParameter) : Real.exp (-profileRoot l) < offspringMean l := by
  have h := lambertCriticalGap_neg_before_zero hl hc lambertCriticalGap_criticalParameter
  rw [lambertCriticalGap_of_gt_one hl] at h
  have hdiv : 1 / offspringMean l < Real.exp (profileRoot l) := by linarith
  have hmul := (div_lt_iff₀ (offspringMean_pos hl)).mp hdiv
  rw [Real.exp_neg, ← one_div]
  apply (div_lt_iff₀ (Real.exp_pos _)).mpr
  nlinarith

/-- The upper-parameter crossing inequality from the source gap's strict
convexity. -/
theorem offspringMean_lt_exp_neg_profileRoot_lambert {l : ℝ} (hc : criticalParameter < l) :
    offspringMean l < Real.exp (-profileRoot l) := by
  have hl := criticalParameter_gt_one.trans hc
  have h := lambertCriticalGap_pos_after_zero criticalParameter_gt_one hc
    lambertCriticalGap_criticalParameter
  rw [lambertCriticalGap_of_gt_one hl] at h
  have hdiv : Real.exp (profileRoot l) < 1 / offspringMean l := by linarith
  have hmul := (lt_div_iff₀ (offspringMean_pos hl)).mp hdiv
  rw [Real.exp_neg, ← one_div]
  apply (lt_div_iff₀ (Real.exp_pos _)).mpr
  nlinarith

end HeightPaper
