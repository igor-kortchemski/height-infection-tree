module

public import HeightPaper.Analysis.LambertCritical
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.Piecewise

/-!
# Regularity at the height phase transition

The two smooth branch formulas are differentiated separately. The critical
matching equation identifies their first derivatives, allowing the derivative
of the piecewise coefficient to be glued continuously.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace HeightPaper

/-- The left branch after cancelling the two terms involving the optimizing
height inside the original formula. -/
def phaseLeftBranch (l : ℝ) : ℝ :=
  (1 + growthFactor l * (1 / offspringMean l - 1)) / outgrowthRate l

/-- The right branch in the paper's main theorem. -/
def phaseRightBranch (l : ℝ) : ℝ := growthFactor l * Real.exp (profileRoot l)

/-- Derivative of the outgrowth rate. -/
def phaseRateSlope (l : ℝ) : ℝ := (l - 1) / (l * (1 - offspringMean l))

/-- The derivative of the left branch, in envelope form. -/
def phaseLeftSlope (l : ℝ) : ℝ :=
  -(Real.exp (outgrowthRate l) - 1) / ((l - 1) ^ 2 * outgrowthRate l) -
    profileExponent l (outgrowthRate l) * phaseRateSlope l / (outgrowthRate l) ^ 2

/-- The derivative of the right branch, simplified by the profile-root equation. -/
def phaseRightSlope (l : ℝ) : ℝ :=
  -(Real.exp (profileRoot l) - 1) / ((l - 1) ^ 2 * profileRoot l)

/-- The continuously matched derivative of the actual coefficient. -/
def mainCoefficientSlope (l : ℝ) : ℝ :=
  if l ≤ criticalParameter then phaseLeftSlope l else phaseRightSlope l

theorem exp_outgrowthRate {l : ℝ} (hl : 1 < l) :
    Real.exp (outgrowthRate l) = 1 / offspringMean l := by
  rw [outgrowthRate, Real.exp_neg, Real.exp_log (offspringMean_pos hl), one_div]

theorem mainCoefficient_eq_phaseLeftBranch {l : ℝ} (hl : 1 < l)
    (hc : l ≤ criticalParameter) : mainCoefficient l = phaseLeftBranch l := by
  rw [mainCoefficient_of_le_critical hc]
  unfold phaseLeftBranch profileExponent
  rw [exp_outgrowthRate hl]
  unfold growthFactor
  field_simp [(sub_pos.mpr hl).ne', (offspringMean_pos hl).ne', (outgrowthRate_pos hl).ne']
  ring

theorem mainCoefficient_eq_phaseRightBranch {l : ℝ} (hl : 1 < l)
    (hc : criticalParameter ≤ l) : mainCoefficient l = phaseRightBranch l :=
  mainCoefficient_of_critical_le hl hc

theorem hasDerivAt_growthFactor {l : ℝ} (hl : 1 < l) :
    HasDerivAt growthFactor (-(1 / (l - 1) ^ 2)) l := by
  convert (hasDerivAt_id l).div ((hasDerivAt_id l).sub_const 1) (sub_pos.mpr hl).ne' using 1
  · rfl
  · dsimp
    field_simp
    ring

theorem hasDerivAt_outgrowthRate {l : ℝ} (hl : 1 < l) :
    HasDerivAt outgrowthRate (phaseRateSlope l) l := by
  convert ((hasDerivAt_offspringMean hl).log (offspringMean_pos hl).ne').neg using 1
  · rfl
  · unfold phaseRateSlope
    field_simp [(lt_trans zero_lt_one hl).ne', (offspringMean_pos hl).ne',
      (sub_pos.mpr (offspringMean_lt_one hl)).ne']
    ring

theorem hasDerivAt_phaseLeftBranch {l : ℝ} (hl : 1 < l) :
    HasDerivAt phaseLeftBranch (phaseLeftSlope l) l := by
  have hd := (((hasDerivAt_growthFactor hl).mul
    ((hasDerivAt_reciprocal_offspringMean hl).sub_const 1)).const_add 1).div
    (hasDerivAt_outgrowthRate hl) (outgrowthRate_pos hl).ne'
  convert hd using 1
  · rfl
  · have hval : (growthFactor * fun x ↦ 1 / offspringMean x - 1) l =
        growthFactor l * (1 / offspringMean l - 1) := rfl
    rw [hval]
    unfold phaseLeftSlope profileExponent phaseRateSlope growthFactor
    rw [exp_outgrowthRate hl]
    field_simp [(lt_trans zero_lt_one hl).ne', (sub_pos.mpr hl).ne',
      (offspringMean_pos hl).ne', (sub_pos.mpr (offspringMean_lt_one hl)).ne',
      (outgrowthRate_pos hl).ne']
    ring

theorem hasDerivAt_phaseRightBranch {l : ℝ} (hl : 1 < l) :
    HasDerivAt phaseRightBranch (phaseRightSlope l) l := by
  have hd := (hasDerivAt_growthFactor hl).mul (hasDerivAt_profileRoot hl).exp
  convert hd using 1
  · rfl
  · unfold phaseRightSlope growthFactor
    field_simp [(lt_trans zero_lt_one hl).ne', (sub_pos.mpr hl).ne', (profileRoot_pos hl).ne']
    have h := (eq_div_iff (lt_trans zero_lt_one hl).ne').mp (profileRoot_equation hl)
    have h' := congrArg (fun t : ℝ ↦ t * (l - 1)) h
    nlinarith

theorem outgrowthRate_criticalParameter :
    outgrowthRate criticalParameter = profileRoot criticalParameter := by
  rw [outgrowthRate, criticalParameter_spec, Real.log_exp, neg_neg]

/-- The first derivatives of the two source branches agree exactly at the
critical parameter, as asserted after `eq:kappa`. -/
theorem phaseSlopes_eq_at_critical : phaseLeftSlope criticalParameter = phaseRightSlope criticalParameter := by
  unfold phaseLeftSlope phaseRightSlope
  rw [outgrowthRate_criticalParameter, profileExponent_profileRoot criticalParameter_gt_one]
  simp

theorem hasDerivAt_mainCoefficient_critical :
    HasDerivAt mainCoefficient (phaseLeftSlope criticalParameter) criticalParameter := by
  have hleft : HasDerivWithinAt mainCoefficient (phaseLeftSlope criticalParameter)
      (Iic criticalParameter) criticalParameter := by
    apply (hasDerivAt_phaseLeftBranch criticalParameter_gt_one).hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds criticalParameter_gt_one).filter_mono nhdsWithin_le_nhds] with l hl hl1
      exact mainCoefficient_eq_phaseLeftBranch hl1 hl
    · exact mainCoefficient_eq_phaseLeftBranch criticalParameter_gt_one le_rfl
  have hright : HasDerivWithinAt mainCoefficient (phaseLeftSlope criticalParameter)
      (Ici criticalParameter) criticalParameter := by
    rw [phaseSlopes_eq_at_critical]
    apply (hasDerivAt_phaseRightBranch criticalParameter_gt_one).hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with l hl
      exact mainCoefficient_eq_phaseRightBranch (criticalParameter_gt_one.trans_le hl) hl
    · exact mainCoefficient_eq_phaseRightBranch criticalParameter_gt_one le_rfl
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright

theorem hasDerivAt_mainCoefficient {l : ℝ} (hl : 1 < l) :
    HasDerivAt mainCoefficient (mainCoefficientSlope l) l := by
  rcases lt_trichotomy l criticalParameter with hc | rfl | hc
  · have hs : mainCoefficientSlope l = phaseLeftSlope l := by simp [mainCoefficientSlope, hc.le]
    rw [hs]
    apply (hasDerivAt_phaseLeftBranch hl).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hl, eventually_lt_nhds hc] with x hx hxc
    exact mainCoefficient_eq_phaseLeftBranch hx hxc.le
  · simpa only [mainCoefficientSlope, le_refl, ite_true] using hasDerivAt_mainCoefficient_critical
  · have hs : mainCoefficientSlope l = phaseRightSlope l := by
      simp [mainCoefficientSlope, not_le.mpr hc]
    rw [hs]
    apply (hasDerivAt_phaseRightBranch hl).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hc] with x hx
    exact mainCoefficient_eq_phaseRightBranch (criticalParameter_gt_one.trans hx) hx.le

theorem continuousAt_phaseLeftSlope {l : ℝ} (hl : 1 < l) : ContinuousAt phaseLeftSlope l := by
  have hm := continuousAt_offspringMean hl
  have hr := continuousAt_outgrowthRate hl
  have hl0 := (lt_trans zero_lt_one hl).ne'
  have hl1 := (sub_pos.mpr hl).ne'
  have hm0 := (offspringMean_pos hl).ne'
  have hm1 := (sub_pos.mpr (offspringMean_lt_one hl)).ne'
  have hr0 := (outgrowthRate_pos hl).ne'
  have hden1 : (l - 1) ^ 2 * outgrowthRate l ≠ 0 := mul_ne_zero (pow_ne_zero _ hl1) hr0
  have hden2 : l * (1 - offspringMean l) ≠ 0 := mul_ne_zero hl0 hm1
  have hden3 : outgrowthRate l ^ 2 ≠ 0 := pow_ne_zero _ hr0
  unfold phaseLeftSlope phaseRateSlope profileExponent growthFactor
  fun_prop

theorem continuousAt_phaseRightSlope {l : ℝ} (hl : 1 < l) : ContinuousAt phaseRightSlope l := by
  have hz := continuousAt_profileRoot hl
  have hl1 := (sub_pos.mpr hl).ne'
  have hz0 := (profileRoot_pos hl).ne'
  have hden : (l - 1) ^ 2 * profileRoot l ≠ 0 := mul_ne_zero (pow_ne_zero _ hl1) hz0
  unfold phaseRightSlope
  fun_prop

theorem continuousOn_mainCoefficientSlope : ContinuousOn mainCoefficientSlope (Ioi 1) := by
  unfold mainCoefficientSlope
  apply ContinuousOn.if
  · intro l hl
    have hc : l = criticalParameter := frontier_Iic_subset criticalParameter hl.2
    subst l
    exact phaseSlopes_eq_at_critical
  · intro l hl
    exact (continuousAt_phaseLeftSlope hl.1).continuousWithinAt
  · intro l hl
    exact (continuousAt_phaseRightSlope hl.1).continuousWithinAt

/-- The height coefficient is continuously differentiable on its entire source
domain, including the critical parameter. -/
theorem contDiffOn_one_mainCoefficient : ContDiffOn ℝ 1 mainCoefficient (Ioi 1) := by
  apply (contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn).mpr
  refine ⟨fun l hl ↦ (hasDerivAt_mainCoefficient hl).differentiableAt.differentiableWithinAt, ?_⟩
  apply continuousOn_mainCoefficientSlope.congr
  intro l hl
  exact (hasDerivAt_mainCoefficient hl).hasDerivWithinAt.derivWithin (isOpen_Ioi.uniqueDiffOn l hl)

theorem contDiffAt_one_mainCoefficient_critical : ContDiffAt ℝ 1 mainCoefficient criticalParameter :=
  contDiffOn_one_mainCoefficient.contDiffAt (isOpen_Ioi.mem_nhds criticalParameter_gt_one)

/-- The derivative of the profile root, named for the curvature comparison. -/
def phaseRootSlope (l : ℝ) : ℝ := (1 - profileRoot l) / (l * profileRoot l)

private def phaseCurvatureBase (l s : ℝ) : ℝ :=
  2 * (Real.exp s - 1) / ((l - 1) ^ 3 * s)

private def phaseCurvatureTilt (l s : ℝ) : ℝ :=
  -(s * Real.exp s - Real.exp s + 1) / ((l - 1) ^ 2 * s ^ 2)

private def phaseProfileSlope (l s a : ℝ) : ℝ :=
  -(Real.exp s - 1 - s * Real.exp s) / (l - 1) ^ 2 -
    growthFactor l * s * Real.exp s * a

private theorem hasDerivAt_phaseTiltSlope {q : ℝ → ℝ} {l a : ℝ}
    (hl : 1 < l) (hq : q l ≠ 0) (hd : HasDerivAt q a l) :
    HasDerivAt (fun x ↦ -(Real.exp (q x) - 1) / ((x - 1) ^ 2 * q x))
      (phaseCurvatureBase l (q l) + phaseCurvatureTilt l (q l) * a) l := by
  have h := (hd.exp.sub_const 1).neg.div
    ((((hasDerivAt_id l).sub_const 1).pow 2).mul hd)
    (mul_ne_zero (pow_ne_zero _ (sub_pos.mpr hl).ne') hq)
  convert h using 1
  · rfl
  · unfold phaseCurvatureBase phaseCurvatureTilt
    dsimp
    field_simp [(sub_pos.mpr hl).ne', hq]
    ring

private theorem hasDerivAt_profileExponent_along {q : ℝ → ℝ} {l a : ℝ}
    (hl : 1 < l) (hd : HasDerivAt q a l) :
    HasDerivAt (fun x ↦ profileExponent x (q x)) (phaseProfileSlope l (q l) a) l := by
  have h := ((hasDerivAt_growthFactor hl).mul
    ((hd.exp.sub_const 1).sub (hd.mul hd.exp))).const_add 1
  convert h using 1
  · rfl
  · unfold phaseProfileSlope
    dsimp
    ring

private theorem differentiableAt_phaseRateSlope {l : ℝ} (hl : 1 < l) :
    DifferentiableAt ℝ phaseRateSlope l := by
  have hm := (hasDerivAt_offspringMean hl).differentiableAt
  have hden : l * (1 - offspringMean l) ≠ 0 :=
    mul_ne_zero (lt_trans zero_lt_one hl).ne' (sub_pos.mpr (offspringMean_lt_one hl)).ne'
  unfold phaseRateSlope
  fun_prop

private theorem hasDerivAt_phaseRightSlope {l : ℝ} (hl : 1 < l) :
    HasDerivAt phaseRightSlope
      (phaseCurvatureBase l (profileRoot l) +
        phaseCurvatureTilt l (profileRoot l) * phaseRootSlope l) l :=
  hasDerivAt_phaseTiltSlope hl (profileRoot_pos hl).ne' (hasDerivAt_profileRoot hl)

private theorem hasDerivAt_phaseLeftSlope_critical :
    HasDerivAt phaseLeftSlope
      (phaseCurvatureBase criticalParameter (profileRoot criticalParameter) +
        phaseCurvatureTilt criticalParameter (profileRoot criticalParameter) * phaseRateSlope criticalParameter -
        phaseProfileSlope criticalParameter (profileRoot criticalParameter) (phaseRateSlope criticalParameter) *
          phaseRateSlope criticalParameter / (profileRoot criticalParameter) ^ 2) criticalParameter := by
  have hr := hasDerivAt_outgrowthRate criticalParameter_gt_one
  have hP := hasDerivAt_profileExponent_along criticalParameter_gt_one hr
  have hA := (differentiableAt_phaseRateSlope criticalParameter_gt_one).hasDerivAt
  have hcor := (hP.mul hA).div (hr.pow 2)
    (pow_ne_zero _ (outgrowthRate_pos criticalParameter_gt_one).ne')
  have h := (hasDerivAt_phaseTiltSlope criticalParameter_gt_one
    (outgrowthRate_pos criticalParameter_gt_one).ne' hr).sub hcor
  convert h using 1
  · rfl
  · have hval : ((fun x ↦ profileExponent x (outgrowthRate x)) * phaseRateSlope) criticalParameter = 0 := by
      change profileExponent criticalParameter (outgrowthRate criticalParameter) * phaseRateSlope criticalParameter = 0
      rw [outgrowthRate_criticalParameter, profileExponent_profileRoot criticalParameter_gt_one, zero_mul]
    have hpval : (outgrowthRate ^ 2) criticalParameter = outgrowthRate criticalParameter ^ 2 := rfl
    rw [hval, hpval]
    simp only [outgrowthRate_criticalParameter,
      profileExponent_profileRoot criticalParameter_gt_one, zero_mul, add_zero, sub_zero]
    field_simp [(profileRoot_pos criticalParameter_gt_one).ne']

private theorem phaseCurvatureTilt_at_profileRoot {l : ℝ} (hl : 1 < l) :
    phaseCurvatureTilt l (profileRoot l) =
      -growthFactor l * Real.exp (profileRoot l) * phaseRootSlope l / profileRoot l := by
  unfold phaseCurvatureTilt growthFactor phaseRootSlope
  field_simp [(lt_trans zero_lt_one hl).ne', (sub_pos.mpr hl).ne', (profileRoot_pos hl).ne']
  have h := (eq_div_iff (lt_trans zero_lt_one hl).ne').mp (profileRoot_equation hl)
  have h' := congrArg (fun t : ℝ ↦ t * (l - 1)) h
  nlinarith

private theorem phaseProfileSlope_at_profileRoot {l a : ℝ} (hl : 1 < l) :
    phaseProfileSlope l (profileRoot l) a = growthFactor l * profileRoot l *
      Real.exp (profileRoot l) * (phaseRootSlope l - a) := by
  unfold phaseProfileSlope growthFactor phaseRootSlope
  field_simp [(lt_trans zero_lt_one hl).ne', (sub_pos.mpr hl).ne', (profileRoot_pos hl).ne']
  have h := (eq_div_iff (lt_trans zero_lt_one hl).ne').mp (profileRoot_equation hl)
  have h' := congrArg (fun t : ℝ ↦ t * (l - 1)) h
  nlinarith

/-- The exact jump between the two branch curvatures at criticality. -/
theorem phase_curvature_jump :
    deriv phaseLeftSlope criticalParameter - deriv phaseRightSlope criticalParameter =
      growthFactor criticalParameter * Real.exp (profileRoot criticalParameter) /
        profileRoot criticalParameter *
        (phaseRateSlope criticalParameter - phaseRootSlope criticalParameter) ^ 2 := by
  rw [hasDerivAt_phaseLeftSlope_critical.deriv,
    (hasDerivAt_phaseRightSlope criticalParameter_gt_one).deriv,
    phaseCurvatureTilt_at_profileRoot criticalParameter_gt_one,
    phaseProfileSlope_at_profileRoot criticalParameter_gt_one]
  field_simp [(profileRoot_pos criticalParameter_gt_one).ne']
  ring

/-- Strict convexity of the critical gap makes the two optimizing tilts cross
with different derivatives. -/
theorem phaseRateSlope_gt_phaseRootSlope_critical :
    phaseRootSlope criticalParameter < phaseRateSlope criticalParameter := by
  have hneg : lambertCriticalGap (5 / 4) < 0 := by
    rw [lambertCriticalGap_of_gt_one (by norm_num : (1 : ℝ) < 5 / 4)]
    exact lambert_critical_gap_neg_at_five_fourths
  have hca : (5 / 4 : ℝ) < criticalParameter := by
    by_contra! h
    rcases h.eq_or_lt with h | h
    · rw [← h, lambertCriticalGap_criticalParameter] at hneg
      exact (lt_irrefl _ hneg)
    · have hp := lambertCriticalGap_pos_after_zero criticalParameter_gt_one h
        lambertCriticalGap_criticalParameter
      linarith
  have hg : HasDerivAt lambertCriticalGap
      (Real.exp (profileRoot criticalParameter) *
        (phaseRateSlope criticalParameter - phaseRootSlope criticalParameter)) criticalParameter := by
    have h := ((hasDerivAt_outgrowthRate criticalParameter_gt_one).exp.sub
      (hasDerivAt_profileRoot criticalParameter_gt_one).exp).congr_of_eventuallyEq
      (show lambertCriticalGap =ᶠ[𝓝 criticalParameter]
        (fun x ↦ Real.exp (outgrowthRate x)) - (fun x ↦ Real.exp (profileRoot x)) by
          filter_upwards [eventually_gt_nhds criticalParameter_gt_one] with x hx
          simp only [Pi.sub_apply, lambertCriticalGap_of_gt_one hx, exp_outgrowthRate hx])
    convert h using 1
    rw [outgrowthRate_criticalParameter]
    unfold phaseRootSlope
    ring
  have hs := strictConvexOn_lambertCriticalGap.convexOn.slope_le_of_hasDerivAt
    (show (5 / 4 : ℝ) ∈ Ici 1 by norm_num) criticalParameter_gt_one.le hca hg
  rw [slope_def_field, lambertCriticalGap_criticalParameter, zero_sub] at hs
  have hp : 0 < -lambertCriticalGap (5 / 4) / (criticalParameter - 5 / 4) :=
    div_pos (neg_pos.mpr hneg) (sub_pos.mpr hca)
  have hprod := hp.trans_le hs
  have he := Real.exp_pos (profileRoot criticalParameter)
  by_contra! h
  have hn := mul_nonpos_of_nonneg_of_nonpos he.le (sub_nonpos.mpr h)
  linarith

/-- The second derivatives of the two branch formulas do not agree. -/
theorem phase_curvature_jump_pos :
    0 < deriv phaseLeftSlope criticalParameter - deriv phaseRightSlope criticalParameter := by
  rw [phase_curvature_jump]
  exact mul_pos
    (div_pos (mul_pos (growthFactor_pos criticalParameter_gt_one)
      (Real.exp_pos _)) (profileRoot_pos criticalParameter_gt_one))
    (sq_pos_of_pos (sub_pos.mpr phaseRateSlope_gt_phaseRootSlope_critical))

private theorem mainCoefficientSlope_eq_right {l : ℝ} (hc : criticalParameter ≤ l) :
    mainCoefficientSlope l = phaseRightSlope l := by
  rcases hc.eq_or_lt with h | h
  · subst l
    simpa only [mainCoefficientSlope, le_refl, ite_true] using phaseSlopes_eq_at_critical
  · simp [mainCoefficientSlope, not_le.mpr h]

/-- The derivative of the height coefficient is not differentiable at the
critical parameter; this rules out twice differentiable and C² regularity. -/
theorem not_differentiableAt_deriv_mainCoefficient_critical :
    ¬DifferentiableAt ℝ (deriv mainCoefficient) criticalParameter := by
  intro hd
  have hleft : HasDerivWithinAt (deriv mainCoefficient) (deriv phaseLeftSlope criticalParameter)
      (Iic criticalParameter) criticalParameter := by
    apply hasDerivAt_phaseLeftSlope_critical.differentiableAt.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds criticalParameter_gt_one).filter_mono nhdsWithin_le_nhds] with l hl hl1
      rw [(hasDerivAt_mainCoefficient hl1).deriv]
      simp only [mainCoefficientSlope, ite_eq_left (show l ≤ criticalParameter from hl)]
    · simpa using hasDerivAt_mainCoefficient_critical.deriv
  have hright : HasDerivWithinAt (deriv mainCoefficient) (deriv phaseRightSlope criticalParameter)
      (Ici criticalParameter) criticalParameter := by
    apply (hasDerivAt_phaseRightSlope criticalParameter_gt_one).differentiableAt.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with l hl
      rw [(hasDerivAt_mainCoefficient (criticalParameter_gt_one.trans_le hl)).deriv]
      exact mainCoefficientSlope_eq_right hl
    · rw [hasDerivAt_mainCoefficient_critical.deriv, phaseSlopes_eq_at_critical]
  have heql : deriv phaseLeftSlope criticalParameter = deriv (deriv mainCoefficient) criticalParameter :=
    (hleft.derivWithin (uniqueDiffOn_Iic criticalParameter criticalParameter le_rfl)).symm.trans
      (hd.hasDerivAt.hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Iic criticalParameter criticalParameter le_rfl))
  have heqr : deriv phaseRightSlope criticalParameter = deriv (deriv mainCoefficient) criticalParameter :=
    (hright.derivWithin (uniqueDiffOn_Ici criticalParameter criticalParameter le_rfl)).symm.trans
      (hd.hasDerivAt.hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Ici criticalParameter criticalParameter le_rfl))
  have h := phase_curvature_jump_pos
  rw [heql, heqr, sub_self] at h
  exact (lt_irrefl _ h)

/-- The paper's failure of C² regularity at the phase transition. -/
theorem not_contDiffAt_two_mainCoefficient_critical :
    ¬ContDiffAt ℝ 2 mainCoefficient criticalParameter := by
  intro h
  exact not_differentiableAt_deriv_mainCoefficient_critical
    (h.derivWithin (m := 1) (by norm_num)).differentiableAt_one

end HeightPaper
