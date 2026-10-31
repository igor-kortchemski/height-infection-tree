module

public import HeightPaper.Analysis.Parameters
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Complex.ExponentialBounds

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The critical parameter

An elementary change of variable reduces the critical equation to a scalar
function of the profile root. This is an alternative to the Lambert bounds
used in the source appendix; the exact equivalence is proved below.
-/

@[expose] public section

noncomputable section

namespace HeightPaper

open Set

/-- The critical equation after eliminating the epidemic rate. -/
def criticalEquation (z : ℝ) : ℝ :=
  meanEquation z + (1 - z) * Real.log (1 - z)

/-- The derivative of `criticalEquation` on `(-∞,1)`. -/
def criticalSlope (z : ℝ) : ℝ :=
  (1 - z) * Real.exp (-z) - Real.log (1 - z) - 1

/-- The second derivative of `criticalEquation` on `(-∞,1)`. -/
def criticalCurvature (z : ℝ) : ℝ :=
  1 / (1 - z) - (2 - z) * Real.exp (-z)

theorem continuous_criticalEquation : Continuous criticalEquation := by
  exact continuous_meanEquation.add (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))

theorem hasDerivAt_criticalEquation {z : ℝ} (hz : z < 1) :
    HasDerivAt criticalEquation (criticalSlope z) z := by
  have hne : 1 - z ≠ 0 := ne_of_gt (sub_pos.mpr hz)
  have h := (hasDerivAt_meanEquation z).add
    ((Real.hasDerivAt_mul_log hne).comp z ((hasDerivAt_id z).const_sub 1))
  convert h using 1 <;> first | rfl | (dsimp [criticalSlope]; ring)

theorem hasDerivAt_criticalSlope {z : ℝ} (hz : z < 1) :
    HasDerivAt criticalSlope (criticalCurvature z) z := by
  have hne : 1 - z ≠ 0 := ne_of_gt (sub_pos.mpr hz)
  have h := ((((hasDerivAt_id z).const_sub 1).mul ((hasDerivAt_id z).neg.exp)).sub
    (((hasDerivAt_id z).const_sub 1).log hne)).sub_const 1
  convert h using 1 <;> first | rfl | (dsimp [criticalCurvature]; ring)

theorem hasDerivAt_criticalCurvature {z : ℝ} (hz : z < 1) :
    HasDerivAt criticalCurvature
      (1 / (1 - z)^2 + (3 - z) * Real.exp (-z)) z := by
  have hne : 1 - z ≠ 0 := ne_of_gt (sub_pos.mpr hz)
  have h := (((hasDerivAt_const z (1 : ℝ)).div ((hasDerivAt_id z).const_sub 1) hne).sub
    (((hasDerivAt_id z).const_sub 2).mul ((hasDerivAt_id z).neg.exp)))
  convert h using 1 <;> first | rfl | (simp only [id_eq, Pi.neg_apply]; ring)

theorem criticalCurvature_strictMonoOn : StrictMonoOn criticalCurvature (Iio 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Iio _)
  · intro x hx
    exact (hasDerivAt_criticalCurvature hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx1 : x < 1 := by simpa only [interior_Iio, mem_Iio] using hx
    rw [(hasDerivAt_criticalCurvature hx1).deriv]
    exact add_pos (one_div_pos.mpr (sq_pos_of_pos (sub_pos.mpr hx1)))
      (mul_pos (by linarith) (Real.exp_pos _))

@[simp] theorem criticalEquation_zero : criticalEquation 0 = 0 := by
  simp [criticalEquation, meanEquation]

@[simp] theorem criticalEquation_one : criticalEquation 1 = Real.exp (-1) := by
  simp [criticalEquation, meanEquation]

@[simp] theorem criticalSlope_zero : criticalSlope 0 = 0 := by
  simp [criticalSlope]

theorem criticalEquation_half_neg : criticalEquation (1 / 2) < 0 := by
  have he : (3 : ℝ) / 2 < Real.exp (1 / 2) := by
    have h := Real.add_one_lt_exp (by norm_num : (1 / 2 : ℝ) ≠ 0)
    linarith
  have he' : Real.exp (-(1 / 2 : ℝ)) < 2 / 3 := by
    rw [Real.exp_neg]
    exact (inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2 / 3)).mpr (by norm_num; linarith)
  have hlog : (2 : ℝ) / 3 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hhalf : Real.log (1 - (1 / 2 : ℝ)) = -Real.log 2 := by
    norm_num [Real.log_div]
  dsimp [criticalEquation, meanEquation]
  rw [hhalf]
  nlinarith

theorem exists_criticalRoot : ∃ z ∈ Ioo (1 / 2 : ℝ) 1, criticalEquation z = 0 := by
  obtain ⟨z, hz, hq⟩ := intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1)
    continuous_criticalEquation.continuousOn
    (show (0 : ℝ) ∈ Icc (criticalEquation (1 / 2)) (criticalEquation 1) from
      ⟨criticalEquation_half_neg.le, by simpa using (Real.exp_pos (-1)).le⟩)
  refine ⟨z, ⟨lt_of_le_of_ne hz.1 ?_, lt_of_le_of_ne hz.2 ?_⟩, hq⟩
  · intro heq
    rw [← heq] at hq
    linarith [criticalEquation_half_neg]
  · intro heq
    rw [heq, criticalEquation_one] at hq
    exact (Real.exp_ne_zero (-1)) hq

private theorem criticalEquation_no_two_roots {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hab : a < b) (hqa : criticalEquation a = 0) (hqb : criticalEquation b = 0) : False := by
  obtain ⟨c, hc, hsc⟩ := exists_hasDerivAt_eq_zero ha
    continuous_criticalEquation.continuousOn (criticalEquation_zero.trans hqa.symm)
    (fun x hx => hasDerivAt_criticalEquation (lt_trans hx.2 (lt_trans hab hb)))
  obtain ⟨d, hd, hsd⟩ := exists_hasDerivAt_eq_zero hab
    continuous_criticalEquation.continuousOn (hqa.trans hqb.symm)
    (fun x hx => hasDerivAt_criticalEquation (lt_trans hx.2 hb))
  have hcd : c < d := hc.2.trans hd.1
  have hd1 : d < 1 := hd.2.trans hb
  have slope_cont : ContinuousOn criticalSlope (Icc 0 d) := by
    intro x hx
    exact (hasDerivAt_criticalSlope (hx.2.trans_lt hd1)).continuousAt.continuousWithinAt
  obtain ⟨u, hu, hcu⟩ := exists_hasDerivAt_eq_zero hc.1
    (slope_cont.mono (Icc_subset_Icc le_rfl hcd.le))
    (criticalSlope_zero.trans hsc.symm)
    (fun x hx => hasDerivAt_criticalSlope (hx.2.trans (hcd.trans hd1)))
  obtain ⟨v, hv, hcv⟩ := exists_hasDerivAt_eq_zero hcd
    (slope_cont.mono (Icc_subset_Icc hc.1.le le_rfl))
    (hsc.trans hsd.symm)
    (fun x hx => hasDerivAt_criticalSlope (hx.2.trans hd1))
  have hlt := criticalCurvature_strictMonoOn (hu.2.trans (hcd.trans hd1))
    (hv.2.trans hd1) (hu.2.trans hv.1)
  rw [hcu, hcv] at hlt
  exact (lt_irrefl 0) hlt

theorem criticalEquation_root_unique {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hqa : criticalEquation a = 0)
    (hqb : criticalEquation b = 0) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact False.elim (criticalEquation_no_two_roots ha.1 hb.2 h hqa hqb)
  · exact h
  · exact False.elim (criticalEquation_no_two_roots hb.1 ha.2 h hqb hqa)

/-- The unique interior zero of the critical equation. -/
def criticalRoot : ℝ := sInf {z : ℝ | z ∈ Ioo (0 : ℝ) 1 ∧ criticalEquation z = 0}

theorem criticalRoot_spec : criticalRoot ∈ Ioo (1 / 2 : ℝ) 1 ∧
    criticalEquation criticalRoot = 0 := by
  obtain ⟨z, hz, hq⟩ := exists_criticalRoot
  have hz0 : z ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
  have hs : {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ criticalEquation x = 0} = {z} := by
    ext x
    constructor
    · intro hx
      exact mem_singleton_iff.mpr (criticalEquation_root_unique hx.1 hz0 hx.2 hq)
    · rintro rfl
      exact ⟨hz0, hq⟩
  have hr : criticalRoot = z := by
    unfold criticalRoot
    rw [hs]
    simp
  rw [hr]
  exact ⟨hz, hq⟩

theorem criticalRoot_pos : 0 < criticalRoot := by
  linarith [criticalRoot_spec.1.1]

theorem criticalRoot_lt_one : criticalRoot < 1 := criticalRoot_spec.1.2

theorem criticalEquation_neg_of_lt_criticalRoot {z : ℝ} (hz : 0 < z)
    (hzc : z < criticalRoot) : criticalEquation z < 0 := by
  by_contra h
  have hq : 0 ≤ criticalEquation z := le_of_not_gt h
  rcases le_total z (1 / 2) with hh | hh
  · obtain ⟨w, hw, hwq⟩ := intermediate_value_Icc' hh
      continuous_criticalEquation.continuousOn ⟨criticalEquation_half_neg.le, hq⟩
    have hw0 : w ∈ Ioo (0 : ℝ) 1 :=
      ⟨hz.trans_le hw.1, by linarith [hw.2]⟩
    have heq := criticalEquation_root_unique hw0 ⟨criticalRoot_pos, criticalRoot_lt_one⟩
      hwq criticalRoot_spec.2
    linarith [criticalRoot_spec.1.1, hw.2]
  · obtain ⟨w, hw, hwq⟩ := intermediate_value_Icc hh
      continuous_criticalEquation.continuousOn ⟨criticalEquation_half_neg.le, hq⟩
    have hw0 : w ∈ Ioo (0 : ℝ) 1 :=
      ⟨by linarith [hw.1], (hw.2.trans_lt hzc).trans criticalRoot_lt_one⟩
    have heq := criticalEquation_root_unique hw0 ⟨criticalRoot_pos, criticalRoot_lt_one⟩
      hwq criticalRoot_spec.2
    linarith [hw.2]

theorem criticalEquation_pos_of_criticalRoot_lt {z : ℝ} (hz : z < 1)
    (hcz : criticalRoot < z) : 0 < criticalEquation z := by
  by_contra h
  have hq : criticalEquation z ≤ 0 := le_of_not_gt h
  obtain ⟨w, hw, hwq⟩ := intermediate_value_Icc hz.le
    continuous_criticalEquation.continuousOn
    ⟨hq, by simpa using (Real.exp_pos (-1)).le⟩
  have hw1 : w < 1 := lt_of_le_of_ne hw.2 (by
    intro h
    rw [h, criticalEquation_one] at hwq
    exact (Real.exp_ne_zero (-1)) hwq)
  have heq := criticalEquation_root_unique
    ⟨(criticalRoot_pos.trans hcz).trans_le hw.1, hw1⟩
    ⟨criticalRoot_pos, criticalRoot_lt_one⟩ hwq criticalRoot_spec.2
  linarith [hw.1]

/-- The epidemic parameter obtained from its profile root. -/
def parameterFromRoot (z : ℝ) : ℝ := Real.exp (-z) / (1 - z)

theorem hasDerivAt_parameterFromRoot {z : ℝ} (hz : z < 1) :
    HasDerivAt parameterFromRoot (z * Real.exp (-z) / (1 - z)^2) z := by
  have hne : 1 - z ≠ 0 := ne_of_gt (sub_pos.mpr hz)
  have h := ((hasDerivAt_id z).neg.exp).div ((hasDerivAt_id z).const_sub 1) hne
  convert h using 1 <;> first | rfl | (simp only [id_eq, Pi.neg_apply]; ring)

theorem parameterFromRoot_strictMonoOn : StrictMonoOn parameterFromRoot (Ico 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico _ _)
  · intro z hz
    exact (hasDerivAt_parameterFromRoot hz.2).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ico, mem_Ioo] at hz
    rw [(hasDerivAt_parameterFromRoot hz.2).deriv]
    exact div_pos (mul_pos hz.1 (Real.exp_pos _))
      (sq_pos_of_pos (sub_pos.mpr hz.2))

@[simp] theorem parameterFromRoot_zero : parameterFromRoot 0 = 1 := by
  simp [parameterFromRoot]

theorem parameterFromRoot_gt_one {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    1 < parameterFromRoot z := by
  simpa using parameterFromRoot_strictMonoOn (show (0 : ℝ) ∈ Ico 0 1 by norm_num)
    ⟨hz.1.le, hz.2⟩ hz.1

theorem parameterFromRoot_profileRoot {l : ℝ} (hl : 1 < l) :
    parameterFromRoot (profileRoot l) = l := (parameter_eq_of_profileRoot hl).symm

theorem profileRoot_parameterFromRoot {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    profileRoot (parameterFromRoot z) = z := by
  have hl := parameterFromRoot_gt_one hz
  apply parameterFromRoot_strictMonoOn.injOn
    ⟨(profileRoot_pos hl).le, profileRoot_lt_one hl⟩ ⟨hz.1.le, hz.2⟩
  exact parameterFromRoot_profileRoot hl

theorem log_meanEquation {x : ℝ} (hx : 0 < x) :
    Real.log (meanEquation x) = Real.log x - x := by
  simp [meanEquation, Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp, sub_eq_add_neg]

theorem critical_log_difference {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    Real.log (meanEquation (parameterFromRoot z)) -
      Real.log (meanEquation (Real.exp (-z))) = -criticalEquation z / (1 - z) := by
  have hp : 0 < parameterFromRoot z := lt_trans zero_lt_one (parameterFromRoot_gt_one hz)
  rw [log_meanEquation hp, log_meanEquation (Real.exp_pos _), Real.log_exp]
  simp only [parameterFromRoot, Real.log_div (Real.exp_pos _).ne'
    (ne_of_gt (sub_pos.mpr hz.2)), Real.log_exp, criticalEquation, meanEquation]
  field_simp [(ne_of_gt (sub_pos.mpr hz.2))]
  ring

theorem offspringMean_le_threshold_iff {l : ℝ} (hl : 1 < l) :
    offspringMean l ≤ Real.exp (-profileRoot l) ↔ 0 ≤ criticalEquation (profileRoot l) := by
  have hz := (profileRoot_spec hl).1
  have ht : Real.exp (-profileRoot l) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact (Real.exp_pos _).le
    · rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr hz.1.le
  have hm : offspringMean l ∈ Icc (0 : ℝ) 1 :=
    ⟨(offspringMean_pos hl).le, (offspringMean_lt_one hl).le⟩
  have hdiff := critical_log_difference hz
  rw [parameterFromRoot_profileRoot hl] at hdiff
  have hpos : 0 < 1 - profileRoot l := sub_pos.mpr hz.2
  calc
    offspringMean l ≤ Real.exp (-profileRoot l) ↔
        meanEquation (offspringMean l) ≤ meanEquation (Real.exp (-profileRoot l)) :=
      (meanEquation_strictMonoOn.le_iff_le hm ht).symm
    _ ↔ Real.log (meanEquation l) ≤ Real.log (meanEquation (Real.exp (-profileRoot l))) := by
      rw [(offspringMean_spec hl).2]
      exact (Real.log_le_log_iff (mul_pos (lt_trans zero_lt_one hl) (Real.exp_pos _))
        (mul_pos (Real.exp_pos _) (Real.exp_pos _))).symm
    _ ↔ 0 ≤ criticalEquation (profileRoot l) := by
      constructor
      · intro h
        have hq : -criticalEquation (profileRoot l) / (1 - profileRoot l) ≤ 0 := by linarith
        have hq' := (div_le_iff₀ hpos).mp hq
        linarith
      · intro h
        have hq : -criticalEquation (profileRoot l) / (1 - profileRoot l) ≤ 0 :=
          (div_le_iff₀ hpos).mpr (by linarith)
        linarith

theorem offspringMean_lt_threshold_iff {l : ℝ} (hl : 1 < l) :
    offspringMean l < Real.exp (-profileRoot l) ↔ 0 < criticalEquation (profileRoot l) := by
  have hz := (profileRoot_spec hl).1
  have ht : Real.exp (-profileRoot l) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact (Real.exp_pos _).le
    · rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr hz.1.le
  have hm : offspringMean l ∈ Icc (0 : ℝ) 1 :=
    ⟨(offspringMean_pos hl).le, (offspringMean_lt_one hl).le⟩
  have hdiff := critical_log_difference hz
  rw [parameterFromRoot_profileRoot hl] at hdiff
  have hpos : 0 < 1 - profileRoot l := sub_pos.mpr hz.2
  calc
    offspringMean l < Real.exp (-profileRoot l) ↔
        meanEquation (offspringMean l) < meanEquation (Real.exp (-profileRoot l)) :=
      (meanEquation_strictMonoOn.lt_iff_lt hm ht).symm
    _ ↔ Real.log (meanEquation l) < Real.log (meanEquation (Real.exp (-profileRoot l))) := by
      rw [(offspringMean_spec hl).2]
      exact (Real.log_lt_log_iff (mul_pos (lt_trans zero_lt_one hl) (Real.exp_pos _))
        (mul_pos (Real.exp_pos _) (Real.exp_pos _))).symm
    _ ↔ 0 < criticalEquation (profileRoot l) := by
      constructor
      · intro h
        have hq : -criticalEquation (profileRoot l) / (1 - profileRoot l) < 0 := by linarith
        have hq' := (div_lt_iff₀ hpos).mp hq
        linarith
      · intro h
        have hq : -criticalEquation (profileRoot l) / (1 - profileRoot l) < 0 :=
          (div_lt_iff₀ hpos).mpr (by linarith)
        linarith

theorem offspringMean_eq_threshold_iff {l : ℝ} (hl : 1 < l) :
    offspringMean l = Real.exp (-profileRoot l) ↔ criticalEquation (profileRoot l) = 0 := by
  constructor
  · intro h
    have hq := (offspringMean_le_threshold_iff hl).mp h.le
    have hn : ¬0 < criticalEquation (profileRoot l) := by
      intro hp
      have hm := (offspringMean_lt_threshold_iff hl).mpr hp
      linarith
    exact le_antisymm (le_of_not_gt hn) hq
  · intro h
    apply le_antisymm ((offspringMean_le_threshold_iff hl).mpr h.ge)
    apply le_of_not_gt
    intro hm
    have hq := (offspringMean_lt_threshold_iff hl).mp hm
    linarith

/-- The critical value from equation `eq:lc`, defined directly from its equation. -/
def criticalParameter : ℝ :=
  sInf {l : ℝ | 1 < l ∧ offspringMean l = Real.exp (-profileRoot l)}

theorem criticalParameter_eq : criticalParameter = parameterFromRoot criticalRoot := by
  have hc : 1 < parameterFromRoot criticalRoot :=
    parameterFromRoot_gt_one ⟨criticalRoot_pos, criticalRoot_lt_one⟩
  have hroot := profileRoot_parameterFromRoot ⟨criticalRoot_pos, criticalRoot_lt_one⟩
  have hcross : offspringMean (parameterFromRoot criticalRoot) =
      Real.exp (-profileRoot (parameterFromRoot criticalRoot)) := by
    apply (offspringMean_eq_threshold_iff hc).mpr
    rw [hroot]
    exact criticalRoot_spec.2
  have hs : {l : ℝ | 1 < l ∧ offspringMean l = Real.exp (-profileRoot l)} =
      {parameterFromRoot criticalRoot} := by
    ext l
    constructor
    · intro hl
      apply mem_singleton_iff.mpr
      have hz : profileRoot l = criticalRoot := criticalEquation_root_unique
        (profileRoot_spec hl.1).1 ⟨criticalRoot_pos, criticalRoot_lt_one⟩
        ((offspringMean_eq_threshold_iff hl.1).mp hl.2) criticalRoot_spec.2
      calc
        l = parameterFromRoot (profileRoot l) := (parameterFromRoot_profileRoot hl.1).symm
        _ = parameterFromRoot criticalRoot := congrArg parameterFromRoot hz
    · rintro rfl
      exact ⟨hc, hcross⟩
  unfold criticalParameter
  rw [hs]
  simp

theorem criticalParameter_gt_one : 1 < criticalParameter := by
  rw [criticalParameter_eq]
  exact parameterFromRoot_gt_one ⟨criticalRoot_pos, criticalRoot_lt_one⟩

theorem criticalParameter_spec :
    offspringMean criticalParameter = Real.exp (-profileRoot criticalParameter) := by
  apply (offspringMean_eq_threshold_iff criticalParameter_gt_one).mpr
  rw [criticalParameter_eq, profileRoot_parameterFromRoot ⟨criticalRoot_pos, criticalRoot_lt_one⟩]
  exact criticalRoot_spec.2

theorem criticalParameter_unique {l : ℝ} (hl : 1 < l)
    (hc : offspringMean l = Real.exp (-profileRoot l)) : l = criticalParameter := by
  have hz := criticalEquation_root_unique (profileRoot_spec hl).1
    ⟨criticalRoot_pos, criticalRoot_lt_one⟩
    ((offspringMean_eq_threshold_iff hl).mp hc) criticalRoot_spec.2
  rw [criticalParameter_eq, ← hz, parameterFromRoot_profileRoot hl]

theorem existsUnique_criticalParameter :
    ∃! l : ℝ, 1 < l ∧ offspringMean l = Real.exp (-profileRoot l) := by
  exact ⟨criticalParameter, ⟨criticalParameter_gt_one, criticalParameter_spec⟩,
    fun l hl => criticalParameter_unique hl.1 hl.2⟩

theorem parameter_le_critical_iff {l : ℝ} (hl : 1 < l) :
    l ≤ criticalParameter ↔ profileRoot l ≤ criticalRoot := by
  have h := parameterFromRoot_strictMonoOn.le_iff_le
    ⟨(profileRoot_pos hl).le, profileRoot_lt_one hl⟩
    ⟨criticalRoot_pos.le, criticalRoot_lt_one⟩
  simpa only [parameterFromRoot_profileRoot hl, ← criticalParameter_eq] using h

theorem parameter_lt_critical_iff {l : ℝ} (hl : 1 < l) :
    l < criticalParameter ↔ profileRoot l < criticalRoot := by
  have h := parameterFromRoot_strictMonoOn.lt_iff_lt
    ⟨(profileRoot_pos hl).le, profileRoot_lt_one hl⟩
    ⟨criticalRoot_pos.le, criticalRoot_lt_one⟩
  simpa only [parameterFromRoot_profileRoot hl, ← criticalParameter_eq] using h

theorem offspringMean_gt_threshold_of_lt_critical {l : ℝ} (hl : 1 < l)
    (hc : l < criticalParameter) : Real.exp (-profileRoot l) < offspringMean l := by
  have hneg := criticalEquation_neg_of_lt_criticalRoot (profileRoot_pos hl)
    ((parameter_lt_critical_iff hl).mp hc)
  apply lt_of_not_ge
  intro hm
  have hq := (offspringMean_le_threshold_iff hl).mp hm
  linarith

theorem offspringMean_lt_threshold_of_critical_lt {l : ℝ} (hl : 1 < l)
    (hc : criticalParameter < l) : offspringMean l < Real.exp (-profileRoot l) := by
  apply (offspringMean_lt_threshold_iff hl).mpr
  have hz : criticalRoot < profileRoot l := by
    apply lt_of_not_ge
    intro h
    have := (parameter_le_critical_iff hl).mpr h
    linarith
  exact criticalEquation_pos_of_criticalRoot_lt (profileRoot_lt_one hl) hz

theorem outgrowthRate_le_profileRoot_of_le_critical {l : ℝ} (hl : 1 < l)
    (hc : l ≤ criticalParameter) : outgrowthRate l ≤ profileRoot l := by
  apply (outgrowthRate_le_profileRoot_iff hl).mpr
  rcases hc.lt_or_eq with h | rfl
  · exact (offspringMean_gt_threshold_of_lt_critical hl h).le
  · exact criticalParameter_spec.symm.le

theorem profileRoot_le_outgrowthRate_of_critical_le {l : ℝ} (hl : 1 < l)
    (hc : criticalParameter ≤ l) : profileRoot l ≤ outgrowthRate l := by
  apply (profileRoot_le_outgrowthRate_iff hl).mpr
  rcases hc.lt_or_eq with h | h
  · exact (offspringMean_lt_threshold_of_critical_lt hl h).le
  · subst l
    exact criticalParameter_spec.le

/-- The piecewise constant in the statement of `thm:main`. Both branches agree
at `criticalParameter`, as shown by the variational characterization. -/
def mainCoefficient (l : ℝ) : ℝ :=
  if l ≤ criticalParameter then
    l / ((l - 1) * offspringMean l) +
      profileExponent l (outgrowthRate l) / outgrowthRate l
  else growthFactor l * Real.exp (profileRoot l)

theorem mainCoefficient_eq_heightCoefficient {l : ℝ} (hl : 1 < l) :
    mainCoefficient l = heightCoefficient l := by
  unfold mainCoefficient
  split_ifs with hc
  · exact (heightCoefficient_of_outgrowthRate_le hl
      (outgrowthRate_le_profileRoot_of_le_critical hl hc)).symm
  · exact (heightCoefficient_of_profileRoot_le hl
      (profileRoot_le_outgrowthRate_of_critical_le hl (le_of_not_ge hc))).symm

theorem mainCoefficient_of_le_critical {l : ℝ} (hc : l ≤ criticalParameter) :
    mainCoefficient l = l / ((l - 1) * offspringMean l) +
      profileExponent l (outgrowthRate l) / outgrowthRate l := by
  simp only [mainCoefficient, ite_eq_left hc]

theorem mainCoefficient_of_critical_le {l : ℝ} (hl : 1 < l)
    (hc : criticalParameter ≤ l) :
    mainCoefficient l = growthFactor l * Real.exp (profileRoot l) := by
  rw [mainCoefficient_eq_heightCoefficient hl]
  exact heightCoefficient_of_profileRoot_le hl (profileRoot_le_outgrowthRate_of_critical_le hl hc)

theorem mainCoefficient_eq_sup {l : ℝ} (hl : 1 < l) :
    mainCoefficient l = sSup (heightIntegrand l '' Icc 0 (profileRoot l)) := by
  rw [mainCoefficient_eq_heightCoefficient hl, heightCoefficient_eq_sup hl]

theorem mainCoefficient_pos {l : ℝ} (hl : 1 < l) : 0 < mainCoefficient l := by
  rw [mainCoefficient_eq_heightCoefficient hl]
  exact heightCoefficient_pos hl

theorem growthFactor_mul_exp_profileRoot_le_mainCoefficient {l : ℝ} (hl : 1 < l) :
    growthFactor l * Real.exp (profileRoot l) ≤ mainCoefficient l := by
  rw [mainCoefficient_eq_heightCoefficient hl]
  simpa [heightIntegrand, profileExponent_profileRoot hl] using
    heightIntegrand_le_heightCoefficient hl (le_refl (profileRoot l))

/-- The defining inverse equation and principal-branch range for the paper's
`-W(-l exp(-l))`. -/
theorem offspringMean_principal_lambert {l : ℝ} (hl : 1 < l) :
    -offspringMean l ∈ Ioo (-1 : ℝ) 0 ∧
      (-offspringMean l) * Real.exp (-offspringMean l) = -l * Real.exp (-l) := by
  refine ⟨⟨by linarith [offspringMean_lt_one hl], by linarith [offspringMean_pos hl]⟩, ?_⟩
  have h := (offspringMean_spec hl).2
  dsimp [meanEquation] at h
  linarith

/-- The defining inverse equation and principal-branch range for the paper's
`1 + W(-1/(e*l))`. -/
theorem profileRoot_principal_lambert {l : ℝ} (hl : 1 < l) :
    profileRoot l - 1 ∈ Ioo (-1 : ℝ) 0 ∧
      (profileRoot l - 1) * Real.exp (profileRoot l - 1) =
        -(1 / (Real.exp 1 * l)) := by
  refine ⟨⟨by linarith [profileRoot_pos hl], by linarith [profileRoot_lt_one hl]⟩, ?_⟩
  rw [Real.exp_sub]
  calc
    (profileRoot l - 1) * (Real.exp (profileRoot l) / Real.exp 1) =
        -((1 - profileRoot l) * Real.exp (profileRoot l)) / Real.exp 1 := by ring
    _ = -(1 / l) / Real.exp 1 := by rw [profileRoot_equation hl]
    _ = -(1 / (Real.exp 1 * l)) := by
      field_simp [(ne_of_gt (lt_trans zero_lt_one hl)), (Real.exp_pos (1 : ℝ)).ne']

/-- Uniqueness of the inverse equation on the negative principal branch. -/
theorem principalLambert_negative_unique {u v : ℝ} (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-1 : ℝ) 0)
    (heq : u * Real.exp u = v * Real.exp v) : u = v := by
  have hmean : meanEquation (-u) = meanEquation (-v) := by
    dsimp [meanEquation]
    simp only [neg_neg]
    linarith
  have h := meanEquation_strictMonoOn.injOn
    (show -u ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hu.1, hu.2])
    (show -v ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hv.1, hv.2]) hmean
  linarith

theorem offspringMean_eq_neg_of_lambert {l w : ℝ} (hl : 1 < l)
    (hw : w ∈ Icc (-1 : ℝ) 0)
    (heq : w * Real.exp w = -l * Real.exp (-l)) : offspringMean l = -w := by
  have h := offspringMean_principal_lambert hl
  have hequal := principalLambert_negative_unique ⟨h.1.1.le, h.1.2.le⟩ hw
    (h.2.trans heq.symm)
  linarith

theorem profileRoot_eq_one_add_of_lambert {l w : ℝ} (hl : 1 < l)
    (hw : w ∈ Icc (-1 : ℝ) 0)
    (heq : w * Real.exp w = -(1 / (Real.exp 1 * l))) : profileRoot l = 1 + w := by
  have h := profileRoot_principal_lambert hl
  have hequal := principalLambert_negative_unique ⟨h.1.1.le, h.1.2.le⟩ hw
    (h.2.trans heq.symm)
  linarith

end HeightPaper
