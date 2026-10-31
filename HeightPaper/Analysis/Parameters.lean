module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Analytic parameters of the infection-tree height

The profile exponent is the function in equation `eq:param` of the source.
Its positive zero is defined as the infimum used there. The subcritical
mean is characterized by the unique solution in `(0,1)` of the equation
`m exp(-m) = l exp(-l)`, so it selects the principal Lambert branch without
assuming the existence of a Lambert function.
-/

@[expose] public section

noncomputable section

namespace HeightPaper

open Set

/-- The factor `γ = l / (l - 1)` in the paper. -/
def growthFactor (l : ℝ) : ℝ := l / (l - 1)

/-- The profile exponent `f_l` in equation `eq:param`. -/
def profileExponent (l z : ℝ) : ℝ :=
  1 + growthFactor l * (Real.exp z - 1 - z * Real.exp z)

@[simp] theorem profileExponent_zero (l : ℝ) : profileExponent l 0 = 1 := by
  simp [profileExponent]

theorem growthFactor_pos {l : ℝ} (hl : 1 < l) : 0 < growthFactor l :=
  div_pos (by linarith) (by linarith)

theorem growthFactor_gt_one {l : ℝ} (hl : 1 < l) : 1 < growthFactor l := by
  unfold growthFactor
  apply (lt_div_iff₀ (by linarith : 0 < l - 1)).2
  linarith

theorem hasDerivAt_profileExponent (l z : ℝ) :
    HasDerivAt (profileExponent l) (-growthFactor l * z * Real.exp z) z := by
  unfold profileExponent
  convert (((Real.hasDerivAt_exp z).sub_const 1).sub
    ((hasDerivAt_id z).mul (Real.hasDerivAt_exp z))).const_mul
      (growthFactor l) |>.const_add 1 using 1
  · funext x
    simp only [id_eq, Pi.sub_apply, Pi.mul_apply]
  · simp only [id_eq, one_mul]
    ring

theorem continuous_profileExponent (l : ℝ) : Continuous (profileExponent l) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_profileExponent l x).continuousAt

theorem profileExponent_strictAntiOn {l : ℝ} (hl : 1 < l) :
    StrictAntiOn (profileExponent l) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    (continuous_profileExponent l).continuousOn
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  rw [(hasDerivAt_profileExponent l x).deriv]
  have := mul_pos (mul_pos (growthFactor_pos hl) hx) (Real.exp_pos x)
  nlinarith

theorem profileExponent_one_neg {l : ℝ} (hl : 1 < l) :
    profileExponent l 1 < 0 := by
  have := growthFactor_gt_one hl
  simp only [profileExponent, one_mul]
  linarith

theorem exists_profileRoot {l : ℝ} (hl : 1 < l) :
    ∃ z ∈ Ioo (0 : ℝ) 1, profileExponent l z = 0 := by
  obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    (continuous_profileExponent l).continuousOn
    (show (0 : ℝ) ∈ Icc (profileExponent l 1) (profileExponent l 0) from
      ⟨(profileExponent_one_neg hl).le, by simp⟩)
  refine ⟨z, ⟨lt_of_le_of_ne hz.1 ?_, lt_of_le_of_ne hz.2 ?_⟩, hzero⟩
  · intro heq
    rw [← heq, profileExponent_zero] at hzero
    norm_num at hzero
  · intro heq
    have hneg := profileExponent_one_neg hl
    rw [heq] at hzero
    linarith

/-- The paper's infimum of the positive zeros of `f_l`. -/
def profileRoot (l : ℝ) : ℝ := sInf {z : ℝ | 0 < z ∧ profileExponent l z = 0}

theorem profileRoot_spec {l : ℝ} (hl : 1 < l) :
    profileRoot l ∈ Ioo (0 : ℝ) 1 ∧ profileExponent l (profileRoot l) = 0 := by
  obtain ⟨z, hz, hf⟩ := exists_profileRoot hl
  have hs : {x : ℝ | 0 < x ∧ profileExponent l x = 0} = {z} := by
    ext x
    constructor
    · intro hx
      apply mem_singleton_iff.mpr
      exact (profileExponent_strictAntiOn hl).injOn hx.1.le hz.1.le (hx.2.trans hf.symm)
    · rintro rfl
      exact ⟨hz.1, hf⟩
  simpa [profileRoot, hs] using (show z ∈ Ioo (0 : ℝ) 1 ∧ profileExponent l z = 0 from ⟨hz, hf⟩)

theorem profileRoot_pos {l : ℝ} (hl : 1 < l) : 0 < profileRoot l :=
  (profileRoot_spec hl).1.1

theorem profileRoot_lt_one {l : ℝ} (hl : 1 < l) : profileRoot l < 1 :=
  (profileRoot_spec hl).1.2

@[simp] theorem profileExponent_profileRoot {l : ℝ} (hl : 1 < l) :
    profileExponent l (profileRoot l) = 0 := (profileRoot_spec hl).2

theorem profileRoot_unique {l z : ℝ} (hl : 1 < l) (hz : 0 ≤ z)
    (hf : profileExponent l z = 0) : z = profileRoot l :=
  (profileExponent_strictAntiOn hl).injOn hz (profileRoot_pos hl).le
    (hf.trans (profileExponent_profileRoot hl).symm)

theorem profileExponent_pos {l z : ℝ} (hl : 1 < l) (hz : 0 ≤ z)
    (hlt : z < profileRoot l) : 0 < profileExponent l z := by
  have := profileExponent_strictAntiOn hl hz (profileRoot_pos hl).le hlt
  simpa [profileExponent_profileRoot hl] using this

/-- The map whose inverse on `[0,1]` gives the principal-branch offspring mean. -/
def meanEquation (x : ℝ) : ℝ := x * Real.exp (-x)

theorem hasDerivAt_meanEquation (x : ℝ) :
    HasDerivAt meanEquation ((1 - x) * Real.exp (-x)) x := by
  have h : HasDerivAt (fun y : ℝ => y * Real.exp (-y))
      (1 * Real.exp (-x) + x * (Real.exp (-x) * -1)) x :=
    (hasDerivAt_id x).mul ((hasDerivAt_id x).neg.exp)
  convert h using 1 <;> first | rfl | ring

theorem continuous_meanEquation : Continuous meanEquation :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_meanEquation x).continuousAt

theorem meanEquation_strictMonoOn : StrictMonoOn meanEquation (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) continuous_meanEquation.continuousOn
  intro x hx
  rw [interior_Icc, mem_Ioo] at hx
  rw [(hasDerivAt_meanEquation x).deriv]
  exact mul_pos (sub_pos.mpr hx.2) (Real.exp_pos _)

theorem meanEquation_strictAntiOn : StrictAntiOn meanEquation (Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1) continuous_meanEquation.continuousOn
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  rw [(hasDerivAt_meanEquation x).deriv]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hx) (Real.exp_pos _)

theorem exists_offspringMean {l : ℝ} (hl : 1 < l) :
    ∃ m ∈ Ioo (0 : ℝ) 1, meanEquation m = meanEquation l := by
  have hp : 0 < meanEquation l := mul_pos (by linarith) (Real.exp_pos _)
  have hu : meanEquation l < meanEquation 1 :=
    meanEquation_strictAntiOn (by simp) hl.le hl
  obtain ⟨m, hm, heq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    continuous_meanEquation.continuousOn
    (show meanEquation l ∈ Icc (meanEquation 0) (meanEquation 1) from
      ⟨by simpa [meanEquation] using hp.le, hu.le⟩)
  refine ⟨m, ⟨lt_of_le_of_ne hm.1 ?_, lt_of_le_of_ne hm.2 ?_⟩, heq⟩
  · intro h
    rw [← h] at heq
    simp only [meanEquation, neg_zero, Real.exp_zero, zero_mul] at heq
    dsimp [meanEquation] at hp
    linarith
  · intro h
    rw [h] at heq
    linarith

/-- The unique subcritical mean satisfying the defining Lambert equation.
Its characterization below singles out the principal, rather than lower, branch. -/
def offspringMean (l : ℝ) : ℝ :=
  sInf {m : ℝ | m ∈ Ioo (0 : ℝ) 1 ∧ meanEquation m = meanEquation l}

theorem offspringMean_spec {l : ℝ} (hl : 1 < l) :
    offspringMean l ∈ Ioo (0 : ℝ) 1 ∧
      meanEquation (offspringMean l) = meanEquation l := by
  obtain ⟨m, hm, heq⟩ := exists_offspringMean hl
  have hs : {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ meanEquation x = meanEquation l} = {m} := by
    ext x
    constructor
    · intro hx
      apply mem_singleton_iff.mpr
      exact meanEquation_strictMonoOn.injOn ⟨hx.1.1.le, hx.1.2.le⟩
        ⟨hm.1.le, hm.2.le⟩ (hx.2.trans heq.symm)
    · rintro rfl
      exact ⟨hm, heq⟩
  have hmean : offspringMean l = m := by
    unfold offspringMean
    rw [hs]
    simp
  rw [hmean]
  exact ⟨hm, heq⟩

theorem offspringMean_pos {l : ℝ} (hl : 1 < l) : 0 < offspringMean l :=
  (offspringMean_spec hl).1.1

theorem offspringMean_lt_one {l : ℝ} (hl : 1 < l) : offspringMean l < 1 :=
  (offspringMean_spec hl).1.2

theorem offspringMean_unique {l m : ℝ} (hl : 1 < l) (hm : m ∈ Ioo (0 : ℝ) 1)
    (heq : meanEquation m = meanEquation l) : m = offspringMean l :=
  meanEquation_strictMonoOn.injOn ⟨hm.1.le, hm.2.le⟩
    ⟨(offspringMean_pos hl).le, (offspringMean_lt_one hl).le⟩
    (heq.trans (offspringMean_spec hl).2.symm)

/-- The positive exponential decay rate of the terminal outgrowth heights. -/
def outgrowthRate (l : ℝ) : ℝ := -Real.log (offspringMean l)

theorem outgrowthRate_pos {l : ℝ} (hl : 1 < l) : 0 < outgrowthRate l := by
  exact neg_pos.mpr (Real.log_neg (offspringMean_pos hl) (offspringMean_lt_one hl))

/-- The variational height contribution in Proposition `prop:lc` (ii). -/
def heightIntegrand (l s : ℝ) : ℝ :=
  growthFactor l * Real.exp s + profileExponent l s / outgrowthRate l

/-- The maximum is attained either at the profile boundary or the terminal
outgrowth decay rate. Theorems below prove the variational characterization. -/
def heightCoefficient (l : ℝ) : ℝ :=
  heightIntegrand l (min (profileRoot l) (outgrowthRate l))

theorem hasDerivAt_heightIntegrand (l s : ℝ) :
    HasDerivAt (heightIntegrand l)
      (growthFactor l * Real.exp s * (1 - s / outgrowthRate l)) s := by
  unfold heightIntegrand
  convert ((Real.hasDerivAt_exp s).const_mul (growthFactor l)).add
    ((hasDerivAt_profileExponent l s).div_const (outgrowthRate l)) using 1
  ring

theorem continuous_heightIntegrand (l : ℝ) : Continuous (heightIntegrand l) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_heightIntegrand l s).continuousAt

theorem heightIntegrand_monotoneOn {l : ℝ} (hl : 1 < l) :
    MonotoneOn (heightIntegrand l) (Iic (outgrowthRate l)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Iic _) (continuous_heightIntegrand l).continuousOn
  · intro x _
    exact (hasDerivAt_heightIntegrand l x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Iic, mem_Iio] at hx
    rw [(hasDerivAt_heightIntegrand l x).deriv]
    apply mul_nonneg (mul_nonneg (growthFactor_pos hl).le (Real.exp_pos _).le)
    exact sub_nonneg.mpr ((div_le_one (outgrowthRate_pos hl)).mpr hx.le)

theorem heightIntegrand_antitoneOn {l : ℝ} (hl : 1 < l) :
    AntitoneOn (heightIntegrand l) (Ici (outgrowthRate l)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) (continuous_heightIntegrand l).continuousOn
  · intro x _
    exact (hasDerivAt_heightIntegrand l x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici, mem_Ioi] at hx
    rw [(hasDerivAt_heightIntegrand l x).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (growthFactor_pos hl).le (Real.exp_pos _).le)
    exact sub_nonpos.mpr ((one_le_div (outgrowthRate_pos hl)).mpr hx.le)

theorem heightIntegrand_le_heightCoefficient {l s : ℝ} (hl : 1 < l)
    (hs : s ≤ profileRoot l) : heightIntegrand l s ≤ heightCoefficient l := by
  unfold heightCoefficient
  by_cases hcut : outgrowthRate l ≤ profileRoot l
  · rw [min_eq_right hcut]
    rcases le_total s (outgrowthRate l) with h | h
    · exact heightIntegrand_monotoneOn hl h (by simp) h
    · exact heightIntegrand_antitoneOn hl (by simp) h h
  · have hcut' : profileRoot l ≤ outgrowthRate l := le_of_not_ge hcut
    rw [min_eq_left hcut']
    exact heightIntegrand_monotoneOn hl (hs.trans hcut') hcut' hs

theorem heightCoefficient_isGreatest {l : ℝ} (hl : 1 < l) :
    IsGreatest (heightIntegrand l '' Icc 0 (profileRoot l)) (heightCoefficient l) := by
  refine ⟨?_, ?_⟩
  · refine ⟨min (profileRoot l) (outgrowthRate l), ?_, rfl⟩
    exact ⟨le_min (profileRoot_pos hl).le (outgrowthRate_pos hl).le, min_le_left _ _⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact heightIntegrand_le_heightCoefficient hl hs.2

/-- The variational coefficient occurring in the proof of `thm:main`. -/
theorem heightCoefficient_eq_sup {l : ℝ} (hl : 1 < l) :
    heightCoefficient l = sSup (heightIntegrand l '' Icc 0 (profileRoot l)) := by
  exact (heightCoefficient_isGreatest hl).csSup_eq.symm

theorem heightCoefficient_of_profileRoot_le {l : ℝ} (hl : 1 < l)
    (h : profileRoot l ≤ outgrowthRate l) :
    heightCoefficient l = growthFactor l * Real.exp (profileRoot l) := by
  simp [heightCoefficient, min_eq_left h, heightIntegrand, profileExponent_profileRoot hl]

theorem heightCoefficient_of_outgrowthRate_le {l : ℝ} (hl : 1 < l)
    (h : outgrowthRate l ≤ profileRoot l) :
    heightCoefficient l = l / ((l - 1) * offspringMean l) +
      profileExponent l (outgrowthRate l) / outgrowthRate l := by
  unfold heightCoefficient
  rw [min_eq_right h]
  unfold heightIntegrand
  congr 1
  rw [outgrowthRate, Real.exp_neg, Real.exp_log (offspringMean_pos hl)]
  unfold growthFactor
  rw [div_mul_eq_div_mul_one_div]
  ring

theorem heightCoefficient_pos {l : ℝ} (hl : 1 < l) : 0 < heightCoefficient l := by
  have hp : 0 < heightIntegrand l (profileRoot l) := by
    simpa [heightIntegrand, profileExponent_profileRoot hl] using
      mul_pos (growthFactor_pos hl) (Real.exp_pos (profileRoot l))
  exact hp.trans_le (heightIntegrand_le_heightCoefficient hl le_rfl)

theorem profileRoot_equation {l : ℝ} (hl : 1 < l) :
    (1 - profileRoot l) * Real.exp (profileRoot l) = 1 / l := by
  have hf := profileExponent_profileRoot hl
  unfold profileExponent growthFactor at hf
  have hd : l - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hl)
  have hl0 : l ≠ 0 := ne_of_gt (lt_trans zero_lt_one hl)
  apply (eq_div_iff hl0).mpr
  field_simp [hd] at hf
  nlinarith

theorem parameter_eq_of_profileRoot {l : ℝ} (hl : 1 < l) :
    l = Real.exp (-profileRoot l) / (1 - profileRoot l) := by
  have h := profileRoot_equation hl
  have hl0 : l ≠ 0 := ne_of_gt (lt_trans zero_lt_one hl)
  have hz0 : 1 - profileRoot l ≠ 0 := ne_of_gt (sub_pos.mpr (profileRoot_lt_one hl))
  rw [Real.exp_neg]
  field_simp [hl0] at h
  field_simp [hz0, (Real.exp_pos (profileRoot l)).ne']
  nlinarith

theorem outgrowthRate_eq {l : ℝ} (hl : 1 < l) :
    outgrowthRate l = l - offspringMean l - Real.log l := by
  have h := congrArg Real.log (offspringMean_spec hl).2
  have hl0 : l ≠ 0 := ne_of_gt (lt_trans zero_lt_one hl)
  simp only [meanEquation, Real.log_mul (offspringMean_pos hl).ne'
      (Real.exp_pos _).ne', Real.log_mul hl0 (Real.exp_pos _).ne', Real.log_exp] at h
  unfold outgrowthRate
  linarith

theorem outgrowthRate_le_profileRoot_iff {l : ℝ} (hl : 1 < l) :
    outgrowthRate l ≤ profileRoot l ↔ Real.exp (-profileRoot l) ≤ offspringMean l := by
  rw [← Real.exp_log (offspringMean_pos hl), Real.exp_le_exp]
  unfold outgrowthRate
  constructor <;> intro h <;> linarith

theorem profileRoot_le_outgrowthRate_iff {l : ℝ} (hl : 1 < l) :
    profileRoot l ≤ outgrowthRate l ↔ offspringMean l ≤ Real.exp (-profileRoot l) := by
  rw [← Real.exp_log (offspringMean_pos hl), Real.exp_le_exp]
  unfold outgrowthRate
  constructor <;> intro h <;> linarith

end HeightPaper
