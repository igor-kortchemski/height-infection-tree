module

public import HeightPaper.Analysis.Parameters

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Deterministic fluid-limit parameters

The final susceptible fraction and the positive extinction time are
characterized directly from the subcritical offspring mean. The fluid
susceptible curve is defined by its unique positive inverse equation.
No stochastic convergence or fluid-limit theorem is asserted in this module.
-/

@[expose] public section

noncomputable section

namespace HeightPaper

open Set

/-- The final susceptible fraction `m_l / l`. -/
def finalSusceptibleFraction (l : ℝ) : ℝ := offspringMean l / l

/-- The positive extinction time of the deterministic fluid curve. -/
def fluidExtinctionTime (l : ℝ) : ℝ := 2 - 2 * finalSusceptibleFraction l

theorem finalSusceptibleFraction_pos {l : ℝ} (hl : 1 < l) :
    0 < finalSusceptibleFraction l :=
  div_pos (offspringMean_pos hl) (lt_trans zero_lt_one hl)

theorem finalSusceptibleFraction_lt_inv {l : ℝ} (hl : 1 < l) :
    finalSusceptibleFraction l < 1 / l := by
  exact (div_lt_div_iff_of_pos_right (lt_trans zero_lt_one hl)).mpr (offspringMean_lt_one hl)

theorem finalSusceptibleFraction_lt_one {l : ℝ} (hl : 1 < l) :
    finalSusceptibleFraction l < 1 := by
  unfold finalSusceptibleFraction
  apply (div_lt_one (lt_trans zero_lt_one hl)).mpr
  exact (offspringMean_lt_one hl).trans hl

theorem fluidExtinctionTime_pos {l : ℝ} (hl : 1 < l) : 0 < fluidExtinctionTime l := by
  have h := finalSusceptibleFraction_lt_one hl
  unfold fluidExtinctionTime
  linarith

theorem fluidExtinctionTime_lt_two {l : ℝ} (hl : 1 < l) : fluidExtinctionTime l < 2 := by
  have h := finalSusceptibleFraction_pos hl
  unfold fluidExtinctionTime
  linarith

theorem log_finalSusceptibleFraction {l : ℝ} (hl : 1 < l) :
    Real.log (finalSusceptibleFraction l) = offspringMean l - l := by
  have h := outgrowthRate_eq hl
  unfold outgrowthRate at h
  rw [finalSusceptibleFraction, Real.log_div (offspringMean_pos hl).ne'
    (ne_of_gt (lt_trans zero_lt_one hl))]
  linarith

/-- The nontrivial final-size equation of the SIR fluid model. -/
theorem finalSusceptibleFraction_fixedPoint {l : ℝ} (hl : 1 < l) :
    finalSusceptibleFraction l = Real.exp (-l * (1 - finalSusceptibleFraction l)) := by
  have hl0 : l ≠ 0 := ne_of_gt (lt_trans zero_lt_one hl)
  have he : -l * (1 - finalSusceptibleFraction l) = offspringMean l - l := by
    unfold finalSusceptibleFraction
    field_simp [hl0]
    ring
  rw [he, ← log_finalSusceptibleFraction hl, Real.exp_log (finalSusceptibleFraction_pos hl)]

theorem meanEquation_of_finalSize_fixedPoint {l s : ℝ}
    (hs : s = Real.exp (-l * (1 - s))) : meanEquation (l * s) = meanEquation l := by
  unfold meanEquation
  calc
    l * s * Real.exp (-(l * s)) = l * (s * Real.exp (-(l * s))) := by ring
    _ = l * (Real.exp (-l * (1 - s)) * Real.exp (-(l * s))) := by rw [← hs]
    _ = l * Real.exp (-l * (1 - s) + -(l * s)) := by rw [Real.exp_add]
    _ = l * Real.exp (-l) := by congr 2; ring

/-- The final fraction is the unique fixed point strictly between zero and one;
the other final-size fixed point is the initial state `s = 1`. -/
theorem finalSusceptibleFraction_unique {l s : ℝ} (hl : 1 < l)
    (hs0 : 0 < s) (hs1 : s < 1) (hs : s = Real.exp (-l * (1 - s))) :
    s = finalSusceptibleFraction l := by
  have hl0 : 0 < l := lt_trans zero_lt_one hl
  have heq := meanEquation_of_finalSize_fixedPoint hs
  have hsprod : 0 < l * s := mul_pos hl0 hs0
  have hsprodlt : l * s < l := by nlinarith
  have hm : l * s = offspringMean l := by
    by_cases hsub : l * s ≤ 1
    · exact meanEquation_strictMonoOn.injOn ⟨hsprod.le, hsub⟩
        ⟨(offspringMean_pos hl).le, (offspringMean_lt_one hl).le⟩
        (heq.trans (offspringMean_spec hl).2.symm)
    · have hanti := meanEquation_strictAntiOn (le_of_not_ge hsub) hl.le hsprodlt
      rw [heq] at hanti
      exact False.elim ((lt_irrefl _) hanti)
  unfold finalSusceptibleFraction
  apply (eq_div_iff hl0.ne').mpr
  nlinarith

/-- The continuous increasing function inverted by the susceptible curve. -/
def fluidInverse (l s : ℝ) : ℝ := s * Real.exp (l * s)

theorem hasDerivAt_fluidInverse (l s : ℝ) :
    HasDerivAt (fluidInverse l) ((1 + l * s) * Real.exp (l * s)) s := by
  have h := (hasDerivAt_id s).mul (((hasDerivAt_id s).const_mul l).exp)
  convert h using 1 <;> first | rfl | (simp only [id_eq, one_mul, mul_one]; ring)

theorem continuous_fluidInverse (l : ℝ) : Continuous (fluidInverse l) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_fluidInverse l s).continuousAt

theorem fluidInverse_strictMonoOn {l : ℝ} (hl : 0 < l) :
    StrictMonoOn (fluidInverse l) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (continuous_fluidInverse l).continuousOn
  intro s hs
  rw [interior_Ici, mem_Ioi] at hs
  rw [(hasDerivAt_fluidInverse l s).deriv]
  exact mul_pos (by positivity) (Real.exp_pos _)

theorem exists_fluidSusceptible {l t : ℝ} (hl : 1 < l) :
    ∃ s, 0 < s ∧ fluidInverse l s = Real.exp (l - l * t) := by
  let b : ℝ := max 1 (Real.exp (l - l * t))
  have hb1 : 1 ≤ b := le_max_left _ _
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hlexp : 1 ≤ Real.exp (l * b) := Real.one_le_exp (mul_nonneg (by linarith) hb0.le)
  have hupper : Real.exp (l - l * t) ≤ fluidInverse l b := by
    have hbexp : Real.exp (l - l * t) ≤ b := le_max_right _ _
    unfold fluidInverse
    nlinarith
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc hb0.le
    (continuous_fluidInverse l).continuousOn
    (show Real.exp (l - l * t) ∈ Icc (fluidInverse l 0) (fluidInverse l b) from
      ⟨by simpa [fluidInverse] using (Real.exp_pos (l - l * t)).le, hupper⟩)
  refine ⟨s, lt_of_le_of_ne hs.1 ?_, heq⟩
  intro hzero
  rw [← hzero] at heq
  simp only [fluidInverse, mul_zero, Real.exp_zero, zero_mul] at heq
  exact (Real.exp_ne_zero _) heq.symm

/-- The fluid susceptible curve, equivalently the unique positive solution of
`l*g + log g = l - l*t`. -/
def fluidSusceptible (l t : ℝ) : ℝ :=
  sInf {s : ℝ | 0 < s ∧ fluidInverse l s = Real.exp (l - l * t)}

theorem fluidSusceptible_spec {l t : ℝ} (hl : 1 < l) :
    0 < fluidSusceptible l t ∧
      fluidInverse l (fluidSusceptible l t) = Real.exp (l - l * t) := by
  obtain ⟨s, hs0, heq⟩ := exists_fluidSusceptible (t := t) hl
  have hset : {x : ℝ | 0 < x ∧ fluidInverse l x = Real.exp (l - l * t)} = {s} := by
    ext x
    constructor
    · intro hx
      exact mem_singleton_iff.mpr
        ((fluidInverse_strictMonoOn (lt_trans zero_lt_one hl)).injOn hx.1.le hs0.le
          (hx.2.trans heq.symm))
    · rintro rfl
      exact ⟨hs0, heq⟩
  have hcurve : fluidSusceptible l t = s := by
    unfold fluidSusceptible
    rw [hset]
    simp
  rw [hcurve]
  exact ⟨hs0, heq⟩

theorem fluidSusceptible_pos {l t : ℝ} (hl : 1 < l) : 0 < fluidSusceptible l t :=
  (fluidSusceptible_spec hl).1

theorem fluidSusceptible_unique {l t s : ℝ} (hl : 1 < l) (hs : 0 < s)
    (heq : fluidInverse l s = Real.exp (l - l * t)) : s = fluidSusceptible l t :=
  (fluidInverse_strictMonoOn (lt_trans zero_lt_one hl)).injOn hs.le
    (fluidSusceptible_pos hl).le (heq.trans (fluidSusceptible_spec hl).2.symm)

theorem fluidSusceptible_log_equation {l t : ℝ} (hl : 1 < l) :
    l * fluidSusceptible l t + Real.log (fluidSusceptible l t) = l - l * t := by
  have h := congrArg Real.log (fluidSusceptible_spec (t := t) hl).2
  simp only [fluidInverse, Real.log_mul (fluidSusceptible_pos hl).ne'
    (Real.exp_pos _).ne', Real.log_exp] at h
  linarith

theorem fluidSusceptible_unique_of_log {l t s : ℝ} (hl : 1 < l) (hs : 0 < s)
    (heq : l * s + Real.log s = l - l * t) : s = fluidSusceptible l t := by
  apply fluidSusceptible_unique hl hs
  unfold fluidInverse
  rw [← Real.exp_log hs]
  rw [← Real.exp_add]
  congr 1
  rw [Real.exp_log hs]
  linarith

@[simp] theorem fluidSusceptible_zero {l : ℝ} (hl : 1 < l) : fluidSusceptible l 0 = 1 := by
  apply Eq.symm
  apply fluidSusceptible_unique_of_log hl zero_lt_one
  simp

theorem fluidSusceptible_strictAnti {l : ℝ} (hl : 1 < l) : StrictAnti (fluidSusceptible l) := by
  intro t u htu
  apply ((fluidInverse_strictMonoOn (lt_trans zero_lt_one hl)).lt_iff_lt
    (fluidSusceptible_pos hl).le (fluidSusceptible_pos hl).le).mp
  rw [(fluidSusceptible_spec hl).2, (fluidSusceptible_spec hl).2, Real.exp_lt_exp]
  nlinarith

theorem fluidSusceptible_lt_one {l t : ℝ} (hl : 1 < l) (ht : 0 < t) :
    fluidSusceptible l t < 1 := by
  simpa [fluidSusceptible_zero hl] using fluidSusceptible_strictAnti hl ht

theorem fluidSusceptible_at_extinction {l : ℝ} (hl : 1 < l) :
    fluidSusceptible l (fluidExtinctionTime l) = finalSusceptibleFraction l := by
  symm
  apply fluidSusceptible_unique_of_log hl (finalSusceptibleFraction_pos hl)
  rw [log_finalSusceptibleFraction hl]
  unfold fluidExtinctionTime finalSusceptibleFraction
  field_simp [(ne_of_gt (lt_trans zero_lt_one hl))]
  ring

@[simp] theorem fluidExtinctionTime_equation {l : ℝ} (hl : 1 < l) :
    2 - 2 * fluidSusceptible l (fluidExtinctionTime l) - fluidExtinctionTime l = 0 := by
  rw [fluidSusceptible_at_extinction hl]
  unfold fluidExtinctionTime
  ring

theorem fluidExtinctionTime_unique {l t : ℝ} (hl : 1 < l) (ht : 0 < t)
    (heq : 2 - 2 * fluidSusceptible l t - t = 0) : t = fluidExtinctionTime l := by
  have hlog := fluidSusceptible_log_equation (t := t) hl
  have hfixed : fluidSusceptible l t = Real.exp (-l * (1 - fluidSusceptible l t)) := by
    have hlog' : Real.log (fluidSusceptible l t) = -l * (1 - fluidSusceptible l t) := by
      nlinarith
    rw [← hlog', Real.exp_log (fluidSusceptible_pos hl)]
  have hs := finalSusceptibleFraction_unique hl (fluidSusceptible_pos hl)
    (fluidSusceptible_lt_one hl ht) hfixed
  unfold fluidExtinctionTime
  linarith

/-- Agreement with the paper's definition as an infimum of positive zeros. -/
theorem fluidExtinctionTime_eq_inf {l : ℝ} (hl : 1 < l) :
    fluidExtinctionTime l =
      sInf {t : ℝ | 0 < t ∧ 2 - 2 * fluidSusceptible l t - t = 0} := by
  have hs : {t : ℝ | 0 < t ∧ 2 - 2 * fluidSusceptible l t - t = 0} =
      {fluidExtinctionTime l} := by
    ext t
    constructor
    · intro ht
      exact mem_singleton_iff.mpr (fluidExtinctionTime_unique hl ht.1 ht.2)
    · rintro rfl
      exact ⟨fluidExtinctionTime_pos hl, fluidExtinctionTime_equation hl⟩
  rw [hs]
  simp

/-- The positive Lambert inverse equation corresponding to equation `eq:glambda`. -/
theorem fluidSusceptible_lambert_equation {l t : ℝ} (hl : 1 < l) :
    (l * fluidSusceptible l t) * Real.exp (l * fluidSusceptible l t) =
      l * Real.exp l * Real.exp (-l * t) := by
  have h := (fluidSusceptible_spec (t := t) hl).2
  unfold fluidInverse at h
  calc
    (l * fluidSusceptible l t) * Real.exp (l * fluidSusceptible l t) =
        l * (fluidSusceptible l t * Real.exp (l * fluidSusceptible l t)) := by ring
    _ = l * Real.exp (l - l * t) := by rw [h]
    _ = l * Real.exp l * Real.exp (-l * t) := by
      rw [sub_eq_add_neg, Real.exp_add]
      rw [neg_mul]
      ring

end HeightPaper
