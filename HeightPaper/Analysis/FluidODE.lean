module

public import HeightPaper.Analysis.FluidParameters
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Topology.Order.MonotoneContinuity

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The deterministic susceptible ODE and infectious curve

The inverse-clock characterization gives the susceptible ODE. Its derivative
then gives strict concavity and positivity of the pre-extinction infectious
curve. These are deterministic results, not a probabilistic fluid-limit theorem.
-/

@[expose] public section

noncomputable section

namespace HeightPaper

open Set Filter
open scoped Topology

/-- Time expressed in terms of the positive susceptible fraction. -/
def fluidClock (l s : ℝ) : ℝ := (l - l * s - Real.log s) / l

theorem fluidClock_fluidSusceptible {l t : ℝ} (hl : 1 < l) :
    fluidClock l (fluidSusceptible l t) = t := by
  have h := fluidSusceptible_log_equation (t := t) hl
  unfold fluidClock
  apply (div_eq_iff (ne_of_gt (lt_trans zero_lt_one hl))).mpr
  linarith

theorem fluidSusceptible_fluidClock {l s : ℝ} (hl : 1 < l) (hs : 0 < s) :
    fluidSusceptible l (fluidClock l s) = s := by
  symm
  apply fluidSusceptible_unique_of_log hl hs
  unfold fluidClock
  field_simp [(ne_of_gt (lt_trans zero_lt_one hl))]
  ring

theorem continuous_fluidSusceptible {l : ℝ} (hl : 1 < l) : Continuous (fluidSusceptible l) := by
  let G : ℝ → (Ioi (0 : ℝ))ᵒᵈ := fun t => ⟨fluidSusceptible l t, fluidSusceptible_pos hl⟩
  have hmono : Monotone G := by
    intro t u htu
    exact (fluidSusceptible_strictAnti hl).antitone htu
  have hsurj : Function.Surjective G := by
    intro s
    let a : Ioi (0 : ℝ) := OrderDual.ofDual s
    refine ⟨fluidClock l a.val, ?_⟩
    apply Subtype.ext
    exact fluidSusceptible_fluidClock hl a.property
  have hc := hmono.continuous_of_surjective hsurj
  exact continuous_subtype_val.comp hc

theorem hasDerivAt_fluidClock {l s : ℝ} (hl : 1 < l) (hs : 0 < s) :
    HasDerivAt (fluidClock l) (-(1 + l * s) / (l * s)) s := by
  have h := ((((hasDerivAt_const s l).sub ((hasDerivAt_id s).const_mul l)).sub
    (Real.hasDerivAt_log hs.ne')).div_const l)
  convert h using 1 <;> first
    | rfl
    | (simp only [mul_one]
       field_simp [hs.ne', (ne_of_gt (lt_trans zero_lt_one hl))]; ring)

/-- The ODE `g' = -l*g/(1+l*g)` from the source. -/
theorem hasDerivAt_fluidSusceptible {l t : ℝ} (hl : 1 < l) :
    HasDerivAt (fluidSusceptible l)
      (-l * fluidSusceptible l t / (1 + l * fluidSusceptible l t)) t := by
  have hs := fluidSusceptible_pos (t := t) hl
  have hl0 := lt_trans zero_lt_one hl
  have hn : 0 < 1 + l * fluidSusceptible l t := by nlinarith [mul_pos hl0 hs]
  have h := HasDerivAt.of_local_left_inverse
    (continuous_fluidSusceptible hl).continuousAt (hasDerivAt_fluidClock hl hs)
    (show -(1 + l * fluidSusceptible l t) / (l * fluidSusceptible l t) ≠ 0 from
      div_ne_zero (neg_ne_zero.mpr hn.ne') (mul_ne_zero hl0.ne' hs.ne'))
    (Filter.Eventually.of_forall (fun x => fluidClock_fluidSusceptible (t := x) hl))
  convert h using 1
  field_simp [hl0.ne', hs.ne', hn.ne']

/-- The untruncated infectious fluid curve; the epidemic limit truncates it at zero. -/
def fluidInfectiousRaw (l t : ℝ) : ℝ := 2 - 2 * fluidSusceptible l t - t

theorem hasDerivAt_fluidInfectiousRaw {l t : ℝ} (hl : 1 < l) :
    HasDerivAt (fluidInfectiousRaw l)
      ((l * fluidSusceptible l t - 1) / (1 + l * fluidSusceptible l t)) t := by
  have hs := fluidSusceptible_pos (t := t) hl
  have hn : 0 < 1 + l * fluidSusceptible l t := by
    nlinarith [mul_pos (lt_trans zero_lt_one hl) hs]
  have h := (((hasDerivAt_fluidSusceptible hl).const_mul 2).const_sub 2).sub (hasDerivAt_id t)
  convert h using 1 <;> first | rfl | (field_simp [hn.ne']; ring)

theorem continuous_fluidInfectiousRaw {l : ℝ} (hl : 1 < l) : Continuous (fluidInfectiousRaw l) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_fluidInfectiousRaw (t := t) hl).continuousAt

theorem deriv_fluidInfectiousRaw_strictAnti {l : ℝ} (hl : 1 < l) :
    StrictAnti (deriv (fluidInfectiousRaw l)) := by
  intro t u htu
  rw [(hasDerivAt_fluidInfectiousRaw hl).deriv, (hasDerivAt_fluidInfectiousRaw hl).deriv]
  have hs := fluidSusceptible_strictAnti hl htu
  have hl0 := lt_trans zero_lt_one hl
  have ht : 0 < 1 + l * fluidSusceptible l t := by
    nlinarith [mul_pos hl0 (fluidSusceptible_pos (t := t) hl)]
  have hu : 0 < 1 + l * fluidSusceptible l u := by
    nlinarith [mul_pos hl0 (fluidSusceptible_pos (t := u) hl)]
  apply (div_lt_div_iff₀ hu ht).mpr
  nlinarith

theorem strictConcaveOn_fluidInfectiousRaw {l : ℝ} (hl : 1 < l) :
    StrictConcaveOn ℝ univ (fluidInfectiousRaw l) :=
  (deriv_fluidInfectiousRaw_strictAnti hl).strictConcaveOn_univ_of_deriv
    (continuous_fluidInfectiousRaw hl)

@[simp] theorem fluidInfectiousRaw_zero {l : ℝ} (hl : 1 < l) : fluidInfectiousRaw l 0 = 0 := by
  simp [fluidInfectiousRaw, fluidSusceptible_zero hl]

@[simp] theorem fluidInfectiousRaw_extinction {l : ℝ} (hl : 1 < l) :
    fluidInfectiousRaw l (fluidExtinctionTime l) = 0 := fluidExtinctionTime_equation hl

theorem fluidInfectiousRaw_pos {l t : ℝ} (hl : 1 < l)
    (ht : t ∈ Ioo (0 : ℝ) (fluidExtinctionTime l)) : 0 < fluidInfectiousRaw l t := by
  have h := (strictConcaveOn_fluidInfectiousRaw hl).lt_on_openSegment
    (mem_univ (0 : ℝ)) (mem_univ (fluidExtinctionTime l))
    (ne_of_lt (fluidExtinctionTime_pos hl)) (Ioo_subset_openSegment ht)
  simpa only [fluidInfectiousRaw_zero hl, fluidInfectiousRaw_extinction hl, min_self] using h

theorem hasDerivAt_fluidInfectiousRaw_zero {l : ℝ} (hl : 1 < l) :
    HasDerivAt (fluidInfectiousRaw l) ((l - 1) / (1 + l)) 0 := by
  simpa only [fluidSusceptible_zero hl, mul_one] using
    hasDerivAt_fluidInfectiousRaw (t := 0) hl

theorem parameter_mul_fluidSusceptible_extinction {l : ℝ} (hl : 1 < l) :
    l * fluidSusceptible l (fluidExtinctionTime l) = offspringMean l := by
  rw [fluidSusceptible_at_extinction hl]
  unfold finalSusceptibleFraction
  field_simp [(ne_of_gt (lt_trans zero_lt_one hl))]

theorem deriv_fluidInfectiousRaw_extinction_neg {l : ℝ} (hl : 1 < l) :
    deriv (fluidInfectiousRaw l) (fluidExtinctionTime l) < 0 := by
  rw [(hasDerivAt_fluidInfectiousRaw hl).deriv, parameter_mul_fluidSusceptible_extinction hl]
  exact div_neg_of_neg_of_pos (sub_neg.mpr (offspringMean_lt_one hl))
    (add_pos zero_lt_one (offspringMean_pos hl))

theorem fluidInfectiousRaw_strictAntiOn_after_extinction {l : ℝ} (hl : 1 < l) :
    StrictAntiOn (fluidInfectiousRaw l) (Ici (fluidExtinctionTime l)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (continuous_fluidInfectiousRaw hl).continuousOn
  intro t ht
  rw [interior_Ici, mem_Ioi] at ht
  exact ((deriv_fluidInfectiousRaw_strictAnti hl) ht).trans
    (deriv_fluidInfectiousRaw_extinction_neg hl)

theorem fluidInfectiousRaw_neg_after_extinction {l t : ℝ} (hl : 1 < l)
    (ht : fluidExtinctionTime l < t) : fluidInfectiousRaw l t < 0 := by
  have h := fluidInfectiousRaw_strictAntiOn_after_extinction hl (show fluidExtinctionTime l ∈
    Ici (fluidExtinctionTime l) from le_rfl) ht.le ht
  simpa only [fluidInfectiousRaw_extinction hl] using h

/-- The nonnegative infectious fluid curve appearing in the source limit. -/
def fluidInfectious (l t : ℝ) : ℝ := max (fluidInfectiousRaw l t) 0

theorem continuous_fluidInfectious {l : ℝ} (hl : 1 < l) : Continuous (fluidInfectious l) :=
  (continuous_fluidInfectiousRaw hl).max continuous_const

theorem fluidInfectious_eq_raw {l t : ℝ} (hl : 1 < l)
    (ht : t ∈ Icc (0 : ℝ) (fluidExtinctionTime l)) :
    fluidInfectious l t = fluidInfectiousRaw l t := by
  unfold fluidInfectious
  apply max_eq_left
  rcases ht.1.eq_or_lt with h | h
  · rw [← h, fluidInfectiousRaw_zero hl]
  · rcases ht.2.lt_or_eq with h' | h'
    · exact (fluidInfectiousRaw_pos hl ⟨h, h'⟩).le
    · rw [h', fluidInfectiousRaw_extinction hl]

theorem fluidInfectious_eq_zero_after_extinction {l t : ℝ} (hl : 1 < l)
    (ht : fluidExtinctionTime l ≤ t) : fluidInfectious l t = 0 := by
  unfold fluidInfectious
  apply max_eq_right
  rcases ht.lt_or_eq with h | h
  · exact (fluidInfectiousRaw_neg_after_extinction hl h).le
  · rw [← h, fluidInfectiousRaw_extinction hl]

end HeightPaper
