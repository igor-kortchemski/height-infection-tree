module

public import HeightPaper.Model.InfectionTree
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# Active profiles and their one-step generating functions

These are finite-state algebraic identities for the infection-tree kernel.
They are the elementary input to the profile martingale, not an asymptotic
profile estimate or a convergence theorem.
-/

@[expose] public section
open scoped NNReal ENNReal BigOperators

namespace HeightPaper.Model

/-- Number of currently infectious vertices at a specified height. -/
def activeProfile (s : State) (h : ℕ) : ℕ :=
  (s.active.filter fun v => s.tree.depth v = h).card

/-- The generating function of the active profile. Setting `w = exp z` gives
its Laplace transform. -/
def activeWeight {R : Type*} [CommSemiring R] (w : R) (s : State) : R :=
  ∑ v ∈ s.active, w ^ s.tree.depth v

@[simp] theorem activeWeight_initial {R : Type*} [CommSemiring R] (w : R) (n : ℕ) :
    activeWeight w (initial n) = 1 := by
  simp [activeWeight, initial]

@[simp] theorem activeWeight_one {R : Type*} [CommSemiring R] (s : State) :
    activeWeight (1 : R) s = infectious s := by
  simp [activeWeight, infectious]

/-- Recovery removes the selected vertex's contribution. -/
theorem activeWeight_recover_add {R : Type*} [CommSemiring R] (w : R)
    {s : State} {v : Fin s.vertices} (hv : v ∈ s.active) :
    activeWeight w (recover s v) + w ^ s.tree.depth v = activeWeight w s := by
  exact Finset.sum_erase_add s.active (fun v => w ^ s.tree.depth v) hv

 theorem activeWeight_recover {R : Type*} [CommRing R] (w : R)
    {s : State} {v : Fin s.vertices} (hv : v ∈ s.active) :
    activeWeight w (recover s v) = activeWeight w s - w ^ s.tree.depth v := by
  exact eq_sub_of_add_eq (activeWeight_recover_add w hv)

/-- Infection adds the selected parent's contribution multiplied by `w`. -/
theorem activeWeight_infect {R : Type*} [CommSemiring R] (w : R)
    (s : State) (v : Fin s.vertices) :
    activeWeight w (infect s v) = activeWeight w s + w * w ^ s.tree.depth v := by
  have hnew : Fin.last s.vertices ∉ s.active.map Fin.castSuccEmb := by
    simp only [Finset.mem_map, not_exists, not_and]
    intro u _ hu
    have hval := congrArg Fin.val hu
    change u.val = s.vertices at hval
    have := u.isLt
    omega
  simp only [activeWeight, infect, Finset.sum_insert hnew, Finset.sum_map]
  simp only [Fin.coe_castSuccEmb, Tree.depth_attach_old, Tree.depth_attach_new]
  rw [pow_succ, add_comm, mul_comm]

/-- Coefficient in the conditional drift for a prescribed infection probability. -/
noncomputable def profileMultiplier (p : ℝ) (w : ℂ) (s : State) : ℂ :=
  1 + ((p : ℂ) * w - (1 - (p : ℂ))) / (infectious s : ℂ)

/-- Averaging over a uniformly chosen infectious vertex gives the elementary
one-step profile identity. This form applies when susceptibles remain. -/
theorem average_activeWeight (p : ℝ) (w : ℂ) (s : State) (h : s.active.Nonempty) :
    (∑ v ∈ s.active,
        ((p : ℂ) * activeWeight w (infect s v) +
          (1 - (p : ℂ)) * activeWeight w (recover s v))) /
        (infectious s : ℂ) = activeWeight w s * profileMultiplier p w s := by
  have hi : (infectious s : ℂ) ≠ 0 := by
    exact_mod_cast h.card_pos.ne'
  have hexpand :
      (∑ v ∈ s.active,
        ((p : ℂ) * activeWeight w (infect s v) +
          (1 - (p : ℂ)) * activeWeight w (recover s v))) =
        (infectious s : ℂ) * activeWeight w s +
          ((p : ℂ) * w - (1 - (p : ℂ))) * activeWeight w s := by
    calc
      _ = ∑ v ∈ s.active,
          (activeWeight w s + ((p : ℂ) * w - (1 - (p : ℂ))) *
            w ^ s.tree.depth v) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [activeWeight_infect, activeWeight_recover w hv]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum]
        rfl
  rw [hexpand]
  unfold profileMultiplier
  field_simp

open MeasureTheory

/-- Integration against the finite uniform active-parent draw is averaging. -/
theorem uniformActive_integral (s : State) (h : s.active.Nonempty)
    (f : Fin s.vertices → ℂ) :
    (∫ v, f v ∂(uniformActive s h).toMeasure) =
      (∑ v ∈ s.active, f v) / (infectious s : ℂ) := by
  rw [PMF.integral_eq_sum]
  simp only [uniformActive_apply]
  simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_zero, ite_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.smul_sum]
  simp [Complex.real_smul, infectious, div_eq_mul_inv, mul_comm]

/-- The finite Bernoulli event draw has its specified two weighted outcomes. -/
theorem eventChoice_integral (rate : ℝ≥0) (susceptible : ℕ) (f : Bool → ℂ) :
    (∫ b, f b ∂(eventChoice rate susceptible).toMeasure) =
      (infectionProbability rate susceptible : ℝ) • f true +
        (1 - (infectionProbability rate susceptible : ℝ)) • f false := by
  rw [PMF.integral_eq_sum, Fintype.sum_bool]
  have hp : (infectionProbability rate susceptible : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast infectionProbability_le_one rate susceptible
  simp [eventChoice_true, eventChoice_false, ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top]

/-- Expected active generating function for the two finite random draws used by
`step`: uniform infectious parent, followed by the infection/recovery event. -/
noncomputable def expectedActiveWeight (rate : ℝ≥0) (w : ℂ)
    (s : State) (h : s.active.Nonempty) : ℂ :=
  ∫ v, (∫ b, activeWeight w
      (if b = true ∧ 0 < s.susceptible then infect s v else recover s v)
      ∂(eventChoice rate s.susceptible).toMeasure)
    ∂(uniformActive s h).toMeasure

/-- The one-step conditional generating-function expectation. The hypothesis
`0 < susceptible` is the pre-exhaustion regime, not an asymptotic assumption. -/
theorem expectedActiveWeight_eq_of_susceptible_pos (rate : ℝ≥0) (w : ℂ) (s : State)
    (h : s.active.Nonempty) (hpos : 0 < s.susceptible) :
    expectedActiveWeight rate w s h =
      activeWeight w s * profileMultiplier (infectionProbability rate s.susceptible) w s := by
  unfold expectedActiveWeight
  rw [uniformActive_integral]
  simp_rw [eventChoice_integral]
  simp only [Bool.false_eq_true, false_and, ↓reduceIte, true_and, hpos, Complex.real_smul,
    Complex.ofReal_sub, Complex.ofReal_one]
  exact average_activeWeight (infectionProbability rate s.susceptible) w s h

/-- Expected profile increment for an infection at a uniform active parent. -/
theorem uniformInfect_integral (w : ℂ) (s : State) (h : s.active.Nonempty) :
    (∫ v, activeWeight w (infect s v) ∂(uniformActive s h).toMeasure) =
      activeWeight w s * (1 + w / (infectious s : ℂ)) := by
  rw [uniformActive_integral]
  simpa [profileMultiplier] using average_activeWeight 1 w s h

/-- Expected profile decrement for recovery of a uniform active vertex. -/
theorem uniformRecover_integral (w : ℂ) (s : State) (h : s.active.Nonempty) :
    (∫ v, activeWeight w (recover s v) ∂(uniformActive s h).toMeasure) =
      activeWeight w s * (1 - 1 / (infectious s : ℂ)) := by
  rw [uniformActive_integral]
  simpa [profileMultiplier, sub_eq_add_neg, div_eq_mul_inv] using average_activeWeight 0 w s h

/-- The conditional expectation formula also holds when susceptibles are
exhausted, because then the infection probability is exactly zero. -/
theorem expectedActiveWeight_eq (rate : ℝ≥0) (w : ℂ) (s : State)
    (h : s.active.Nonempty) :
    expectedActiveWeight rate w s h =
      activeWeight w s * profileMultiplier (infectionProbability rate s.susceptible) w s := by
  by_cases hpos : 0 < s.susceptible
  · exact expectedActiveWeight_eq_of_susceptible_pos rate w s h hpos
  · have hz : s.susceptible = 0 := by omega
    unfold expectedActiveWeight
    simp only [eventChoice_integral, hz, infectionProbability_zero, NNReal.coe_zero,
      zero_smul, sub_zero, one_smul, zero_add, Bool.false_eq_true, false_and, ↓reduceIte]
    rw [uniformRecover_integral]
    simp [profileMultiplier, sub_eq_add_neg, div_eq_mul_inv]

/-- Joint finite draw of the uniformly selected infectious individual and event. -/
noncomputable def stepDraw (rate : ℝ≥0) (s : State) (h : s.active.Nonempty) :
    PMF (Fin s.vertices × Bool) :=
  (uniformActive s h).bind fun v => (eventChoice rate s.susceptible).map (Prod.mk v)

/-- Applying a joint draw produces exactly the previously defined SIR step law. -/
theorem step_eq_map_stepDraw (rate : ℝ≥0) (s : State) (h : s.active.Nonempty) :
    step rate s = (stepDraw rate s h).map (fun vb =>
      if vb.2 = true ∧ 0 < s.susceptible then infect s vb.1 else recover s vb.1) := by
  simp only [step, dite_eq_left h, stepDraw, PMF.map_bind, PMF.map_comp]
  rfl

/-- The two component draws are independent given the current state. -/
theorem stepDraw_apply (rate : ℝ≥0) (s : State) (h : s.active.Nonempty)
    (v : Fin s.vertices) (b : Bool) :
    stepDraw rate s h (v, b) = uniformActive s h v * eventChoice rate s.susceptible b := by
  have hmap (u : Fin s.vertices) :
      ((eventChoice rate s.susceptible).map (Prod.mk u)) (v, b) =
        if v = u then eventChoice rate s.susceptible b else 0 := by
    by_cases hu : v = u
    · subst u
      simp [PMF.map_apply]
    · simp [PMF.map_apply, hu]
  simp only [stepDraw, PMF.bind_apply, hmap]
  simp [mul_ite]

/-- Fubini for the finite draw law, expressed here directly as finite sums. -/
theorem stepDraw_integral (rate : ℝ≥0) (s : State) (h : s.active.Nonempty)
    (f : Fin s.vertices → Bool → ℂ) :
    (∫ vb, f vb.1 vb.2 ∂(stepDraw rate s h).toMeasure) =
      ∫ v, (∫ b, f v b ∂(eventChoice rate s.susceptible).toMeasure)
        ∂(uniformActive s h).toMeasure := by
  simp only [PMF.integral_eq_sum, Fintype.sum_prod_type, stepDraw_apply,
    ENNReal.toReal_mul, mul_smul, Finset.smul_sum]

/-- Expected profile with respect to the actual finite SIR draw law. -/
theorem stepDraw_activeWeight_integral (rate : ℝ≥0) (w : ℂ) (s : State)
    (h : s.active.Nonempty) :
    (∫ vb, activeWeight w
      (if vb.2 = true ∧ 0 < s.susceptible then infect s vb.1 else recover s vb.1)
      ∂(stepDraw rate s h).toMeasure) =
      activeWeight w s * profileMultiplier (infectionProbability rate s.susceptible) w s := by
  exact (stepDraw_integral rate s h (fun v b =>
    activeWeight w (if b = true ∧ 0 < s.susceptible then infect s v else recover s v))).trans
    (expectedActiveWeight_eq rate w s h)

end HeightPaper.Model
