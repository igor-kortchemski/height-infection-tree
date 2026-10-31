module

public import HeightPaper.Probability.CorrectedCouplingForestPotential
public import HeightPaper.Probability.CorrectedCouplingEmittedLaw
public import HeightPaper.Probability.FreshBinaryIntegral

/-!
# Constant expectations of the bounding-forest completion potentials

The parent proposal is part of a countable causal code. The recovery sign
is independent of that code, so the pointwise harmonic identity integrates
without any uniform-parent assumption for the lower forest.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace HeightPaper.CountCoupling

def CorrectedCouplingState.boundForest (s : CorrectedCouplingState) (upper : Bool) : CouplingGenealogy :=
  if upper then s.trees.upper else s.trees.lower

def boundForestRate (upper : Bool) (p q : ℝ) : ℝ := if upper then p else q

theorem CorrectedCouplingState.step_boundForest (s : CorrectedCouplingState)
    (hlu : s.trees.lower.LE s.trees.upper) (p q : ℝ) (r : List Bool → ℝ)
    (u recovery : ℝ) (upper : Bool) :
    (s.step p q r u recovery).boundForest upper =
      (s.boundForest upper).update (s.trees.upper.totalSelected u) s.trees.upper.fresh
        (recoveryThresholdBirth (boundForestRate upper p q) recovery) := by
  cases upper
  · exact s.step_lower hlu p q r u recovery
  · rw [boundForest, ite_eq_left rfl, s.step_upper]
    by_cases hu : s.trees.upper.carrier.active.Nonempty
    · simp only [hu, dite_eq_left, CouplingGenealogy.totalSelected, boundForestRate,
        ↓reduceIte, boundForest]
    · have he := Finset.not_nonempty_iff_eq_empty.mp hu
      simp [CouplingGenealogy.totalSelected, boundForestRate, boundForest, he,
        s.trees.upper.update_eq_self_of_empty he]

noncomputable def couplingSelectionCode (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (j : ℕ) (w : (Fin 2 × ℕ) → ℝ) : FiniteCouplingState × ℕ :=
  (finiteCouplingStage roots p q r w j,
    (finiteCouplingStage roots p q r w j).upper.1.totalSelected (w (0, j)))

theorem measurable_selectionCodeMap :
    Measurable (fun z : FiniteCouplingState × ℝ ↦ (z.1, z.1.upper.1.totalSelected z.2)) := by
  apply measurable_from_prod_countable_right
  intro s
  change Measurable (fun u : ℝ ↦ (s, s.upper.1.totalSelected u))
  exact measurable_const.prodMk s.upper.1.measurable_totalSelected

theorem measurable_couplingSelectionCode (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ) (j : ℕ) :
    Measurable (couplingSelectionCode roots p q r j) := by
  have harg : Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦
      (finiteCouplingStage roots p q r w j, w (0, j))) :=
    (measurable_finiteCouplingStage roots p q r j).prodMk (measurable_pi_apply (0, j))
  change Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦
    (finiteCouplingStage roots p q r w j,
      (finiteCouplingStage roots p q r w j).upper.1.totalSelected (w (0, j))))
  simpa only [Function.comp_def] using measurable_selectionCodeMap.comp harg

theorem selectionCode_indep_recovery (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ) (j : ℕ) :
    IndepFun (couplingSelectionCode roots p q r j) (fun w ↦ w (1, j)) pairedUniformLaw := by
  have h := (causal_state_parent_indep_recovery j _ (measurable_finiteCouplingStage roots p q r j)
    (fun _ _ hh ↦ finiteCouplingStage_congr_prefix roots p q r j hh)).comp
      measurable_selectionCodeMap measurable_id
  change IndepFun (fun w : (Fin 2 × ℕ) → ℝ ↦
    (finiteCouplingStage roots p q r w j,
      (finiteCouplingStage roots p q r w j).upper.1.totalSelected (w (0, j)))) _ pairedUniformLaw
  simpa only [Function.comp_def, id_eq] using h

theorem paired_recoveryThreshold_real_mass (j : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (b : Bool) :
    pairedUniformLaw.real {w | recoveryThresholdBirth a (w (1, j)) = b} =
      if b then 1 - a else a := by
  have hD : MeasurableSet {u | recoveryThresholdBirth a u = b} :=
    (measurable_recoveryThresholdBirth a) (measurableSet_singleton b)
  have hm : pairedUniformLaw {w | recoveryThresholdBirth a (w (1, j)) = b} = adaptiveStepMass a b := by
    change pairedUniformLaw ((fun w ↦ w (1, j)) ⁻¹' {u | recoveryThresholdBirth a u = b}) = _
    rw [← Measure.map_apply (measurable_pi_apply (1, j)) hD, pairedUniformLaw_map_eval,
      unitUniform_threshold_probability ha0 ha1]
  change (pairedUniformLaw {w | recoveryThresholdBirth a (w (1, j)) = b}).toReal = _
  rw [hm]
  cases b <;> simp only [adaptiveStepMass, Bool.false_eq_true, ↓reduceIte, ENNReal.toReal_ofReal ha0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ha1)]

theorem forestCompletionPotential_integral_succ
    (N : ℕ) {p q : ℝ} (hpq : p ≤ q) (hp0 : 0 ≤ p) (hq1 : q ≤ 1)
    (r : List Bool → ℝ) (t : Fin N → PlaneForward.FiniteShape) (upper : Bool) (j : ℕ) :
    (∫ w, forestCompletionPotential N t (boundForestRate upper p q)
      ((correctedCouplingStage (Finset.range N) p q r w (j + 1)).boundForest upper) ∂pairedUniformLaw) =
    ∫ w, forestCompletionPotential N t (boundForestRate upper p q)
      ((correctedCouplingStage (Finset.range N) p q r w j).boundForest upper) ∂pairedUniformLaw := by
  let a := boundForestRate upper p q
  have ha0 : 0 ≤ a := by cases upper <;> dsimp [a, boundForestRate] <;> linarith
  have ha1 : a ≤ 1 := by cases upper <;> dsimp [a, boundForestRate] <;> linarith
  let X := couplingSelectionCode (Finset.range N) p q r j
  let Y : ((Fin 2 × ℕ) → ℝ) → Bool := fun w ↦ recoveryThresholdBirth a (w (1, j))
  let F : (FiniteCouplingState × ℕ) → Bool → ℝ := fun x b ↦
    forestCompletionPotential N t a
      ((x.1.toState.boundForest upper).update x.2 x.1.upper.1.fresh b)
  have hX : Measurable X := measurable_couplingSelectionCode _ p q r j
  have hY : Measurable Y := (measurable_recoveryThresholdBirth a).comp (measurable_pi_apply (1, j))
  have hXY : IndepFun X Y pairedUniformLaw :=
    (selectionCode_indep_recovery (Finset.range N) p q r j).comp measurable_id (measurable_recoveryThresholdBirth a)
  have hf (x : FiniteCouplingState × ℕ) (b : Bool) : 0 ≤ F x b ∧ F x b ≤ 1 :=
    ⟨forestCompletionPotential_nonneg N t ha0 ha1 _, forestCompletionPotential_le_one N t ha0 ha1 _⟩
  have hbinary := integral_binary_of_indepFun pairedUniformLaw X Y hX hY hXY a
    (paired_recoveryThreshold_real_mass j ha0 ha1 false)
    (paired_recoveryThreshold_real_mass j ha0 ha1 true) F hf
  have hstep (w : (Fin 2 × ℕ) → ℝ) :
      forestCompletionPotential N t a ((correctedCouplingStage (Finset.range N) p q r w (j + 1)).boundForest upper) =
        F (X w) (Y w) := by
    have hlu := correctedCouplingStage_lower_upper (Finset.range N) hpq r w j
    have hU : (finiteCouplingStage (Finset.range N) p q r w j).upper.1 =
        (correctedCouplingStage (Finset.range N) p q r w j).trees.upper := congrArg
      (fun s : CorrectedCouplingState ↦ s.trees.upper)
      (finiteCouplingStage_toState (Finset.range N) p q r w j)
    change forestCompletionPotential N t a
      (((correctedCouplingStage (Finset.range N) p q r w j).step p q r (w (0, j)) (w (1, j))).boundForest upper) = _
    rw [CorrectedCouplingState.step_boundForest _ hlu]
    dsimp only [F, X, Y, couplingSelectionCode]
    rw [finiteCouplingStage_toState, hU]
  have hharm (w : (Fin 2 × ℕ) → ℝ) : a * F (X w) false + (1 - a) * F (X w) true =
      forestCompletionPotential N t a ((correctedCouplingStage (Finset.range N) p q r w j).boundForest upper) := by
    let s := correctedCouplingStage (Finset.range N) p q r w j
    have hs : (s.boundForest upper).Valid (Finset.range N) := by
      have h := correctedCouplingStage_valid (Finset.range N) hpq r w j
      cases upper
      · exact h.1
      · exact h.2.2
    have hgt : ∀ x ∈ (s.boundForest upper).carrier.vertices, x < s.trees.upper.fresh := by
      intro x hx
      cases upper
      · exact s.trees.upper.mem_lt_fresh ((correctedCouplingStage_lower_upper (Finset.range N) hpq r w j).1.1 hx)
      · exact s.trees.upper.mem_lt_fresh hx
    have hU : (finiteCouplingStage (Finset.range N) p q r w j).upper.1 = s.trees.upper := congrArg
      (fun t : CorrectedCouplingState ↦ t.trees.upper)
      (finiteCouplingStage_toState (Finset.range N) p q r w j)
    dsimp only [F, X, couplingSelectionCode]
    rw [finiteCouplingStage_toState, hU]
    exact forestCompletionPotential_harmonic N t a _ hs _ _ hgt
  calc
    _ = ∫ w, F (X w) (Y w) ∂pairedUniformLaw := integral_congr_ae (ae_of_all _ hstep)
    _ = ∫ w, a * F (X w) false + (1 - a) * F (X w) true ∂pairedUniformLaw := hbinary
    _ = _ := integral_congr_ae (ae_of_all _ hharm)

end HeightPaper.CountCoupling
