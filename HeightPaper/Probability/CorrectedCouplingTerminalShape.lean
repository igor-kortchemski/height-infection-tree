module

public import HeightPaper.Probability.CorrectedCouplingPotentialExpectation

/-!
# Measurable terminal shapes of both bounding forests

Both forests are evaluated at the same upper extinction time. The arbitrary
default on non-extinction paths is measurable and lies in a null set under
the subcritical assumptions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace HeightPaper.CountCoupling

noncomputable def upperEmptyWords (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) : List Bool :=
  if (finiteCouplingStage roots p q r w j).upper.1.carrier.active = ∅ then [false] else []

noncomputable def couplingExtinctionTime (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) : ℕ := firstLongWord (upperEmptyWords roots p q r w) 0

theorem measurable_couplingExtinctionTime (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ) :
    Measurable (couplingExtinctionTime roots p q r) := by
  have hW : Measurable (upperEmptyWords roots p q r) := by
    apply measurable_pi_iff.mpr
    intro j
    let f : FiniteCouplingState → List Bool := fun s ↦
      if s.upper.1.carrier.active = ∅ then [false] else []
    have hf : Measurable f := measurable_of_countable f
    exact hf.comp (measurable_finiteCouplingStage roots p q r j)
  exact (measurable_firstLongWord 0).comp hW

theorem couplingExtinctionTime_spec (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ)
    (hex : ∃ j, (correctedCouplingStage roots p q r w j).trees.upper.carrier.active = ∅) :
    (correctedCouplingStage roots p q r w (couplingExtinctionTime roots p q r w)).trees.upper.carrier.active = ∅ := by
  have hex' : ∃ j, 0 < (upperEmptyWords roots p q r w j).length := by
    obtain ⟨j, hj⟩ := hex
    have hj' : (finiteCouplingStage roots p q r w j).upper.1.carrier.active = ∅ := by
      rw [← finiteCouplingStage_toState] at hj
      exact hj
    exact ⟨j, by simp [upperEmptyWords, hj']⟩
  have hlen := firstLongWord_spec (upperEmptyWords roots p q r w) 0 hex'
  change 0 < (upperEmptyWords roots p q r w (couplingExtinctionTime roots p q r w)).length at hlen
  have he : (finiteCouplingStage roots p q r w (couplingExtinctionTime roots p q r w)).upper.1.carrier.active = ∅ := by
    by_contra hn
    simp [upperEmptyWords, hn] at hlen
  rw [← finiteCouplingStage_toState]
  exact he

theorem correctedCouplingStage_bound_empty_of_upper_empty
    (roots : Finset ℕ) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) (upper : Bool)
    (he : (correctedCouplingStage roots p q r w j).trees.upper.carrier.active = ∅) :
    ((correctedCouplingStage roots p q r w j).boundForest upper).carrier.active = ∅ := by
  cases upper
  · change (correctedCouplingStage roots p q r w j).trees.lower.carrier.active = ∅
    apply Finset.subset_empty.mp
    simpa only [he] using (correctedCouplingStage_lower_upper roots hpq r w j).1.2
  · exact he

theorem correctedCouplingStage_bound_eq_of_upper_empty
    (roots : Finset ℕ) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) {i j : ℕ} (hij : i ≤ j) (upper : Bool)
    (he : (correctedCouplingStage roots p q r w i).trees.upper.carrier.active = ∅) :
    (correctedCouplingStage roots p q r w j).boundForest upper =
      (correctedCouplingStage roots p q r w i).boundForest upper := by
  have heSide := correctedCouplingStage_bound_empty_of_upper_empty roots hpq r w i upper he
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j _ ih =>
      change ((correctedCouplingStage roots p q r w j).step p q r (w (0, j)) (w (1, j))).boundForest upper = _
      rw [CorrectedCouplingState.step_boundForest _ (correctedCouplingStage_lower_upper roots hpq r w j), ih]
      exact CouplingGenealogy.update_eq_self_of_empty _ heSide _ _ _

noncomputable def terminalBoundShape (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) (upper : Bool)
    (w : (Fin 2 × ℕ) → ℝ) : Fin N → PlaneForward.FiniteShape :=
  forestShape N ((correctedCouplingStage (Finset.range N) p q r w
    (couplingExtinctionTime (Finset.range N) p q r w)).boundForest upper)

theorem measurable_terminalBoundShape (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) (upper : Bool) :
    Measurable (terminalBoundShape N p q r upper) := by
  have hstage : Measurable (fun z : ℕ × ((Fin 2 × ℕ) → ℝ) ↦
      finiteCouplingStage (Finset.range N) p q r z.2 z.1) :=
    measurable_from_prod_countable_right (measurable_finiteCouplingStage (Finset.range N) p q r)
  have hcode := hstage.comp ((measurable_couplingExtinctionTime (Finset.range N) p q r).prodMk measurable_id)
  have hshape : Measurable (fun s : FiniteCouplingState ↦ forestShape N (s.toState.boundForest upper)) :=
    measurable_of_countable _
  have hm := hshape.comp hcode
  change Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦ forestShape N
    ((correctedCouplingStage (Finset.range N) p q r w
      (couplingExtinctionTime (Finset.range N) p q r w)).boundForest upper))
  simpa only [Function.comp_def, id_eq, finiteCouplingStage_toState] using hm

theorem forestCompletionPotential_eventually_terminal
    (N : ℕ) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ)
    (t : Fin N → PlaneForward.FiniteShape) (a : ℝ) (upper : Bool)
    (w : (Fin 2 × ℕ) → ℝ)
    (hex : ∃ j, (correctedCouplingStage (Finset.range N) p q r w j).trees.upper.carrier.active = ∅) :
    ∀ᶠ j in atTop, forestCompletionPotential N t a
      ((correctedCouplingStage (Finset.range N) p q r w j).boundForest upper) =
        if terminalBoundShape N p q r upper w = t then 1 else 0 := by
  let k := couplingExtinctionTime (Finset.range N) p q r w
  have he := couplingExtinctionTime_spec (Finset.range N) p q r w hex
  filter_upwards [eventually_ge_atTop k] with j hj
  rw [correctedCouplingStage_bound_eq_of_upper_empty (Finset.range N) hpq r w hj upper he]
  have hs : ((correctedCouplingStage (Finset.range N) p q r w k).boundForest upper).Valid (Finset.range N) := by
    have hv := correctedCouplingStage_valid (Finset.range N) hpq r w k
    cases upper
    · exact hv.1
    · exact hv.2.2
  exact forestCompletionPotential_of_empty N t a _ hs
    (correctedCouplingStage_bound_empty_of_upper_empty (Finset.range N) hpq r w k upper he)

end HeightPaper.CountCoupling
