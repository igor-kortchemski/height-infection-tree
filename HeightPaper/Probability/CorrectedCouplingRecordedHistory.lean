module

public import HeightPaper.Probability.CorrectedCouplingSampledForest
public import HeightPaper.Probability.CorrectedCouplingPastUpper

/-!
# Causal histories of the middle forest at physical times

Recording an after-event forest only when a letter is emitted makes the
entire logical history available as a countable causal code. This avoids
asserting causality of totalized random-time evaluations off their domain.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HeightPaper.CountCoupling

instance : MeasurableSpace (List FiniteCouplingGenealogy) := ⊤

noncomputable def recordedMiddleHistory (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) : ℕ → List FiniteCouplingGenealogy
  | 0 => []
  | j + 1 =>
      if (finiteCouplingStage roots p q r w j).toState.emit p q r (w (0, j)) then
        recordedMiddleHistory roots p q r w j ++
          [(finiteCouplingStage roots p q r w (j + 1)).middle.chronological]
      else recordedMiddleHistory roots p q r w j

theorem recordedMiddleHistory_length (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) :
    (recordedMiddleHistory roots p q r w j).length = correctedCouplingClock roots p q r w j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [recordedMiddleHistory, correctedCouplingClock_succ]
      rw [finiteCouplingStage_toState]
      cases (correctedCouplingStage roots p q r w j).emit p q r (w (0, j)) <;> simp [ih]

theorem measurable_recordedMiddleHistory (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (j : ℕ) :
    Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦ recordedMiddleHistory roots p q r w j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
      let F : (FiniteCouplingState × FiniteCouplingState × List FiniteCouplingGenealogy) × ℝ →
          List FiniteCouplingGenealogy := fun z ↦
        if z.1.1.toState.emit p q r z.2 then z.1.2.2 ++ [z.1.2.1.middle.chronological]
        else z.1.2.2
      have hF : Measurable F := by
        apply measurable_from_prod_countable_right
        intro s
        change Measurable (fun u : ℝ ↦ if s.1.toState.emit p q r u then
          s.2.2 ++ [s.2.1.middle.chronological] else s.2.2)
        exact measurable_const.ite
          ((s.1.measurable_emit p q r) (measurableSet_singleton true)) measurable_const
      exact hF.comp
        (((measurable_finiteCouplingStage roots p q r j).prodMk
          ((measurable_finiteCouplingStage roots p q r (j + 1)).prodMk ih)).prodMk
            (measurable_pi_apply (0, j)))

theorem recordedMiddleHistory_congr_prefix (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (j : ℕ) {w z : (Fin 2 × ℕ) → ℝ}
    (h : ∀ i, i.2 < j → w i = z i) :
    recordedMiddleHistory roots p q r w j = recordedMiddleHistory roots p q r z j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hs := finiteCouplingStage_congr_prefix roots p q r j
        (fun i hi ↦ h i (by omega))
      have hnext := finiteCouplingStage_congr_prefix roots p q r (j + 1) h
      have hprev := ih (fun i hi ↦ h i (by omega))
      simp only [recordedMiddleHistory, hs, hnext, hprev, h (0, j) (by simp)]

noncomputable def recordedHistoryEvent (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (k j : ℕ) (history : List FiniteCouplingGenealogy)
    (s : FiniteCouplingState) : Set ((Fin 2 × ℕ) → ℝ) :=
  {w | couplingLogicalHit roots p q r w k j ∧
    recordedMiddleHistory roots p q r w j = history ∧ finiteCouplingStage roots p q r w j = s}

theorem measurableSet_recordedHistoryEvent (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (k j : ℕ) (history : List FiniteCouplingGenealogy)
    (s : FiniteCouplingState) : MeasurableSet (recordedHistoryEvent roots p q r k j history s) :=
  (measurableSet_couplingLogicalHit roots p q r k j).inter
    (((measurable_recordedMiddleHistory roots p q r j) (measurableSet_singleton history)).inter
      ((measurable_finiteCouplingStage roots p q r j) (measurableSet_singleton s)))

theorem recordedHistoryEvent_congr_prefix (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (k j : ℕ) (history : List FiniteCouplingGenealogy)
    (s : FiniteCouplingState) (w z : (Fin 2 × ℕ) → ℝ)
    (h : ∀ i, i.2 < j → w i = z i) :
    w ∈ recordedHistoryEvent roots p q r k j history s ↔
      z ∈ recordedHistoryEvent roots p q r k j history s := by
  simp only [recordedHistoryEvent, Set.mem_ofPred_eq,
    couplingLogicalHit_congr_prefix roots p q r k j h,
    recordedMiddleHistory_congr_prefix roots p q r j h,
    finiteCouplingStage_congr_prefix roots p q r j h]

/-- The rejection law is valid after a specified full recorded history,
with its measurability and causality discharged by the physical construction. -/
theorem upperPast_first_accepted_on_history
    (N : ℕ) (hN : 0 < N) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (q : ℝ) (r : List Bool → ℝ) (k j : ℕ)
    (history : List FiniteCouplingGenealogy) (s : FiniteCouplingState)
    (A : Finset ℕ) (hA : A.Nonempty) (hAs : A ⊆ s.upper.1.carrier.active)
    {v : ℕ} (hv : v ∈ A) (D : Set ℝ) (hD : MeasurableSet D) :
    let H := recordedHistoryEvent (Finset.range N) p q r k j history s
    pairedUniformLaw (⋃ n, {w | upperPastPending A (Finset.range N) hA p j H w n = true ∧
      selectFinite ((upperCarrier (Finset.range N) p w (j + n)).active ∪ A)
        (hA.mono Finset.subset_union_right) (w (0, j + n)) = v ∧ w (1, j + n) ∈ D}) =
      (A.card : ℝ≥0∞)⁻¹ * pairedUniformLaw H * unitUniform D := by
  let roots := Finset.range N
  let H := recordedHistoryEvent roots p q r k j history s
  have hinit (w : (Fin 2 × ℕ) → ℝ) (hw : w ∈ H) : A ⊆ (upperCarrier roots p w j).active := by
    have hs : finiteCouplingStage roots p q r w j = s := hw.2.2
    have he : (finiteCouplingStage roots p q r w j).upper.1.carrier.active =
        (upperCarrier roots p w j).active := by
      calc
        _ = (correctedCouplingStage roots p q r w j).trees.upper.carrier.active :=
          congrArg (fun t : CorrectedCouplingState ↦ t.trees.upper.carrier.active)
            (finiteCouplingStage_toState roots p q r w j)
        _ = (upperStage roots p w j).carrier.active := by
          rw [correctedCouplingStage_upper_eq_upperStage]
        _ = _ := congrArg CouplingCarrier.active (upperStage_carrier_eq_upperCarrier roots p w j)
    rw [← he, hs]
    exact hAs
  exact upperPast_first_accepted_joint_law N hN hp hp1 j H
    (measurableSet_recordedHistoryEvent roots p q r k j history s)
    (recordedHistoryEvent_congr_prefix roots p q r k j history s) A hA hinit hv D hD

end HeightPaper.CountCoupling
