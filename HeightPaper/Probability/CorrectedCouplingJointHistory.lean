module

public import HeightPaper.Probability.CorrectedCouplingLogicalKernel

/-!
# Countable joint histories of emitted letters and entire forests

Recording the after-event forest together with each letter provides a causal
physical-time code for all finite-dimensional joint laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

abbrev CouplingToken := Bool × FiniteCouplingGenealogy

instance : MeasurableSpace (List CouplingToken) := ⊤

noncomputable def recordedJointHistory (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) : ℕ → List CouplingToken
  | 0 => []
  | j + 1 =>
      let s := finiteCouplingStage roots p q r w j
      if s.toState.emit p q r (w (0, j)) then
        recordedJointHistory roots p q r w j ++
          [(recoveryThresholdBirth (r s.word) (w (1, j)),
            (finiteCouplingStage roots p q r w (j + 1)).middle.chronological)]
      else recordedJointHistory roots p q r w j

def jointHistoryWord (h : List CouplingToken) : List Bool := h.map Prod.fst

noncomputable def jointHistoryForest (roots : Finset ℕ) (h : List CouplingToken) :
    FiniteCouplingGenealogy :=
  (h.map Prod.snd).getLastD (FiniteCouplingGenealogy.initial roots)

theorem recordedJointHistory_word (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) :
    jointHistoryWord (recordedJointHistory roots p q r w j) =
      (correctedCouplingStage roots p q r w j).word := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hs := congrArg CorrectedCouplingState.word (finiteCouplingStage_toState roots p q r w j)
      change (finiteCouplingStage roots p q r w j).word =
        (correctedCouplingStage roots p q r w j).word at hs
      change List.map Prod.fst (recordedJointHistory roots p q r w j) =
        (correctedCouplingStage roots p q r w j).word at ih
      rw [recordedJointHistory, finiteCouplingStage_toState]
      simp only [jointHistoryWord]
      change _ = ((correctedCouplingStage roots p q r w j).step p q r (w (0, j)) (w (1, j))).word
      rw [CorrectedCouplingState.word_step]
      cases he : (correctedCouplingStage roots p q r w j).emit p q r (w (0, j)) <;>
        simp only [Bool.false_eq_true, ↓reduceIte, List.map_append, List.map_cons,
          List.map_nil, ih, hs]

theorem recordedJointHistory_length (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) :
    (recordedJointHistory roots p q r w j).length = correctedCouplingClock roots p q r w j := by
  simpa only [jointHistoryWord, List.length_map, correctedCouplingClock] using
    congrArg List.length (recordedJointHistory_word roots p q r w j)

theorem recordedJointHistory_forest (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) :
    jointHistoryForest (Finset.range N) (recordedJointHistory (Finset.range N) p q r w j) =
      (finiteCouplingStage (Finset.range N) p q r w j).middle.chronological := by
  induction j with
  | zero =>
      apply Subtype.ext
      exact (CouplingGenealogy.chronological_initial N).symm
  | succ j ih =>
      rw [recordedJointHistory]
      cases he : (finiteCouplingStage (Finset.range N) p q r w j).toState.emit p q r (w (0, j))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih]
        apply Subtype.ext
        have hmid := CorrectedCouplingState.middle_eq_of_no_emission
          (correctedCouplingStage (Finset.range N) p q r w j) p q r (w (0, j)) (w (1, j))
          (by simpa only [finiteCouplingStage_toState] using he)
        have hnext := congrArg (fun t : CorrectedCouplingState ↦ t.trees.middle)
          (finiteCouplingStage_toState (Finset.range N) p q r w (j + 1))
        have hprev := congrArg (fun t : CorrectedCouplingState ↦ t.trees.middle)
          (finiteCouplingStage_toState (Finset.range N) p q r w j)
        exact (congrArg CouplingGenealogy.chronological
          (hnext.trans (hmid.trans hprev.symm))).symm
      · simp only [↓reduceIte, jointHistoryForest, List.map_append, List.map_cons, List.map_nil,
          List.getLastD_concat]

theorem measurable_recordedJointHistory (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (j : ℕ) :
    Measurable (fun w ↦ recordedJointHistory roots p q r w j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
      let F : (FiniteCouplingState × List CouplingToken) × (ℝ × ℝ) → List CouplingToken := fun z ↦
        if z.1.1.toState.emit p q r z.2.1 then z.1.2 ++
          [(recoveryThresholdBirth (r z.1.1.word) z.2.2,
            (z.1.1.step p q r z.2.1 z.2.2).middle.chronological)] else z.1.2
      have hF : Measurable F := by
        apply measurable_from_prod_countable_right
        intro sh
        change Measurable (fun z : ℝ × ℝ ↦
          if sh.1.toState.emit p q r z.1 then sh.2 ++
            [(recoveryThresholdBirth (r sh.1.word) z.2,
              (sh.1.step p q r z.1 z.2).middle.chronological)] else sh.2)
        have ht : Measurable (fun z : ℝ × ℝ ↦
            (recoveryThresholdBirth (r sh.1.word) z.2,
              (sh.1.step p q r z.1 z.2).middle.chronological)) :=
          ((measurable_recoveryThresholdBirth _).comp measurable_snd).prodMk
            ((measurable_of_countable (fun s : FiniteCouplingState ↦ s.middle.chronological)).comp
              (sh.1.measurable_step p q r))
        have ha : Measurable (fun z : ℝ × ℝ ↦ sh.2 ++
            [(recoveryThresholdBirth (r sh.1.word) z.2,
              (sh.1.step p q r z.1 z.2).middle.chronological)]) :=
          (measurable_of_countable (fun t : CouplingToken ↦ sh.2 ++ [t])).comp ht
        exact ha.ite (((sh.1.measurable_emit p q r).comp measurable_fst)
          (measurableSet_singleton true)) measurable_const
      exact hF.comp (((measurable_finiteCouplingStage roots p q r j).prodMk ih).prodMk
        ((measurable_pi_apply (0, j)).prodMk (measurable_pi_apply (1, j))))

theorem recordedJointHistory_congr_prefix (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (j : ℕ) {w z : (Fin 2 × ℕ) → ℝ}
    (h : ∀ i, i.2 < j → w i = z i) :
    recordedJointHistory roots p q r w j = recordedJointHistory roots p q r z j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hs := finiteCouplingStage_congr_prefix roots p q r j (fun i hi ↦ h i (by omega))
      have hn := finiteCouplingStage_congr_prefix roots p q r (j + 1) h
      simp only [recordedJointHistory, hs, hn, ih (fun i hi ↦ h i (by omega)),
        h (0, j) (by simp), h (1, j) (by simp)]

theorem recordedJointHistory_prefix (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) {i j : ℕ} (hij : i ≤ j) :
    recordedJointHistory roots p q r w i <+: recordedJointHistory roots p q r w j := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ j _ ih =>
      rw [recordedJointHistory]
      split
      · exact ih.trans (List.prefix_append _ _)
      · exact ih

end HeightPaper.CountCoupling
