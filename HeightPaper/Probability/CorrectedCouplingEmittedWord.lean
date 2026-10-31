module

public import HeightPaper.Probability.CorrectedCouplingClock
public import HeightPaper.Probability.CorrectedCouplingSourceEvent

/-!
# The infinite word emitted by the physical construction

A coherent increasing sequence of finite words determines its infinite word
whenever its lengths are unbounded. The totalized construction is measurable
on all paths, including the null set where that condition fails.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

theorem word_index_exists (W : ℕ → List Bool) (k : ℕ) :
    ∃ j, k < (W j).length ∨ (¬ (∃ i, k < (W i).length)) ∧ j = 0 := by
  by_cases h : ∃ j, k < (W j).length
  · obtain ⟨j, hj⟩ := h
    exact ⟨j, Or.inl hj⟩
  · exact ⟨0, Or.inr ⟨h, rfl⟩⟩

noncomputable def firstLongWord (W : ℕ → List Bool) (k : ℕ) : ℕ := by
  classical
  exact Nat.find (word_index_exists W k)

theorem firstLongWord_spec (W : ℕ → List Bool) (k : ℕ)
    (h : ∃ j, k < (W j).length) : k < (W (firstLongWord W k)).length := by
  classical
  have hs := Nat.find_spec (word_index_exists W k)
  rcases hs with hs | hs
  · exact hs
  · exact False.elim (hs.1 h)

theorem measurable_firstLongWord (k : ℕ) :
    Measurable (fun W : ℕ → List Bool ↦ firstLongWord W k) := by
  classical
  have hj (j : ℕ) : MeasurableSet {W : ℕ → List Bool | k < (W j).length} :=
    measurableSet_lt measurable_const
      ((measurable_of_countable List.length).comp (measurable_pi_apply j))
  have hex : MeasurableSet {W : ℕ → List Bool | ∃ j, k < (W j).length} := by
    simpa only [Set.ofPred_exists] using MeasurableSet.iUnion hj
  exact measurable_find (fun W ↦ word_index_exists W k)
    (fun j ↦ (hj j).union (hex.compl.inter (MeasurableSet.const (j = 0))))

noncomputable def coherentLimitWord (W : ℕ → List Bool) (k : ℕ) : Bool :=
  (W (firstLongWord W k)).getD k false

theorem measurable_coherentLimitWord :
    Measurable (coherentLimitWord : (ℕ → List Bool) → ℕ → Bool) := by
  apply measurable_pi_iff.mpr
  intro k
  have hsel : Measurable (fun z : ℕ × (ℕ → List Bool) ↦ (z.2 z.1).getD k false) :=
    measurable_from_prod_countable_right (fun j ↦
      (measurable_of_countable (fun w : List Bool ↦ w.getD k false)).comp
        (measurable_pi_apply j))
  exact hsel.comp ((measurable_firstLongWord k).prodMk measurable_id)

theorem coherentLimitWord_getD
    (W : ℕ → List Bool)
    (hprefix : ∀ i j, i ≤ j → W i <+: W j)
    (hunbounded : ∀ k, ∃ j, k < (W j).length)
    (j k : ℕ) (hk : k < (W j).length) :
    (W j).getD k false = coherentLimitWord W k := by
  have hi := firstLongWord_spec W k (hunbounded k)
  change (W j).getD k false = (W (firstLongWord W k)).getD k false
  rcases le_total j (firstLongWord W k) with hle | hle
  · obtain ⟨t, ht⟩ := hprefix _ _ hle
    rw [← ht]
    exact (List.getD_append _ _ _ _ hk).symm
  · obtain ⟨t, ht⟩ := hprefix _ _ hle
    rw [← ht]
    exact List.getD_append _ _ _ _ hi

theorem sourceCouplingPrefix_coherentLimitWord
    (W : ℕ → List Bool)
    (hprefix : ∀ i j, i ≤ j → W i <+: W j)
    (hunbounded : ∀ k, ∃ j, k < (W j).length) (j : ℕ) :
    sourceCouplingPrefix (coherentLimitWord W) (W j).length = W j := by
  apply List.ext_getElem (sourceCouplingPrefix_length _ _)
  intro k _ hk
  have h := coherentLimitWord_getD W hprefix hunbounded j k hk
  rw [List.getD_eq_getElem _ _ hk] at h
  simpa [sourceCouplingPrefix] using h.symm

noncomputable def correctedCouplingEmittedWord (roots : Finset ℕ)
    (p q : ℝ) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) : ℕ → Bool :=
  coherentLimitWord (fun j ↦ (correctedCouplingStage roots p q r w j).word)

theorem measurable_correctedCouplingEmittedWord (roots : Finset ℕ)
    (p q : ℝ) (r : List Bool → ℝ) :
    Measurable (correctedCouplingEmittedWord roots p q r) := by
  apply measurable_coherentLimitWord.comp
  apply measurable_pi_iff.mpr
  intro j
  have h := (measurable_of_countable (fun s : FiniteCouplingState ↦ s.word)).comp
    (measurable_finiteCouplingStage roots p q r j)
  have heq (w : (Fin 2 × ℕ) → ℝ) :
      (finiteCouplingStage roots p q r w j).word =
        (correctedCouplingStage roots p q r w j).word :=
    congrArg CorrectedCouplingState.word (finiteCouplingStage_toState roots p q r w j)
  simpa only [Function.comp_def, heq] using h

theorem sourceCouplingPrefix_correctedCouplingEmittedWord
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ k, ∃ j, k < correctedCouplingClock roots p q r w j)
    (j : ℕ) :
    sourceCouplingPrefix (correctedCouplingEmittedWord roots p q r w)
        (correctedCouplingClock roots p q r w j) =
      (correctedCouplingStage roots p q r w j).word :=
  sourceCouplingPrefix_coherentLimitWord _
    (fun _ _ hij ↦ correctedCouplingStage_word_prefix_of_le roots p q r w hij)
    hunbounded j

theorem correctedCouplingEmittedWord_at_emission
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ k, ∃ j, k < correctedCouplingClock roots p q r w j)
    (j : ℕ)
    (hemit : (correctedCouplingStage roots p q r w j).emit p q r (w (0, j)) = true) :
    correctedCouplingEmittedWord roots p q r w (correctedCouplingClock roots p q r w j) =
      recoveryThresholdBirth (r (correctedCouplingStage roots p q r w j).word) (w (1, j)) := by
  let W := fun i ↦ (correctedCouplingStage roots p q r w i).word
  have hstep : W (j + 1) = W j ++
      [recoveryThresholdBirth (r (correctedCouplingStage roots p q r w j).word) (w (1, j))] := by
    exact (CorrectedCouplingState.word_step _ p q r (w (0, j)) (w (1, j))).trans
      (by simp [hemit, W])
  have hlen : (W j).length < (W (j + 1)).length := by rw [hstep]; simp
  have he := coherentLimitWord_getD W
    (fun _ _ hij ↦ correctedCouplingStage_word_prefix_of_le roots p q r w hij)
    hunbounded (j + 1) (W j).length hlen
  rw [hstep, List.getD_append_right _ _ _ _ (le_refl _)] at he
  simpa [correctedCouplingEmittedWord, correctedCouplingClock, W] using he.symm

end HeightPaper.CountCoupling
