module

public import HeightPaper.Probability.CorrectedCouplingSourceForest
public import HeightPaper.Probability.CorrectedCouplingEmittedLaw

/-!
# The measurable middle forest at logical event times

The sampled forest has dense chronological labels and the recorded word is
the corresponding prefix of the emitted process. Equality of its joint law
with `sourceForestTrajectory` remains a stochastic identification obligation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

theorem firstLongWord_eq_iff (W : ℕ → List Bool) (k j : ℕ)
    (hex : ∃ i, k < (W i).length) :
    firstLongWord W k = j ↔ k < (W j).length ∧ ∀ i < j, (W i).length ≤ k := by
  classical
  unfold firstLongWord
  rw [Nat.find_eq_iff]
  simp only [hex, not_true_eq_false, false_and, or_false, not_lt]

noncomputable def couplingLogicalTime (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => firstLongWord (fun j ↦ (correctedCouplingStage roots p q r w j).word) k

theorem correctedCouplingClock_le_time (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) :
    correctedCouplingClock roots p q r w j ≤ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [correctedCouplingClock_succ]
      cases (correctedCouplingStage roots p q r w j).emit p q r (w (0, j)) <;>
        simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem correctedCouplingClock_firstLongWord (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) (k : ℕ)
    (h : ∃ j, k < correctedCouplingClock roots p q r w j) :
    correctedCouplingClock roots p q r w
      (firstLongWord (fun j ↦ (correctedCouplingStage roots p q r w j).word) k) = k + 1 := by
  let W := fun j ↦ (correctedCouplingStage roots p q r w j).word
  have hgt := firstLongWord_spec W k h
  cases ht : firstLongWord W k with
  | zero => simp [ht, W, correctedCouplingStage, CorrectedCouplingState.initial] at hgt
  | succ j =>
      have hle := firstLongWord_min W k (show j < firstLongWord W k by rw [ht]; omega)
      change correctedCouplingClock roots p q r w j ≤ k at hle
      have hgt' : k < correctedCouplingClock roots p q r w (j + 1) := by
        simpa only [ht, W, correctedCouplingClock] using hgt
      have hs := correctedCouplingClock_succ roots p q r w j
      have hupper : correctedCouplingClock roots p q r w (j + 1) ≤
          correctedCouplingClock roots p q r w j + 1 := by
        rw [hs]
        cases (correctedCouplingStage roots p q r w j).emit p q r (w (0, j)) <;> simp
      omega

theorem couplingLogicalTime_clock (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ k, ∃ j, k < correctedCouplingClock roots p q r w j) (k : ℕ) :
    correctedCouplingClock roots p q r w (couplingLogicalTime roots p q r w k) = k := by
  cases k with
  | zero => rfl
  | succ k => exact correctedCouplingClock_firstLongWord roots p q r w k (hunbounded k)

noncomputable def couplingLogicalHit (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) (k j : ℕ) : Prop :=
  correctedCouplingClock roots p q r w j = k ∧
    ∀ i < j, correctedCouplingClock roots p q r w i < k

theorem measurableSet_couplingLogicalHit (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (k j : ℕ) :
    MeasurableSet {w | couplingLogicalHit roots p q r w k j} := by
  simp only [couplingLogicalHit, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · exact (measurable_correctedCouplingClock roots p q r j) (measurableSet_singleton k)
  · apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_lt (measurable_correctedCouplingClock roots p q r i) measurable_const

theorem correctedCouplingStage_congr_prefix (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (j : ℕ) {w z : (Fin 2 × ℕ) → ℝ}
    (h : ∀ i, i.2 < j → w i = z i) :
    correctedCouplingStage roots p q r w j = correctedCouplingStage roots p q r z j :=
  (finiteCouplingStage_toState roots p q r w j).symm.trans
    ((congrArg FiniteCouplingState.toState (finiteCouplingStage_congr_prefix roots p q r j h)).trans
      (finiteCouplingStage_toState roots p q r z j))

theorem couplingLogicalHit_congr_prefix (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (k j : ℕ) {w z : (Fin 2 × ℕ) → ℝ}
    (h : ∀ i, i.2 < j → w i = z i) :
    couplingLogicalHit roots p q r w k j ↔ couplingLogicalHit roots p q r z k j := by
  have hc (i : ℕ) (hi : i ≤ j) : correctedCouplingClock roots p q r w i =
      correctedCouplingClock roots p q r z i :=
    congrArg (fun s : CorrectedCouplingState ↦ s.word.length)
      (correctedCouplingStage_congr_prefix roots p q r i (fun a ha ↦ h a (ha.trans_le hi)))
  constructor
  · rintro ⟨hj, hprev⟩
    exact ⟨(hc j le_rfl).symm.trans hj, fun i hi ↦ by rw [← hc i hi.le]; exact hprev i hi⟩
  · rintro ⟨hj, hprev⟩
    exact ⟨(hc j le_rfl).trans hj, fun i hi ↦ by rw [hc i hi.le]; exact hprev i hi⟩

/-- On unbounded-clock paths, first passage is a causal finite-prefix event.
No causality is claimed for the arbitrary default on non-passage paths. -/
theorem couplingLogicalTime_eq_iff_hit (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ k, ∃ j, k < correctedCouplingClock roots p q r w j) (k j : ℕ) :
    couplingLogicalTime roots p q r w k = j ↔ couplingLogicalHit roots p q r w k j := by
  cases k with
  | zero =>
      constructor
      · intro h
        have hj : j = 0 := h.symm
        subst j
        exact ⟨rfl, fun i hi ↦ False.elim (Nat.not_lt_zero i hi)⟩
      · rintro ⟨_, hprev⟩
        have hj : j = 0 := by
          by_contra hn
          have := hprev 0 (Nat.pos_of_ne_zero hn)
          exact Nat.not_lt_zero _ this
        subst j
        rfl
  | succ k =>
      have hf := firstLongWord_eq_iff
        (fun i ↦ (correctedCouplingStage roots p q r w i).word) k j (hunbounded k)
      constructor
      · intro ht
        have hparts := hf.mp ht
        refine ⟨?_, fun i hi ↦ ?_⟩
        · rw [← ht]
          exact couplingLogicalTime_clock roots p q r w hunbounded (k + 1)
        · have := hparts.2 i hi
          exact Nat.lt_succ_of_le this
      · rintro ⟨hclock, hprev⟩
        apply hf.mpr
        refine ⟨?_, fun i hi ↦ Nat.le_of_lt_succ (hprev i hi)⟩
        change k < correctedCouplingClock roots p q r w j
        rw [hclock]
        omega

theorem couplingLogicalTime_ge (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ k, ∃ j, k < correctedCouplingClock roots p q r w j) (k : ℕ) :
    k ≤ couplingLogicalTime roots p q r w k := by
  have h := correctedCouplingClock_le_time roots p q r w
    (couplingLogicalTime roots p q r w k)
  rwa [couplingLogicalTime_clock roots p q r w hunbounded k] at h

theorem measurable_couplingLogicalTime (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (k : ℕ) :
    Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦ couplingLogicalTime roots p q r w k) := by
  cases k with
  | zero => exact measurable_const
  | succ k =>
      have hW : Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦
          fun j ↦ (correctedCouplingStage roots p q r w j).word) := by
        apply measurable_pi_iff.mpr
        intro j
        have h := (measurable_of_countable (fun s : FiniteCouplingState ↦ s.word)).comp
          (measurable_finiteCouplingStage roots p q r j)
        have heq (w : (Fin 2 × ℕ) → ℝ) :
            (finiteCouplingStage roots p q r w j).word =
              (correctedCouplingStage roots p q r w j).word :=
          congrArg CorrectedCouplingState.word (finiteCouplingStage_toState roots p q r w j)
        simpa only [Function.comp_def, heq] using h
      exact (measurable_firstLongWord k).comp hW

noncomputable def FiniteCouplingGenealogy.chronological (s : FiniteCouplingGenealogy) :
    FiniteCouplingGenealogy := ⟨s.1.chronological, s.1.chronological_normalized⟩

noncomputable def sampledMiddleForest (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) : FiniteCouplingGenealogy :=
  (finiteCouplingStage (Finset.range N) p q r w
    (couplingLogicalTime (Finset.range N) p q r w k)).middle.chronological

theorem sampledMiddleForest_initial (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) :
    sampledMiddleForest N p q r w 0 = FiniteCouplingGenealogy.initial (Finset.range N) := by
  apply Subtype.ext
  exact CouplingGenealogy.chronological_initial N

theorem sampledMiddleForest_dense (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) : (sampledMiddleForest N p q r w k).1.Dense :=
  CouplingGenealogy.chronological_dense _

theorem sampledMiddleForest_valid (N : ℕ) {p q : ℝ} (hpq : p ≤ q)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) :
    (sampledMiddleForest N p q r w k).1.Valid (Finset.range N) := by
  apply CouplingGenealogy.chronological_valid
  have h := (correctedCouplingStage_valid (Finset.range N) hpq r w
    (couplingLogicalTime (Finset.range N) p q r w k)).2.1
  rw [← finiteCouplingStage_toState] at h
  exact h

theorem measurable_sampledMiddleForest (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) :
    Measurable (sampledMiddleForest N p q r) := by
  apply measurable_pi_iff.mpr
  intro k
  have hstage : Measurable (fun z : ℕ × ((Fin 2 × ℕ) → ℝ) ↦
      finiteCouplingStage (Finset.range N) p q r z.2 z.1) :=
    measurable_from_prod_countable_right (measurable_finiteCouplingStage (Finset.range N) p q r)
  exact (measurable_of_countable (fun s : FiniteCouplingState ↦ s.middle.chronological)).comp
    (hstage.comp ((measurable_couplingLogicalTime (Finset.range N) p q r k).prodMk measurable_id))

theorem sampledMiddle_recorded_word (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ i, ∃ j, i < correctedCouplingClock (Finset.range N) p q r w j) (k : ℕ) :
    (finiteCouplingStage (Finset.range N) p q r w
      (couplingLogicalTime (Finset.range N) p q r w k)).word =
        sourceCouplingPrefix (correctedCouplingEmittedWord (Finset.range N) p q r w) k := by
  have hword := sourceCouplingPrefix_correctedCouplingEmittedWord (Finset.range N) p q r w
    hunbounded (couplingLogicalTime (Finset.range N) p q r w k)
  rw [couplingLogicalTime_clock _ p q r w hunbounded k, ← finiteCouplingStage_toState] at hword
  exact hword.symm

end HeightPaper.CountCoupling
