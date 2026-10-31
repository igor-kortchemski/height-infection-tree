module

public import HeightPaper.Probability.CorrectedCouplingJointHistory

/-!
# Joint logical prefixes and their causal physical partitions
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace HeightPaper.CountCoupling

def couplingTokenPrefix (x : ℕ → CouplingToken) (k : ℕ) : List CouplingToken :=
  List.ofFn (fun i : Fin k ↦ x i)

@[simp] theorem couplingTokenPrefix_length (x : ℕ → CouplingToken) (k : ℕ) :
    (couplingTokenPrefix x k).length = k := by simp [couplingTokenPrefix]

@[simp] theorem couplingTokenPrefix_zero (x : ℕ → CouplingToken) : couplingTokenPrefix x 0 = [] := rfl

theorem couplingTokenPrefix_succ (x : ℕ → CouplingToken) (k : ℕ) :
    couplingTokenPrefix x (k + 1) = couplingTokenPrefix x k ++ [x k] := by
  unfold couplingTokenPrefix
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

theorem measurable_couplingTokenPrefix (k : ℕ) : Measurable (fun x ↦ couplingTokenPrefix x k) := by
  have hm : Measurable (fun x : ℕ → CouplingToken ↦ fun i : Fin k ↦ x i.val) :=
    measurable_pi_iff.mpr (fun i ↦ measurable_pi_apply i.val)
  exact (measurable_of_countable (fun f : Fin k → CouplingToken ↦ List.ofFn f)).comp hm

theorem recordedJointHistory_eq_tokenPrefix
    (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hu : ∀ k, ∃ j, k < correctedCouplingClock (Finset.range N) p q r w j) (j : ℕ) :
    recordedJointHistory (Finset.range N) p q r w j =
      couplingTokenPrefix (correctedCouplingLogicalToken N p q r w)
        (correctedCouplingClock (Finset.range N) p q r w j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hs := congrArg CorrectedCouplingState.word
        (finiteCouplingStage_toState (Finset.range N) p q r w j)
      change (finiteCouplingStage (Finset.range N) p q r w j).word =
        (correctedCouplingStage (Finset.range N) p q r w j).word at hs
      rw [recordedJointHistory, finiteCouplingStage_toState, correctedCouplingClock_succ]
      cases he : (correctedCouplingStage (Finset.range N) p q r w j).emit p q r (w (0, j))
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, ih]
      · simp only [↓reduceIte, couplingTokenPrefix_succ, ih,
          correctedCouplingLogicalToken_at_emission N p q r w hu j he, hs]

noncomputable def jointPrefixEvent (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (h : List CouplingToken) : Set ((Fin 2 × ℕ) → ℝ) :=
  {w | couplingTokenPrefix (correctedCouplingLogicalToken N p q r w) h.length = h}

theorem measurableSet_jointPrefixEvent (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (h : List CouplingToken) : MeasurableSet (jointPrefixEvent N p q r h) :=
  ((measurable_couplingTokenPrefix h.length).comp
    (measurable_pi_iff.mpr (measurable_correctedCouplingLogicalToken N p q r)))
      (measurableSet_singleton h)

noncomputable def jointHistoryEvent (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (h : List CouplingToken) (a : ℕ × FiniteCouplingState) : Set ((Fin 2 × ℕ) → ℝ) :=
  {w | couplingLogicalHit (Finset.range N) p q r w h.length a.1 ∧
    recordedJointHistory (Finset.range N) p q r w a.1 = h ∧
    finiteCouplingStage (Finset.range N) p q r w a.1 = a.2}

theorem measurableSet_jointHistoryEvent (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (h : List CouplingToken) (a : ℕ × FiniteCouplingState) :
    MeasurableSet (jointHistoryEvent N p q r h a) :=
  (measurableSet_couplingLogicalHit (Finset.range N) p q r h.length a.1).inter
    (((measurable_recordedJointHistory (Finset.range N) p q r a.1) (measurableSet_singleton h)).inter
      ((measurable_finiteCouplingStage (Finset.range N) p q r a.1) (measurableSet_singleton a.2)))

theorem jointHistoryEvent_congr_prefix (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (h : List CouplingToken) (a : ℕ × FiniteCouplingState) (w z : (Fin 2 × ℕ) → ℝ)
    (hh : ∀ i, i.2 < a.1 → w i = z i) :
    w ∈ jointHistoryEvent N p q r h a ↔ z ∈ jointHistoryEvent N p q r h a := by
  simp only [jointHistoryEvent, Set.mem_ofPred_eq,
    couplingLogicalHit_congr_prefix (Finset.range N) p q r h.length a.1 hh,
    recordedJointHistory_congr_prefix (Finset.range N) p q r a.1 hh,
    finiteCouplingStage_congr_prefix (Finset.range N) p q r a.1 hh]

theorem jointHistoryEvent_pairwise (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (h : List CouplingToken) : Pairwise (Disjoint on jointHistoryEvent N p q r h) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro w ha hb
  have htime : a.1 = b.1 := by
    rcases lt_trichotomy a.1 b.1 with hlt | he | hgt
    · have := hb.1.2 a.1 hlt
      rw [ha.1.1] at this
      exact False.elim ((Nat.lt_irrefl _) this)
    · exact he
    · have := ha.1.2 b.1 hgt
      rw [hb.1.1] at this
      exact False.elim ((Nat.lt_irrefl _) this)
  have hstate : a.2 = b.2 := by rw [← ha.2.2, ← hb.2.2, htime]
  exact hab (Prod.ext htime hstate)

theorem jointHistoryEvent_ae_cover
    (N : ℕ) (hN : 0 < N) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (q : ℝ) (r : List Bool → ℝ) (h : List CouplingToken) :
    (⋃ a, jointHistoryEvent N p q r h a) =ᵐ[pairedUniformLaw] jointPrefixEvent N p q r h := by
  filter_upwards [correctedCouplingClock_ae_unbounded N hN hp hp1 q r] with w hu
  apply propext
  simp only [Set.mem_iUnion, jointPrefixEvent, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha⟩
    rw [← ha.1.1, ← recordedJointHistory_eq_tokenPrefix N p q r w hu a.1]
    exact ha.2.1
  · intro hh
    let j := couplingLogicalTime (Finset.range N) p q r w h.length
    have hhit := (couplingLogicalTime_eq_iff_hit (Finset.range N) p q r w hu h.length j).mp rfl
    refine ⟨(j, finiteCouplingStage (Finset.range N) p q r w j), hhit, ?_, rfl⟩
    rw [recordedJointHistory_eq_tokenPrefix N p q r w hu j, hhit.1]
    exact hh

theorem jointHistoryEvent_state
    (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) (h : List CouplingToken)
    (a : ℕ × FiniteCouplingState) (w : (Fin 2 × ℕ) → ℝ)
    (hw : w ∈ jointHistoryEvent N p q r h a) :
    a.2.word.length = h.length ∧ a.2.word = jointHistoryWord h ∧
      a.2.middle.chronological = jointHistoryForest (Finset.range N) h := by
  have hs := congrArg CorrectedCouplingState.word
    (finiteCouplingStage_toState (Finset.range N) p q r w a.1)
  change (finiteCouplingStage (Finset.range N) p q r w a.1).word =
    (correctedCouplingStage (Finset.range N) p q r w a.1).word at hs
  have hwrd := recordedJointHistory_word (Finset.range N) p q r w a.1
  have hfr := recordedJointHistory_forest N p q r w a.1
  rw [hw.2.1] at hwrd hfr
  rw [hw.2.2] at hs hfr
  exact ⟨(congrArg List.length hs).trans hw.1.1, hs.trans hwrd.symm, hfr.symm⟩

end HeightPaper.CountCoupling
