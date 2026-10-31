module

public import HeightPaper.Probability.CorrectedCouplingEmittedWord
public import HeightPaper.Probability.CorrectedCouplingStageStructure
public import Mathlib.Data.List.Induction

/-!
# The absorbed middle count and the source good event

Unlike the prescribed natural walk, this count cannot restart after zero.
It identifies the active cardinality throughout the physical time change.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

def absorbedActiveStep (n : ℕ) (b : Bool) : ℕ :=
  if n = 0 then 0 else if b then n + 1 else n - 1

def absorbedActiveCount (N : ℕ) (w : List Bool) : ℕ :=
  w.foldl absorbedActiveStep N

@[simp] theorem absorbedActiveCount_nil (N : ℕ) : absorbedActiveCount N [] = N := rfl

theorem absorbedActiveCount_append_singleton (N : ℕ) (w : List Bool) (b : Bool) :
    absorbedActiveCount N (w ++ [b]) = absorbedActiveStep (absorbedActiveCount N w) b := by
  simp [absorbedActiveCount]

/-- A positive absorbed count implies positivity of every preceding raw
count and identifies the current natural count with its integer version. -/
theorem absorbedActiveCount_pos_raw (N : ℕ) (w : List Bool)
    (hpos : 0 < absorbedActiveCount N w) :
    (absorbedActiveCount N w : ℤ) = couplingActiveCount N w ∧
      ∀ j ≤ w.length, 0 < couplingActiveCount N (w.take j) := by
  induction w using List.reverseRecOn with
  | nil =>
      constructor
      · rfl
      · intro j hj
        have hj0 : j = 0 := by simpa using hj
        subst j
        simpa using (show (0 : ℤ) < (N : ℤ) by exact_mod_cast hpos)
  | append_singleton w b ih =>
      have hp : 0 < absorbedActiveCount N w := by
        by_contra h
        have hz : absorbedActiveCount N w = 0 := by omega
        simp [absorbedActiveCount_append_singleton, absorbedActiveStep, hz] at hpos
      obtain ⟨hcast, hprefix⟩ := ih hp
      have hcast' : (absorbedActiveCount N (w ++ [b]) : ℤ) =
          couplingActiveCount N (w ++ [b]) := by
        rw [absorbedActiveCount_append_singleton, couplingActiveCount_append_singleton]
        cases b <;> simp [absorbedActiveStep, hp.ne',
          Nat.cast_sub (show 1 ≤ absorbedActiveCount N w by omega), hcast]
      refine ⟨hcast', ?_⟩
      intro j hj
      by_cases hjw : j ≤ w.length
      · simpa [List.take_append, Nat.sub_eq_zero_of_le hjw] using hprefix j hjw
      · have hje : j = (w ++ [b]).length := by
          simp only [List.length_append, List.length_singleton] at *
          omega
        rw [hje, List.take_length]
        rw [← hcast']
        exact_mod_cast hpos

theorem CorrectedCouplingState.middle_card_word_step
    (s : CorrectedCouplingState) (N : ℕ)
    (hs : s.trees.middle.carrier.active.card = absorbedActiveCount N s.word)
    (hf : s.faithful = true → s.trees.Ordered)
    (p q : ℝ) (r : List Bool → ℝ) (u recovery : ℝ) :
    (s.step p q r u recovery).trees.middle.carrier.active.card =
      absorbedActiveCount N (s.step p q r u recovery).word := by
  by_cases hg : s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q
  · by_cases hu : s.trees.upper.carrier.active.Nonempty
    · let v := s.trees.upper.selectedActive hu u
      by_cases hm : v ∈ s.trees.middle.carrier.active
      · have hfr : s.trees.upper.fresh ∉ s.trees.middle.carrier.vertices :=
          fun hx ↦ s.trees.upper.fresh_not_mem ((hf hg.1).2.1.1 hx)
        have hc := s.trees.middle.active_card_update v s.trees.upper.fresh hm hfr
          (recoveryThresholdBirth (r s.word) recovery)
        have hn : s.trees.middle.carrier.active.card ≠ 0 :=
          (Finset.card_pos.mpr ⟨v, hm⟩).ne'
        simpa [CorrectedCouplingState.step, hg, hu, CouplingTriple.step,
          absorbedActiveCount_append_singleton, absorbedActiveStep, ← hs, v, hm, hn] using hc
      · simpa [CorrectedCouplingState.step, hg, hu, CouplingTriple.step,
          CouplingGenealogy.update, CouplingCarrier.update, v, hm] using hs
    · have heu := Finset.not_nonempty_iff_eq_empty.mp hu
      have hem : s.trees.middle.carrier.active = ∅ := by
        apply Finset.subset_empty.mp
        simpa [heu] using (hf hg.1).2.1.2
      have hz : absorbedActiveCount N s.word = 0 := by rw [← hs, hem]; rfl
      simp [CorrectedCouplingState.step, hg, hu, hem,
        absorbedActiveCount_append_singleton, absorbedActiveStep, hz]
  · by_cases hm : s.trees.middle.carrier.active.Nonempty
    · let v := s.trees.middle.selectedActive hm u
      have hv := s.trees.middle.selectedActive_mem hm u
      have hc := s.trees.middle.active_card_update v s.trees.middle.fresh hv
        s.trees.middle.fresh_not_mem (recoveryThresholdBirth (r s.word) recovery)
      have hn : s.trees.middle.carrier.active.card ≠ 0 := hm.card_pos.ne'
      simpa [CorrectedCouplingState.step, hg, hm, v,
        absorbedActiveCount_append_singleton, absorbedActiveStep, ← hs, hn] using hc
    · have hem := Finset.not_nonempty_iff_eq_empty.mp hm
      have hz : absorbedActiveCount N s.word = 0 := by rw [← hs, hem]; rfl
      simp [CorrectedCouplingState.step, hg, hem,
        CouplingGenealogy.update, CouplingCarrier.update,
        absorbedActiveCount_append_singleton, absorbedActiveStep, hz]

theorem correctedCouplingStage_middle_card_word
    (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) :
    (correctedCouplingStage (Finset.range N) p q r w j).trees.middle.carrier.active.card =
      absorbedActiveCount N (correctedCouplingStage (Finset.range N) p q r w j).word := by
  induction j with
  | zero => simp [correctedCouplingStage, CorrectedCouplingState.initial,
      CouplingTriple.initial, CouplingGenealogy.initial]
  | succ j ih =>
      exact CorrectedCouplingState.middle_card_word_step _ N ih
        (correctedCouplingStage_faithful_ordered _ p q r w j)
        p q r (w (0, j)) (w (1, j))

theorem sourceCouplingPrefix_take (x : ℕ → Bool) {j k : ℕ} (hjk : j ≤ k) :
    (sourceCouplingPrefix x k).take j = sourceCouplingPrefix x j := by
  apply List.ext_getElem
  · simp [sourceCouplingPrefix_length, Nat.min_eq_left hjk]
  · intro i _ _
    simp [sourceCouplingPrefix]

/-- The good event on the emitted source word supplies all physical rate
bounds while the middle is active, including the terminal recovery. -/
theorem correctedCouplingStage_bounds_of_sourceGood
    (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ k, ∃ j, k < correctedCouplingClock (Finset.range N) p q r w j)
    (hgood : sourceCorrectedGood N p q r
      (correctedCouplingEmittedWord (Finset.range N) p q r w))
    (j : ℕ)
    (hm : (correctedCouplingStage (Finset.range N) p q r w j).trees.middle.carrier.active.Nonempty) :
    p ≤ r (correctedCouplingStage (Finset.range N) p q r w j).word ∧
      r (correctedCouplingStage (Finset.range N) p q r w j).word ≤ q := by
  let s := correctedCouplingStage (Finset.range N) p q r w j
  let x := correctedCouplingEmittedWord (Finset.range N) p q r w
  have hword : sourceCouplingPrefix x s.word.length = s.word :=
    sourceCouplingPrefix_correctedCouplingEmittedWord _ p q r w hunbounded j
  have hcount : 0 < absorbedActiveCount N s.word := by
    rw [← correctedCouplingStage_middle_card_word N p q r w j]
    exact hm.card_pos
  have hraw := (absorbedActiveCount_pos_raw N s.word hcount).2
  have hb := hgood s.word.length (fun i hi ↦ by
    have ht : s.word.take i = sourceCouplingPrefix x i := by
      rw [← hword]
      exact sourceCouplingPrefix_take x hi
    rw [← ht]
    exact hraw i hi)
  change p ≤ r s.word ∧ r s.word ≤ q
  change p ≤ r (sourceCouplingPrefix x s.word.length) ∧
    r (sourceCouplingPrefix x s.word.length) ≤ q at hb
  rwa [hword] at hb

theorem correctedCouplingStage_ordered_of_sourceGood
    (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ k, ∃ j, k < correctedCouplingClock (Finset.range N) p q r w j)
    (hgood : sourceCorrectedGood N p q r
      (correctedCouplingEmittedWord (Finset.range N) p q r w)) (j : ℕ) :
    (correctedCouplingStage (Finset.range N) p q r w j).trees.Ordered :=
  correctedCouplingStage_ordered_of_active_bounds _ p q r w
    (correctedCouplingStage_bounds_of_sourceGood N p q r w hunbounded hgood) j

end HeightPaper.CountCoupling
