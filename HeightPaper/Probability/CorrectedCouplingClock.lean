module

public import HeightPaper.Probability.CorrectedCouplingFiniteState

/-!
# Predictable emissions and the physical clock

Whether a letter is emitted is decided from the current state and the parent
uniform before the recovery draw is inspected. Upper extinction makes the
clock increase at every subsequent physical step.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

noncomputable def CorrectedCouplingState.emit
    (s : CorrectedCouplingState) (p q : ℝ) (r : List Bool → ℝ) (u : ℝ) : Bool :=
  if s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q then
    if hu : s.trees.upper.carrier.active.Nonempty then
      decide (s.trees.upper.selectedActive hu u ∈ s.trees.middle.carrier.active)
    else true
  else true

theorem CorrectedCouplingState.word_step
    (s : CorrectedCouplingState) (p q : ℝ) (r : List Bool → ℝ)
    (u recovery : ℝ) :
    (s.step p q r u recovery).word =
      if s.emit p q r u then
        s.word ++ [recoveryThresholdBirth (r s.word) recovery] else s.word := by
  by_cases hg : s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q
  · by_cases hu : s.trees.upper.carrier.active.Nonempty <;>
      simp [CorrectedCouplingState.step, CorrectedCouplingState.emit, hg, hu]
  · simp [CorrectedCouplingState.step, CorrectedCouplingState.emit, hg]

theorem CorrectedCouplingState.word_length_step
    (s : CorrectedCouplingState) (p q : ℝ) (r : List Bool → ℝ)
    (u recovery : ℝ) :
    (s.step p q r u recovery).word.length =
      s.word.length + if s.emit p q r u then 1 else 0 := by
  rw [s.word_step]
  cases s.emit p q r u <;> simp

theorem CorrectedCouplingState.word_prefix_step
    (s : CorrectedCouplingState) (p q : ℝ) (r : List Bool → ℝ)
    (u recovery : ℝ) : s.word <+: (s.step p q r u recovery).word := by
  rw [s.word_step]
  cases s.emit p q r u
  · exact ⟨[], by simp⟩
  · exact ⟨_, rfl⟩

theorem CorrectedCouplingState.middle_eq_of_no_emission
    (s : CorrectedCouplingState) (p q : ℝ) (r : List Bool → ℝ)
    (u recovery : ℝ) (he : s.emit p q r u = false) :
    (s.step p q r u recovery).trees.middle = s.trees.middle := by
  by_cases hg : s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q
  · by_cases hu : s.trees.upper.carrier.active.Nonempty
    · have hnot : s.trees.upper.selectedActive hu u ∉ s.trees.middle.carrier.active := by
        simpa [CorrectedCouplingState.emit, hg, hu] using he
      simp [CorrectedCouplingState.step, hg, hu, CouplingTriple.step,
        CouplingGenealogy.update, CouplingCarrier.update, hnot]
    · simp [CorrectedCouplingState.emit, hg, hu] at he
  · simp [CorrectedCouplingState.emit, hg] at he

theorem CorrectedCouplingState.emit_of_upper_empty
    (s : CorrectedCouplingState) (p q : ℝ) (r : List Bool → ℝ) (u : ℝ)
    (hu : s.trees.upper.carrier.active = ∅) : s.emit p q r u = true := by
  simp [CorrectedCouplingState.emit, hu]

theorem FiniteCouplingState.measurable_emit
    (s : FiniteCouplingState) (p q : ℝ) (r : List Bool → ℝ) :
    Measurable (fun u : ℝ ↦ s.toState.emit p q r u) := by
  by_cases hg : s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q
  · by_cases hu : s.upper.1.carrier.active.Nonempty
    · simpa [CorrectedCouplingState.emit, FiniteCouplingState.toState, hg, hu,
        Function.comp_def] using
        (measurable_of_countable
          (fun v : ℕ ↦ decide (v ∈ s.middle.1.carrier.active))).comp
          (s.upper.1.measurable_selectedActive hu)
    · simp [CorrectedCouplingState.emit, FiniteCouplingState.toState, hg, hu]
  · simp [CorrectedCouplingState.emit, FiniteCouplingState.toState, hg]

noncomputable def correctedCouplingClock (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) : ℕ :=
  (correctedCouplingStage roots p q r w j).word.length

theorem measurable_correctedCouplingClock
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ) (j : ℕ) :
    Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦ correctedCouplingClock roots p q r w j) := by
  have h := (measurable_of_countable (fun s : FiniteCouplingState ↦ s.word.length)).comp
    (measurable_finiteCouplingStage roots p q r j)
  have heq (w : (Fin 2 × ℕ) → ℝ) :
      (finiteCouplingStage roots p q r w j).word.length =
        correctedCouplingClock roots p q r w j :=
    congrArg (fun s : CorrectedCouplingState ↦ s.word.length)
      (finiteCouplingStage_toState roots p q r w j)
  simpa only [Function.comp_def, heq] using h

theorem correctedCouplingClock_succ
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) :
    correctedCouplingClock roots p q r w (j + 1) =
      correctedCouplingClock roots p q r w j +
        if (correctedCouplingStage roots p q r w j).emit p q r (w (0, j)) then 1 else 0 :=
  CorrectedCouplingState.word_length_step _ p q r (w (0, j)) (w (1, j))

theorem correctedCouplingClock_monotone
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) : Monotone (correctedCouplingClock roots p q r w) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [correctedCouplingClock_succ]
  exact Nat.le_add_right _ _

theorem correctedCouplingStage_word_prefix_of_le
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) {i j : ℕ} (hij : i ≤ j) :
    (correctedCouplingStage roots p q r w i).word <+:
      (correctedCouplingStage roots p q r w j).word := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ j _ ih =>
      exact ih.trans (CorrectedCouplingState.word_prefix_step _ p q r (w (0, j)) (w (1, j)))

theorem correctedCouplingStage_upper_empty_of_le
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) {i j : ℕ} (hij : i ≤ j)
    (hi : (correctedCouplingStage roots p q r w i).trees.upper.carrier.active = ∅) :
    (correctedCouplingStage roots p q r w j).trees.upper.carrier.active = ∅ := by
  induction j, hij using Nat.le_induction with
  | base => exact hi
  | succ j _ ih =>
      change ((correctedCouplingStage roots p q r w j).step p q r
        (w (0, j)) (w (1, j))).trees.upper.carrier.active = ∅
      rw [CorrectedCouplingState.step_upper]
      simp [ih]

theorem correctedCouplingClock_unbounded_of_upper_empty
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (i : ℕ)
    (hi : (correctedCouplingStage roots p q r w i).trees.upper.carrier.active = ∅) :
    ∀ k, ∃ j, k < correctedCouplingClock roots p q r w j := by
  have hlinear (n : ℕ) : correctedCouplingClock roots p q r w (i + n) =
      correctedCouplingClock roots p q r w i + n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.add_succ, correctedCouplingClock_succ]
        have hempty := correctedCouplingStage_upper_empty_of_le roots p q r w
          (Nat.le_add_right i n) hi
        rw [CorrectedCouplingState.emit_of_upper_empty _ p q r _ hempty]
        simp only [↓reduceIte, ih]
        omega
  intro k
  refine ⟨i + (k + 1), ?_⟩
  rw [hlinear]
  omega

theorem correctedCouplingClock_ae_unbounded
    (N : ℕ) (hN : 0 < N) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (q : ℝ) (r : List Bool → ℝ) :
    ∀ᵐ w ∂pairedUniformLaw, ∀ k, ∃ j,
      k < correctedCouplingClock (Finset.range N) p q r w j := by
  filter_upwards [correctedCouplingStage_upper_ae_eventually_empty N hN hp hp1 q r]
    with w hw
  obtain ⟨i, hi⟩ := hw
  exact correctedCouplingClock_unbounded_of_upper_empty _ p q r w i hi

end HeightPaper.CountCoupling
