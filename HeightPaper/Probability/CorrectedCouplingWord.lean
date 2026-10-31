module

public import HeightPaper.Probability.UniformWalk

/-!
# The corrected event for the geometric tree coupling

This is deliberately **not** the event printed in `lem:couplage`.  With
zero-based event indices, `correctedCouplingGood` requires the recovery
probability to lie in `[p,q]` at every step whose entire preceding active-count
history is positive.  Consequently it includes the step at which the middle
walk first hits zero.  The printed event omits that terminal step.

The finite-word construction below is a deterministic part of the proposed
coupling.  It does not assert the full tree sandwich or branching-tree laws.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

/-- A recovery has value `false`; a birth has value `true`. -/
noncomputable def recoveryThresholdBirth (r u : ℝ) : Bool := decide (r ≤ u)

/-- The word generated from conditional recovery probabilities.  The
probability of the next recovery may depend on the complete previous word. -/
noncomputable def adaptiveCouplingWord (r : List Bool → ℝ) (u : ℕ → ℝ) : ℕ → List Bool
  | 0 => []
  | k + 1 =>
      let w := adaptiveCouplingWord r u k
      w ++ [recoveryThresholdBirth (r w) (u k)]

@[simp] theorem adaptiveCouplingWord_zero (r : List Bool → ℝ) (u : ℕ → ℝ) :
    adaptiveCouplingWord r u 0 = [] := rfl

@[simp] theorem adaptiveCouplingWord_succ (r : List Bool → ℝ) (u : ℕ → ℝ)
    (k : ℕ) :
    adaptiveCouplingWord r u (k + 1) =
      adaptiveCouplingWord r u k ++
        [recoveryThresholdBirth (r (adaptiveCouplingWord r u k)) (u k)] := rfl

/-- The unabsorbed number of active individuals after a finite event word. -/
def couplingActiveCount (N : ℕ) (w : List Bool) : ℤ :=
  w.foldl (fun a b ↦ if b then a + 1 else a - 1) N

@[simp] theorem couplingActiveCount_nil (N : ℕ) :
    couplingActiveCount N [] = N := rfl

@[simp] theorem couplingActiveCount_append_singleton (N : ℕ) (w : List Bool)
    (b : Bool) :
    couplingActiveCount N (w ++ [b]) =
      if b then couplingActiveCount N w + 1 else couplingActiveCount N w - 1 := by
  simp [couplingActiveCount]

/-- Corrected hypothesis for `lem:couplage`.  If the first hit of zero is
at one-based time `τ_N`, the bounds apply at times `1 ≤ k ≤ τ_N`, rather than
the printed `1 ≤ k ≤ τ_N - 1`; if there is no hit, they apply forever. -/
def correctedCouplingGood (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (u : ℕ → ℝ) : Prop :=
  ∀ k : ℕ,
    (∀ j ≤ k, 0 < couplingActiveCount N (adaptiveCouplingWord r u j)) →
      p ≤ r (adaptiveCouplingWord r u k) ∧
      r (adaptiveCouplingWord r u k) ≤ q

/-- The event actually printed in the paper: the terminal step is omitted.
This is recorded only to make the distinction mathematically explicit. -/
def printedCouplingGood (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (u : ℕ → ℝ) : Prop :=
  ∀ k : ℕ,
    (∀ j ≤ k + 1,
      0 < couplingActiveCount N (adaptiveCouplingWord r u j)) →
      p ≤ r (adaptiveCouplingWord r u k) ∧
      r (adaptiveCouplingWord r u k) ≤ q

theorem correctedCouplingGood_implies_printed
    {N : ℕ} {p q : ℝ} {r : List Bool → ℝ} {u : ℕ → ℝ}
    (h : correctedCouplingGood N p q r u) :
    printedCouplingGood N p q r u := by
  intro k hk
  exact h k (fun j hj ↦ hk j (by omega))

/-- Unlike the printed event, the corrected event constrains the first
recovery probability even when the first step immediately ends the process. -/
theorem correctedCouplingGood_first {N : ℕ} (hN : 0 < N)
    {p q : ℝ} {r : List Bool → ℝ} {u : ℕ → ℝ}
    (h : correctedCouplingGood N p q r u) : p ≤ r [] ∧ r [] ≤ q := by
  have hzero : 0 < couplingActiveCount N (adaptiveCouplingWord r u 0) := by
    simpa using (show (0 : ℤ) < (N : ℤ) by exact_mod_cast hN)
  have hb := h 0 (by
    intro j hj
    have hj0 : j = 0 := by omega
    simpa [hj0] using hzero)
  simpa using hb

/-- The converse is false even at the first step.  This formally isolates
the precise change in hypotheses before any tree-law construction. -/
theorem printedCouplingGood_not_corrected_of_first_recovery
    {p q : ℝ} (hq : q < 1) :
    printedCouplingGood 1 p q (fun _ ↦ 1) (fun _ ↦ 0) ∧
      ¬ correctedCouplingGood 1 p q (fun _ ↦ 1) (fun _ ↦ 0) := by
  have hhit : couplingActiveCount 1
      (adaptiveCouplingWord (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) 1) = 0 := by
    simp [adaptiveCouplingWord_succ, recoveryThresholdBirth,
      couplingActiveCount]
  constructor
  · intro k hpre
    have hpos := hpre 1 (by omega)
    rw [hhit] at hpos
    omega
  · intro h
    have hfirst := correctedCouplingGood_first (N := 1) (by omega) h
    linarith

theorem recoveryThresholdBirth_mono_lower {r q u : ℝ} (hrq : r ≤ q)
    (h : recoveryThresholdBirth q u = true) :
    recoveryThresholdBirth r u = true := by
  simp only [recoveryThresholdBirth, decide_eq_true_eq] at h ⊢
  exact hrq.trans h

theorem recoveryThresholdBirth_mono_upper {p r u : ℝ} (hpr : p ≤ r)
    (h : recoveryThresholdBirth r u = true) :
    recoveryThresholdBirth p u = true := by
  simp only [recoveryThresholdBirth, decide_eq_true_eq] at h ⊢
  exact hpr.trans h

/-- At every step covered by the corrected event, a lower-tree birth is a
middle birth and a middle birth is an upper-tree birth. -/
theorem correctedCouplingGood_step_birth_sandwich
    {N : ℕ} {p q : ℝ} {r : List Bool → ℝ} {u : ℕ → ℝ}
    (h : correctedCouplingGood N p q r u) (k : ℕ)
    (hactive : ∀ j ≤ k, 0 < couplingActiveCount N (adaptiveCouplingWord r u j)) :
    (recoveryThresholdBirth q (u k) = true →
      recoveryThresholdBirth (r (adaptiveCouplingWord r u k)) (u k) = true) ∧
    (recoveryThresholdBirth (r (adaptiveCouplingWord r u k)) (u k) = true →
      recoveryThresholdBirth p (u k) = true) := by
  obtain ⟨hpr, hrq⟩ := h k hactive
  exact ⟨recoveryThresholdBirth_mono_lower hrq,
    recoveryThresholdBirth_mono_upper hpr⟩

private theorem couplingActiveStep_mono {a b : ℤ} (hab : a ≤ b)
    {x y : Bool} (hxy : x = true → y = true) :
    (if x then a + 1 else a - 1) ≤
      (if y then b + 1 else b - 1) := by
  cases x <;> cases y <;> simp_all; omega

/-- The common-uniform count paths are ordered through the middle walk's
first extinction.  This is the count-level part of the corrected tree
coupling; it does not imply inclusion of the random trees. -/
theorem correctedCoupling_count_sandwich
    {N : ℕ} {p q : ℝ} {r : List Bool → ℝ} {u : ℕ → ℝ}
    (h : correctedCouplingGood N p q r u) (k : ℕ)
    (hpre : ∀ j < k, 0 < couplingActiveCount N (adaptiveCouplingWord r u j)) :
    couplingActiveCount N (adaptiveCouplingWord (fun _ ↦ q) u k) ≤
      couplingActiveCount N (adaptiveCouplingWord r u k) ∧
    couplingActiveCount N (adaptiveCouplingWord r u k) ≤
      couplingActiveCount N (adaptiveCouplingWord (fun _ ↦ p) u k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hprev : ∀ j < k,
          0 < couplingActiveCount N (adaptiveCouplingWord r u j) :=
        fun j hj ↦ hpre j (by omega)
      obtain ⟨hlo, hhi⟩ := ih hprev
      have hactive : ∀ j ≤ k,
          0 < couplingActiveCount N (adaptiveCouplingWord r u j) :=
        fun j hj ↦ hpre j (by omega)
      obtain ⟨hlobirth, hhibirth⟩ :=
        correctedCouplingGood_step_birth_sandwich h k hactive
      simp only [adaptiveCouplingWord_succ,
        couplingActiveCount_append_singleton]
      exact ⟨couplingActiveStep_mono hlo hlobirth,
        couplingActiveStep_mono hhi hhibirth⟩

end HeightPaper.CountCoupling
