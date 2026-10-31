module

public import HeightPaper.Probability.CorrectedCouplingNextEventLaw

/-!
# The actual next logical event

The token includes the emitted letter and the entire after-event middle
forest. On paths with unbounded clock it agrees with the physical update
at any emission of the corresponding logical index.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace HeightPaper.CountCoupling

noncomputable def correctedCouplingLogicalToken (N : ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) :
    Bool × FiniteCouplingGenealogy :=
  (correctedCouplingEmittedWord (Finset.range N) p q r w k,
    sampledMiddleForest N p q r w (k + 1))

theorem measurable_correctedCouplingLogicalToken (N : ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (k : ℕ) :
    Measurable (fun w ↦ correctedCouplingLogicalToken N p q r w k) :=
  ((measurable_pi_apply k).comp
    (measurable_correctedCouplingEmittedWord (Finset.range N) p q r)).prodMk
      ((measurable_pi_apply (k + 1)).comp (measurable_sampledMiddleForest N p q r))

theorem couplingLogicalTime_succ_at_emission
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ k, ∃ j, k < correctedCouplingClock roots p q r w j)
    (j : ℕ)
    (he : (correctedCouplingStage roots p q r w j).emit p q r (w (0, j)) = true) :
    couplingLogicalTime roots p q r w (correctedCouplingClock roots p q r w j + 1) = j + 1 := by
  apply (couplingLogicalTime_eq_iff_hit roots p q r w hunbounded _ _).mpr
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [correctedCouplingClock_succ, he]
    rfl
  · exact lt_of_le_of_lt (correctedCouplingClock_monotone roots p q r w
      (Nat.le_of_lt_succ hi)) (Nat.lt_succ_self _)

theorem correctedCouplingLogicalToken_at_emission
    (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ k, ∃ j, k < correctedCouplingClock (Finset.range N) p q r w j)
    (j : ℕ)
    (he : (correctedCouplingStage (Finset.range N) p q r w j).emit p q r (w (0, j)) = true) :
    correctedCouplingLogicalToken N p q r w
        (correctedCouplingClock (Finset.range N) p q r w j) =
      (recoveryThresholdBirth
        (r (correctedCouplingStage (Finset.range N) p q r w j).word) (w (1, j)),
        (finiteCouplingStage (Finset.range N) p q r w (j + 1)).middle.chronological) := by
  have hletter := correctedCouplingEmittedWord_at_emission (Finset.range N) p q r w
    hunbounded j he
  have htime := couplingLogicalTime_succ_at_emission (Finset.range N) p q r w hunbounded j he
  change (_, sampledMiddleForest N p q r w _) = _
  rw [hletter]
  unfold sampledMiddleForest
  rw [htime]

theorem correctedCouplingStage_word_eq_of_clock_eq
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) {i j : ℕ} (hij : i ≤ j)
    (hc : correctedCouplingClock roots p q r w i = correctedCouplingClock roots p q r w j) :
    (correctedCouplingStage roots p q r w i).word =
      (correctedCouplingStage roots p q r w j).word :=
  (correctedCouplingStage_word_prefix_of_le roots p q r w hij).eq_of_length hc

/-- A disjoint, almost surely exhaustive partition transports any measurable
random variable by summing its restricted laws. -/
theorem map_restrict_eq_sum_of_ae_partition
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) (H : Set Ω) (E : ℕ → Set Ω)
    (hE : ∀ n, MeasurableSet (E n)) (hd : Pairwise (Disjoint on E))
    (hcover : (⋃ n, E n) =ᵐ[μ] H) (T : Ω → α) (hT : Measurable T) :
    (μ.restrict H).map T = Measure.sum (fun n ↦ (μ.restrict (E n)).map T) := by
  rw [← Measure.restrict_congr_set hcover, Measure.restrict_iUnion hd hE,
    Measure.map_sum hT.aemeasurable]

end HeightPaper.CountCoupling
