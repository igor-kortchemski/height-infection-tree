module

public import HeightPaper.Probability.CorrectedCouplingRejectionToken
public import HeightPaper.Probability.CorrectedCouplingEmptyToken

/-!
# Complete source kernel after an arbitrary causal middle history

The three branches (faithful rejection, direct update, and absorbed middle)
share one kernel. Reachability supplies the parent-closure invariant; it is
not imposed as an assumption on the final source law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HeightPaper.CountCoupling

theorem direct_middle_logical_kernel_on_event
    (N : ℕ) (hN : 0 < N) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (q : ℝ) (r : List Bool → ℝ) (j : ℕ)
    (H : Set ((Fin 2 × ℕ) → ℝ)) (hH : MeasurableSet H)
    (hcausal : ∀ w z, (∀ i, i.2 < j → w i = z i) → (w ∈ H ↔ z ∈ H))
    (s : FiniteCouplingState)
    (hfix : ∀ w ∈ H, finiteCouplingStage (Finset.range N) p q r w j = s)
    (hbad : ¬(s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q))
    (hparent : ∀ x ∈ s.middle.1.carrier.vertices,
      s.middle.1.parent x ∈ s.middle.1.carrier.vertices) :
    (pairedUniformLaw.restrict H).map (fun w ↦ correctedCouplingLogicalToken N p q r w s.word.length) =
      pairedUniformLaw H • sourceMiddleTokenLaw s.middle.chronological (r s.word) := by
  have heq : (fun w ↦ correctedCouplingLogicalToken N p q r w s.word.length) =ᵐ[pairedUniformLaw.restrict H]
      (fun w ↦ (recoveryThresholdBirth (r s.word) (w (1, j)),
        (finiteCouplingStage (Finset.range N) p q r w (j + 1)).middle.chronological)) := by
    filter_upwards [ae_restrict_mem hH,
      ae_restrict_of_ae (correctedCouplingClock_ae_unbounded N hN hp hp1 q r)] with w hw hu
    have hreal : correctedCouplingStage (Finset.range N) p q r w j = s.toState := by
      rw [← finiteCouplingStage_toState, hfix w hw]
    have hemit : (correctedCouplingStage (Finset.range N) p q r w j).emit p q r (w (0, j)) = true := by
      rw [hreal]
      simp [CorrectedCouplingState.emit, FiniteCouplingState.toState, hbad]
    have hc : correctedCouplingClock (Finset.range N) p q r w j = s.word.length :=
      congrArg (fun t : CorrectedCouplingState ↦ t.word.length) hreal
    rw [← hc, correctedCouplingLogicalToken_at_emission N p q r w hu j hemit,
      congrArg CorrectedCouplingState.word hreal]
    rfl
  rw [Measure.map_congr heq]
  exact direct_middle_source_kernel_on_event N p q r j H hH hcausal s hfix hbad hparent

/-- Full next-event law on every causal past event fixing the actual state.
No favorable-event conditioning is used to establish the marginal law. -/
theorem middle_logical_kernel_on_event
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hp1 : p ≤ 1)
    (r : List Bool → ℝ) (j : ℕ)
    (H : Set ((Fin 2 × ℕ) → ℝ)) (hH : MeasurableSet H)
    (hcausal : ∀ w z, (∀ i, i.2 < j → w i = z i) → (w ∈ H ↔ z ∈ H))
    (s : FiniteCouplingState)
    (hfix : ∀ w ∈ H, finiteCouplingStage (Finset.range N) p q r w j = s) :
    (pairedUniformLaw.restrict H).map (fun w ↦ correctedCouplingLogicalToken N p q r w s.word.length) =
      pairedUniformLaw H • sourceMiddleTokenLaw s.middle.chronological (r s.word) := by
  by_cases hne : H.Nonempty
  · obtain ⟨w, hw⟩ := hne
    have hreal : correctedCouplingStage (Finset.range N) p q r w j = s.toState := by
      rw [← finiteCouplingStage_toState, hfix w hw]
    have hparent : ∀ x ∈ s.middle.1.carrier.vertices,
        s.middle.1.parent x ∈ s.middle.1.carrier.vertices := by
      have h := correctedCouplingStage_middle_parent_mem N hN hpq r w j
      simpa only [hreal, FiniteCouplingState.toState] using h
    by_cases hA : s.middle.1.carrier.active.Nonempty
    · by_cases hg : s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q
      · exact faithful_middle_logical_kernel_on_event N hN hp hpq hp1 r j H hH hcausal s
          hfix hg.1 hg.2 hA hparent
      · exact direct_middle_logical_kernel_on_event N hN hp hp1 q r j H hH hcausal s hfix hg hparent
    · exact empty_middle_logical_kernel_on_event N hN hp hp1 q r j H hH hcausal s hfix
        (Finset.not_nonempty_iff_eq_empty.mp hA)
  · have he : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [he, Measure.restrict_empty, Measure.map_zero, measure_empty, zero_smul]

end HeightPaper.CountCoupling
