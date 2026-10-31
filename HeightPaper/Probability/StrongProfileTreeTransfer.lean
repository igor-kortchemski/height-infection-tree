module

public import HeightPaper.Probability.FiniteTreeCouplingLaw
public import HeightPaper.Probability.StrongProfileTransfer

/-! # Exact transfer of strong profile estimates from the coupled tree -/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

theorem coupledTreeState_law (l : ℝ≥0) (n k : ℕ) :
    birthParentLaw.map (fun q => coupledTreeState l n q k) = (evolve (l / n) n k).toMeasure := by
  change birthParentLaw.map (FinitePath.last ∘ coupledTreeHistory l n k) = _
  rw [← Measure.map_map (FinitePath.measurable FinitePath.last) (measurable_coupledTreeHistory l n k),
    coupledTreeHistory_law]
  unfold pathMeasure
  rw [PMF.toMeasure_map _ _ (FinitePath.measurable FinitePath.last), pathLaw_map_last]

theorem coupledTreeState_active_iff (l : ℝ) (n : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) (k : ℕ) :
    (coupledTreeState l n q k).active.Nonempty ↔ ∀ i ≤ k, 0 < finiteWalk l n q.1 i := by
  have hc := congrArg Prod.snd (counts_coupledTreeState l n q k)
  change infectious (coupledTreeState l n q k) = (absorbedCounts l n q.1 k).2 at hc
  rw [← Finset.card_pos]
  change 0 < infectious (coupledTreeState l n q k) ↔ _
  rw [hc]
  constructor
  · intro hp
    exact (finiteWalk_survival_iff l n q.1 k).mpr
      (fun i hi => absorbedCounts_pos_past l n q.1 hi hp)
  · intro hs
    exact (finiteWalk_survival_iff l n q.1 k).mp hs k le_rfl

end HeightPaper.CountCoupling

namespace HeightPaper

open Model CountCoupling

/-- The final analytic probability estimate may be established on the two
independent uniform sequences. Both the full tree law and source survival
boundary are transferred exactly or by a proved uniformly vanishing error. -/
theorem uniformStrongProfileStatement_of_coupled
    (hjoint : ∀ I : Set ℝ≥0, IsCompact I → ∀ T > (0 : ℝ),
      ∀ K : Set ℝ, IsCompact K →
      (∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l ∧
        K ⊆ Ioo (0 : ℝ) (profileRoot l)) →
      ∀ ε > (0 : ℝ), ∃ R ≥ (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
        birthParentLaw.real {q | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n q.1 i) ∧
          coupledTreeState l n q ⌊T * n⌋₊ ∈ strongProfileStateBad l K n R} < ε) :
    UniformStrongProfileStatement := by
  apply uniformStrongProfileStatement_of_active
  intro I hI T hT K hK hparams ε hε
  obtain ⟨R, hR, N, hN⟩ := hjoint I hI T hT K hK hparams ε hε
  refine ⟨R, hR, N, ?_⟩
  intro n hn l hl
  rw [← coupledTreeState_law l n ⌊T * n⌋₊]
  have hm : Measurable (fun q => coupledTreeState l n q ⌊T * n⌋₊) :=
    (measurable_pi_apply ⌊T * n⌋₊).comp (measurable_finite_rankTrajectory l n (initial n))
  simp only [Measure.real, Measure.map_apply hm (show MeasurableSet
    {s | s.active.Nonempty ∧ s ∈ strongProfileStateBad l K n R} from trivial)]
  have he : {q | (coupledTreeState l n q ⌊T * n⌋₊).active.Nonempty ∧
      coupledTreeState l n q ⌊T * n⌋₊ ∈ strongProfileStateBad l K n R} =
      {q | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n q.1 i) ∧
        coupledTreeState l n q ⌊T * n⌋₊ ∈ strongProfileStateBad l K n R} := by
    ext q
    rw [mem_ofPred_eq, mem_ofPred_eq, coupledTreeState_active_iff]
  change birthParentLaw.real {q | (coupledTreeState l n q ⌊T * n⌋₊).active.Nonempty ∧
    coupledTreeState l n q ⌊T * n⌋₊ ∈ strongProfileStateBad l K n R} < ε
  rw [he]
  exact hN n hn l hl

end HeightPaper
