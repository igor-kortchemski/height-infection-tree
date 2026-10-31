module

public import HeightPaper.Probability.FiniteStrongProfileCoupled
public import HeightPaper.Probability.StrongProfileTreeTransfer

/-! # The strong profile theorem of the paper -/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper

open Model CountCoupling

/-- The paper's fixed-parameter strong profile theorem, with the exact
lattice condition, Gaussian log correction, zero-mass failure event, and
non-strict source survival boundary. -/
theorem strongProfileTheorem : StrongProfileStatement := by
  intro l hl T hT K hK hKd ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨R, hR, N₁, hcoupled⟩ :=
    finiteStrongProfile_coupled_tight hl hT.1 hT.2 hK hKd hhalf
  let I : Set ℝ≥0 := {l}
  have hI : IsCompact I := isCompact_singleton
  have hparams : ∀ a ∈ I, 1 < (a : ℝ) ∧ T < fluidExtinctionTime a := by
    intro a ha
    have he : a = l := mem_singleton_iff.mp ha
    simpa only [he] using And.intro hl hT.2
  obtain ⟨N₂, hboundary⟩ := strongProfileBoundary_uniform_vanishing
    hI hT.1 hparams hhalf
  refine ⟨R, hR, max N₁ N₂, ?_⟩
  intro n hn
  let H := ⌊T * n⌋₊
  have hcoupled' := hcoupled n ((le_max_left _ _).trans hn)
  have hB := hboundary n ((le_max_right _ _).trans hn) l (mem_singleton l)
  have hstate : (evolve (l / n) n H).toMeasure.real
      {s | s.active.Nonempty ∧ s ∈ strongProfileStateBad l K n R} < ε / 2 := by
    rw [← coupledTreeState_law l n H]
    have hm : Measurable (fun q => coupledTreeState l n q H) :=
      (measurable_pi_apply H).comp (measurable_finite_rankTrajectory l n (initial n))
    simp only [Measure.real, Measure.map_apply hm (show MeasurableSet
      {s | s.active.Nonempty ∧ s ∈ strongProfileStateBad l K n R} from trivial)]
    have he : {q | (coupledTreeState l n q H).active.Nonempty ∧
        coupledTreeState l n q H ∈ strongProfileStateBad l K n R} =
        {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
          coupledTreeState l n q H ∈ strongProfileStateBad l K n R} := by
      ext q
      rw [mem_ofPred_eq, mem_ofPred_eq, coupledTreeState_active_iff]
    change birthParentLaw.real {q | (coupledTreeState l n q H).active.Nonempty ∧
      coupledTreeState l n q H ∈ strongProfileStateBad l K n R} < ε / 2
    rw [he]
    exact hcoupled'
  have hH : H ≤ 2 * n + 1 := by
    let ξ := 1 - T / fluidExtinctionTime l
    have ht := fluidExtinctionTime_pos hl
    have hξ : ξ ∈ Ioo (0 : ℝ) 1 := by
      dsimp [ξ]
      constructor
      · have := (div_lt_one ht).mpr hT.2
        linarith
      · have := div_pos hT.1 ht
        linarith
    have he : (1 - ξ) * fluidExtinctionTime l = T := by
      dsimp [ξ]
      field_simp [ht.ne']
      ring
    simpa only [H, sourceCutoff, he] using sourceCutoff_le_steps hl hξ n
  rw [← pathMeasure_event_at (l / n) n (2 * n + 1) H hH] at hstate
  change (pathMeasure (l / n) n (2 * n + 1)).real
    {q | (q.eval H).active.Nonempty ∧
      q.eval H ∈ strongProfileStateBad l K n R} < ε / 2 at hstate
  have hsub : strongProfileBad l T K n R ⊆
      {q | (q.eval H).active.Nonempty ∧
        q.eval H ∈ strongProfileStateBad l K n R} ∪ strongProfileBoundary T n := by
    intro q hq
    by_cases ha : (q.eval H).active.Nonempty
    · exact Or.inl ⟨ha, hq.2⟩
    · exact Or.inr ⟨hq.1, ha⟩
  have hbound :=
    (measureReal_mono (μ := pathMeasure (l / n) n (2 * n + 1)) hsub).trans
      (measureReal_union_le _ _)
  linarith

end HeightPaper
