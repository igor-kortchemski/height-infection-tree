module

public import HeightPaper.Probability.CorrectedCouplingGenealogy
public import HeightPaper.Probability.UniformParentLaw
public import Mathlib.Probability.Distributions.Uniform

/-!
# Uniform selection from a coupled forest carrier

An independent coordinate selects an upper active label by its ordered rank.
This is the one-step selection law needed by the corrected coupling.  The
rejection-sampling time change that makes the middle and lower selections
uniform is a separate, unfinished step.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

noncomputable def CouplingGenealogy.selectedActive
    (s : CouplingGenealogy) (hs : s.carrier.active.Nonempty) (u : ℝ) : ℕ :=
  s.carrier.active.orderEmbOfFin rfl
    (Model.uniformRank s.carrier.active.card hs.card_pos u)

theorem CouplingGenealogy.selectedActive_mem
    (s : CouplingGenealogy) (hs : s.carrier.active.Nonempty) (u : ℝ) :
    s.selectedActive hs u ∈ s.carrier.active :=
  Finset.orderEmbOfFin_mem s.carrier.active rfl _

theorem CouplingGenealogy.measurable_selectedActive
    (s : CouplingGenealogy) (hs : s.carrier.active.Nonempty) :
    Measurable (s.selectedActive hs) :=
  (measurable_of_countable (s.carrier.active.orderEmbOfFin rfl)).comp
    (Model.measurable_uniformRank _ _)

/-- Each active label receives equal mass under the shared uniform draw. -/
theorem CouplingGenealogy.selectedActive_law
    (s : CouplingGenealogy) (hs : s.carrier.active.Nonempty) (k : ℕ) :
    uniformLaw.map (fun u ↦ s.selectedActive hs (u k)) =
      Measure.uniformOfFinset s.carrier.active := by
  classical
  have hm : Measurable (fun u : ℕ → ℝ ↦ s.selectedActive hs (u k)) :=
    (s.measurable_selectedActive hs).comp (measurable_pi_apply k)
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply hm (measurableSet_singleton x),
    Measure.uniformOfFinset_apply_singleton]
  by_cases hx : x ∈ s.carrier.active
  · obtain ⟨rank, hrank⟩ : x ∈ Set.range
        (s.carrier.active.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hx
    subst x
    simp only [ite_true, Finset.orderEmbOfFin_mem]
    have heq : {u : ℕ → ℝ |
        s.selectedActive hs (u k) =
          s.carrier.active.orderEmbOfFin rfl rank} =
        {u | Model.uniformRank _ hs.card_pos (u k) = rank} := by
      ext u
      exact (s.carrier.active.orderEmbOfFin rfl).injective.eq_iff
    change uniformLaw {u : ℕ → ℝ |
      s.selectedActive hs (u k) =
        s.carrier.active.orderEmbOfFin rfl rank} = _
    rw [heq]
    exact Model.uniformRank_probability _ hs.card_pos k rank
  · rw [ite_eq_right hx]
    have heq : {u : ℕ → ℝ | s.selectedActive hs (u k) = x} = ∅ := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro he
      exact hx (he ▸ s.selectedActive_mem hs (u k))
    change uniformLaw {u : ℕ → ℝ | s.selectedActive hs (u k) = x} = _
    rw [heq, measure_empty]

end HeightPaper.CountCoupling
