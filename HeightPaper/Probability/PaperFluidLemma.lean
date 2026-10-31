module

public import HeightPaper.Probability.FiniteBudgetCompactFunctionalFluid
public import HeightPaper.Probability.SurvivalCoupling

/-!
# The improved coupled fluid lemma of the paper

This combines the previously proved weakly uniform survival-indicator
comparison with the unabsorbed finite-walk functional fluid limit, in the
paper's real-time and compact-parameter scope.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace HeightPaper.CountCoupling

theorem paper_improved_fluid_lemma
    {I : Set ℝ≥0} (hI : IsCompact I)
    {T t₁ t₂ : ℝ} (hT : 0 < T)
    (hparams : ∀ a ∈ I, 1 < (a : ℝ) ∧ T < fluidExtinctionTime a)
    (ht₁ : 0 ≤ t₁) (ht₁₂ : t₁ ≤ t₂)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a ∈ I,
      uniformLaw.real {u |
        ¬ ((∀ j ≤ ⌊T * n⌋₊, 0 < finiteWalk a n u j) ↔
          ∀ k, 0 < localWalk a u k)} < η ∧
      uniformLaw.real {u | ∃ t ∈ Icc t₁ t₂,
        δ ≤ |(finiteWalk (a : ℝ) n u ⌊t * n⌋₊ : ℝ) / n -
          fluidInfectiousRaw (a : ℝ) t|} < η := by
  obtain ⟨Ns, hs⟩ := uniform_survival_disagreement hI hT hparams hη
  obtain ⟨Nf, hf⟩ := finiteWalk_compact_parameter_real_time_fluid hI
    (fun a ha ↦ (hparams a ha).1) ht₁ ht₁₂ hδ hη
  refine ⟨max Ns Nf, ?_⟩
  intro n hn a ha
  exact ⟨hs n ((le_max_left Ns Nf).trans hn) a ha,
    hf n ((le_max_right Ns Nf).trans hn) a ha⟩

end HeightPaper.CountCoupling
