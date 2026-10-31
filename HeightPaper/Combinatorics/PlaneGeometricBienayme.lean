module

public import HeightPaper.Combinatorics.PlaneBienaymeBranching
public import HeightPaper.Combinatorics.PlaneBienaymeUniqueness

/-!
Adapted from the generic Bienaymé-law utilities in the sibling `freezing1`
project, using the same pinned Lean and Mathlib 4.35.0.

# Identification with the concrete iid Bienaymé law

Existence comes from independent potential offspring counts and measurable
pruning. Uniqueness comes from the full branching property and finite
coordinate cylinders. The source's first-child characterization therefore
identifies an arbitrary plane-tree law with this concrete construction.
-/

@[expose] public section

namespace HeightPaper.PlaneTree

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

theorem IsBienayme.eq_bienaymeLaw {μ : Measure Tree} [IsProbabilityMeasure μ]
    {ρ : Measure ℕ} [IsProbabilityMeasure ρ] (h : IsBienayme μ ρ) :
    μ = bienaymeLaw ρ := h.unique (isBienayme_bienaymeLaw ρ)

theorem exists_unique_bienaymeLaw (ρ : Measure ℕ) [IsProbabilityMeasure ρ] :
    IsBienayme (bienaymeLaw ρ) ρ ∧
      ∀ μ : Measure Tree, IsProbabilityMeasure μ → IsBienayme μ ρ → μ = bienaymeLaw ρ := by
  refine ⟨isBienayme_bienaymeLaw ρ, fun μ hprob h => ?_⟩
  let _ := hprob
  exact h.eq_bienaymeLaw

theorem law_eq_geometricBienayme_of_conditional_split (p : unitInterval)
    (hp : (p : ℝ) < 1) (μ : Measure Tree) [IsProbabilityMeasure μ]
    (h0 : μ {T | degree T = 0} = ENNReal.ofReal (1 - (p : ℝ)))
    (hsplit : (p : ℝ) ≠ 0 →
      (ProbabilityTheory.cond μ {T | 0 < degree T}).map
        (fun T => (child T 1, dropFirst T)) = μ.prod μ) :
    μ = geometricBienaymeLaw p :=
  (isBienayme_geometric_of_conditional_split p hp μ h0 hsplit).eq_bienaymeLaw

end HeightPaper.PlaneTree
