module

public import HeightPaper.Combinatorics.PlaneTreePruning
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.Independence.InfinitePi

/-!
Adapted from the generic Bienaymé-law utilities in the sibling `freezing1`
project, using the same pinned Lean and Mathlib 4.35.0.

# The concrete Bienaymé construction from iid offspring counts

The probability space is the countable product of potential offspring
counts indexed by Ulam--Harris addresses. Pruning retains precisely the
counts at existing vertices, producing a canonical locally finite tree.
-/

@[expose] public section

namespace HeightPaper.PlaneTree

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

noncomputable def offspringFieldLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Measure Offspring := Measure.infinitePi (fun _ : Address => μ)

instance offspringFieldLaw_probability (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (offspringFieldLaw μ) := by
  unfold offspringFieldLaw
  infer_instance

noncomputable def bienaymeLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] : Measure Tree :=
  (offspringFieldLaw μ).map prune

instance bienaymeLaw_probability (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (bienaymeLaw μ) := by
  unfold bienaymeLaw
  infer_instance

theorem bienaymeLaw_map_degree (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (bienaymeLaw μ).map degree = μ := by
  rw [bienaymeLaw, Measure.map_map continuous_degree.measurable measurable_prune]
  change (offspringFieldLaw μ).map (fun f => f []) = μ
  exact Measure.infinitePi_map_eval (fun _ : Address => μ) []

theorem bienaymeLaw_leaf (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    bienaymeLaw μ {leaf} = μ {0} := by
  have hh := congrArg (fun ν : Measure ℕ => ν {0}) (bienaymeLaw_map_degree μ)
  rw [Measure.map_apply continuous_degree.measurable (measurableSet_singleton 0)] at hh
  have he : degree ⁻¹' {0} = {leaf} := by
    ext T
    exact degree_zero_iff T
  rw [he] at hh
  exact hh

noncomputable def geometricBienaymeLaw (p : unitInterval) : Measure Tree :=
  bienaymeLaw (geometricMeasure (unitInterval.symm p))

instance geometricBienaymeLaw_probability (p : unitInterval) :
    IsProbabilityMeasure (geometricBienaymeLaw p) := by
  unfold geometricBienaymeLaw
  infer_instance

end HeightPaper.PlaneTree
