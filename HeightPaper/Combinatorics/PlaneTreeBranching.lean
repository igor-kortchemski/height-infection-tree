module

public import HeightPaper.Combinatorics.PlaneTree
public import HeightPaper.Combinatorics.FirstChildFixedPoint
public import Mathlib.Probability.Distributions.Geometric

/-!
Adapted from the generic Bienaymé-law utilities in the sibling `freezing1`
project, using the same pinned Lean and Mathlib 4.35.0.

# The source geometric Bienaymé characterization

The branching property is stated for the genuine finite family of child
subtrees, with their full joint conditional law. No independence of trees
is built into the definition of a plane tree. The zero-parameter case
requires no conditioning on a null event.
-/

@[expose] public section

namespace HeightPaper.PlaneTree

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

def firstChildStructure : FirstChildStructure Tree where
  leaf := leaf
  degree := degree
  child := fun T i => child T (i + 1)
  graft := fun q => graft q.1 q.2
  measurable_degree := continuous_degree.measurable
  measurable_child := fun i => (continuous_child (i + 1)).measurable
  measurable_graft := continuous_graft.measurable
  degree_leaf := degree_leaf
  degree_graft := degree_graft
  child_graft_zero := child_one_graft
  child_graft_succ := fun A B i => child_succ_graft A B (by omega)

/-- The standard branching characterization stated in the paper: the root
has the given offspring law, and conditional on its count all its child
trees are independent copies of the original tree. -/
def IsBienayme (μ : Measure Tree) (offspringLaw : Measure ℕ) : Prop :=
  μ.map degree = offspringLaw ∧
    ∀ k : ℕ, μ {T | degree T = k} ≠ 0 →
      (ProbabilityTheory.cond μ {T | degree T = k}).map
        (fun T (i : Fin k) => child T (i.val + 1)) = Measure.pi (fun _ : Fin k => μ)

theorem isBienayme_geometric_of_fixedPoint (p : unitInterval) (hp : (p : ℝ) < 1)
    (μ : Measure Tree) [IsProbabilityMeasure μ]
    (hμ : μ = ENNReal.ofReal (1 - (p : ℝ)) • Measure.dirac leaf +
      ENNReal.ofReal (p : ℝ) • (μ.prod μ).map (fun q => graft q.1 q.2)) :
    IsBienayme μ (geometricMeasure (unitInterval.symm p)) := by
  have hsym : unitInterval.symm p ≠ 0 := by
    intro he
    have hh := congrArg (fun z : unitInterval => (z : ℝ)) he
    change 1 - (p : ℝ) = 0 at hh
    linarith
  constructor
  · apply Measure.ext_of_singleton
    intro k
    rw [Measure.map_apply continuous_degree.measurable (measurableSet_singleton k),
      geometricMeasure_singleton hsym]
    have hm := firstChildStructure.degree_measure_of_fixedPoint μ
      (ENNReal.ofReal (1 - (p : ℝ))) (ENNReal.ofReal (p : ℝ)) hμ k
    change μ {T | degree T = k} = _
    change μ {T | degree T = k} =
      ENNReal.ofReal (1 - (p : ℝ)) * ENNReal.ofReal (p : ℝ) ^ k at hm
    rw [hm, ← ENNReal.ofReal_pow p.2.1,
      ← ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2)]
    congr 1
    change (1 - (p : ℝ)) * (p : ℝ) ^ k =
      (1 - (1 - (p : ℝ))) ^ k * (1 - (p : ℝ))
    ring
  · intro k hk
    exact firstChildStructure.conditional_childrenLaw_of_fixedPoint μ
      (ENNReal.ofReal (1 - (p : ℝ))) (ENNReal.ofReal (p : ℝ)) hμ k hk

/-- L05, with its source conditional hypothesis expressed as the full joint
law of the first child and the reindexed remainder. -/
theorem isBienayme_geometric_of_conditional_split (p : unitInterval)
    (hp : (p : ℝ) < 1) (μ : Measure Tree) [IsProbabilityMeasure μ]
    (h0 : μ {T | degree T = 0} = ENNReal.ofReal (1 - (p : ℝ)))
    (hsplit : (p : ℝ) ≠ 0 →
      (ProbabilityTheory.cond μ {T | 0 < degree T}).map
        (fun T => (child T 1, dropFirst T)) = μ.prod μ) :
    IsBienayme μ (geometricMeasure (unitInterval.symm p)) := by
  have hpos : μ {T | 0 < degree T} = ENNReal.ofReal (p : ℝ) := by
    have he : {T | 0 < degree T} = {T | degree T = 0}ᶜ := by
      ext T
      simp [Nat.pos_iff_ne_zero]
    have hmeas : MeasurableSet {T | degree T = 0} :=
      continuous_degree.measurable (measurableSet_singleton 0)
    rw [he, measure_compl hmeas
      (measure_ne_top _ _), measure_univ, h0, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr p.2.2)]
    congr 1
    ring
  apply isBienayme_geometric_of_fixedPoint p hp μ
  apply firstChildStructure.fixedPoint_of_conditional_split dropFirst
    continuous_dropFirst.measurable (fun _ ht => eq_leaf_of_degree_zero ht)
    (fun _ ht => graft_child_dropFirst ht) μ
    (ENNReal.ofReal (1 - (p : ℝ))) (ENNReal.ofReal (p : ℝ)) h0 hpos
  intro hr
  apply hsplit
  intro he
  apply hr
  simp [he]

end HeightPaper.PlaneTree
