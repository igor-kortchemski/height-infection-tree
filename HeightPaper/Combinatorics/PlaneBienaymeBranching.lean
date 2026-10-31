module

public import HeightPaper.Combinatorics.PlaneBienaymeLaw
public import HeightPaper.Combinatorics.PlaneTreeBranching
public import HeightPaper.Combinatorics.OffspringFieldGroups

/-!
Adapted from the generic Bienaymé-law utilities in the sibling `freezing1`
project, using the same pinned Lean and Mathlib 4.35.0.

# The actual branching property of the iid offspring construction

The root count and the potential offspring fields of its finitely many
children use disjoint product coordinates. After pruning, their full
conditional joint law is the product of the constructed tree law.
-/

@[expose] public section

namespace HeightPaper.PlaneTree

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

theorem raw_childrenEvent_measure (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k : ℕ) (E : Fin k → Set Tree) (hE : ∀ i, MeasurableSet (E i)) :
    offspringFieldLaw μ {f | f [] = k ∧
      ∀ i : Fin k, prune (fun u => f ((i.val + 1) :: u)) ∈ E i} =
      μ {k} * ∏ i : Fin k, bienaymeLaw μ (E i) := by
  let B : Fin (k + 1) → Set Offspring :=
    Fin.cases {f | f [] = k} (fun i => prune ⁻¹' E i)
  have hB : ∀ i, MeasurableSet (B i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change MeasurableSet {f : Offspring | f [] = k}
      exact (measurable_pi_apply [] : Measurable (fun f : Offspring => f []))
        ((measurableSet_singleton (k : ℕ) : MeasurableSet ({k} : Set ℕ)))
    · exact (hE j).preimage measurable_prune
  have hg := congrArg (fun ν : Measure (Fin (k + 1) → Offspring) =>
    ν (Set.pi Set.univ B)) (iid_branch_groups μ k)
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hB),
    Measure.pi_pi, Fin.prod_univ_succ] at hg
  have he : (fun (f : Offspring) (i : Fin (k + 1)) (u : Address) => f (branchAddress k (i, u))) ⁻¹'
      Set.pi Set.univ B =
      {f | f [] = k ∧ ∀ i : Fin k, prune (fun u => f ((i.val + 1) :: u)) ∈ E i} := by
    ext f
    simp [Set.mem_pi, Fin.forall_fin_succ, B, branchAddress]
  rw [he] at hg
  have hroot : offspringFieldLaw μ (B 0) = μ {k} := by
    have hh := congrArg (fun ν : Measure ℕ => ν {k})
      (Measure.infinitePi_map_eval (fun _ : Address => μ) [])
    rw [Measure.map_apply (measurable_pi_apply [] : Measurable (fun f : Offspring => f []))
      (measurableSet_singleton (k : ℕ) : MeasurableSet ({k} : Set ℕ))] at hh
    exact hh
  calc
    _ = offspringFieldLaw μ (B 0) * ∏ i : Fin k, offspringFieldLaw μ (B i.succ) := hg
    _ = _ := by
      rw [hroot]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact (Measure.map_apply measurable_prune (hE i)).symm

theorem bienaymeLaw_childrenEvent (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k : ℕ) (E : Fin k → Set Tree) (hE : ∀ i, MeasurableSet (E i)) :
    bienaymeLaw μ (firstChildStructure.childrenEvent k E) =
      μ {k} * ∏ i : Fin k, bienaymeLaw μ (E i) := by
  rw [bienaymeLaw, Measure.map_apply measurable_prune
    (firstChildStructure.measurableSet_childrenEvent k E hE)]
  have he : prune ⁻¹' firstChildStructure.childrenEvent k E =
      {f | f [] = k ∧ ∀ i : Fin k, prune (fun u => f ((i.val + 1) :: u)) ∈ E i} := by
    ext f
    change (f [] = k ∧ ∀ i : Fin k, child (prune f) (i.val + 1) ∈ E i) ↔ _
    constructor
    · rintro ⟨hf, hc⟩
      refine ⟨hf, fun i => ?_⟩
      have hi : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ f [] := by
        rw [hf]
        exact ⟨by omega, by omega⟩
      simpa only [child_prune, ite_eq_left hi] using hc i
    · rintro ⟨hf, hc⟩
      refine ⟨hf, fun i => ?_⟩
      have hi : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ f [] := by
        rw [hf]
        exact ⟨by omega, by omega⟩
      simpa only [child_prune, ite_eq_left hi] using hc i
  rw [he]
  exact raw_childrenEvent_measure μ k E hE

/-- Existence of the standard Bienaymé law for every offspring probability
measure, on the concrete countable product probability space. -/
theorem isBienayme_bienaymeLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsBienayme (bienaymeLaw μ) μ := by
  refine ⟨bienaymeLaw_map_degree μ, fun k hk => ?_⟩
  symm
  apply Measure.pi_eq
  intro E hE
  have hdeg : MeasurableSet {T | degree T = k} :=
    continuous_degree.measurable (measurableSet_singleton k)
  have hm : bienaymeLaw μ {T | degree T = k} = μ {k} := by
    have hh := congrArg (fun ν : Measure ℕ => ν {k}) (bienaymeLaw_map_degree μ)
    rw [Measure.map_apply continuous_degree.measurable (measurableSet_singleton k)] at hh
    exact hh
  rw [Measure.map_apply (Measurable.of_eval fun i =>
      (continuous_child (i.val + 1)).measurable) (MeasurableSet.univ_pi hE),
    ProbabilityTheory.cond_apply hdeg]
  have he : {T | degree T = k} ∩
      (fun T (i : Fin k) => child T (i.val + 1)) ⁻¹' Set.pi Set.univ E =
      firstChildStructure.childrenEvent k E := by
    ext T
    simp [FirstChildStructure.childrenEvent, firstChildStructure]
  rw [he, bienaymeLaw_childrenEvent μ k E hE, ← hm, ← mul_assoc,
    ENNReal.inv_mul_cancel hk (measure_ne_top _ _), one_mul]

end HeightPaper.PlaneTree
