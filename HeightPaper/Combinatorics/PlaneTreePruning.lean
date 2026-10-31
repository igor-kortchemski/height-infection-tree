module

public import HeightPaper.Combinatorics.PlaneTree

/-!
Adapted from the generic Bienaymé-law utilities in the sibling `freezing1`
project, using the same pinned Lean and Mathlib 4.35.0.

# Canonicalizing an arbitrary offspring field

Only offspring counts at existing addresses are retained. This measurable
map is the standard construction of a locally finite plane tree from a
field of potential offspring counts.
-/

@[expose] public section

namespace HeightPaper.PlaneTree

open MeasureTheory
open scoped Classical

def pruneRaw (f : Offspring) : Address → ℕ
  | [] => f []
  | j :: u => if 1 ≤ j ∧ j ≤ f [] then pruneRaw (fun v => f (j :: v)) u else 0

theorem canonical_pruneRaw (f : Offspring) : Canonical (pruneRaw f) := by
  intro u j
  induction u generalizing f with
  | nil =>
      simp only [List.nil_append, pruneRaw]
      intro hj
      rw [ite_eq_right hj]
  | cons i u ih =>
      by_cases hi : 1 ≤ i ∧ i ≤ f []
      · simpa only [List.cons_append, pruneRaw, ite_eq_left hi] using
          ih (fun v => f (i :: v))
      · simp [List.cons_append, pruneRaw, hi]

def prune (f : Offspring) : Tree := ⟨pruneRaw f, canonical_pruneRaw f⟩

@[simp] theorem degree_prune (f : Offspring) : degree (prune f) = f [] := rfl

theorem child_prune (f : Offspring) (j : ℕ) :
    child (prune f) j =
      if 1 ≤ j ∧ j ≤ f [] then prune (fun v => f (j :: v)) else leaf := by
  apply Subtype.ext
  funext u
  by_cases hj : 1 ≤ j ∧ j ≤ f [] <;>
    simp [child, prune, pruneRaw, hj]

theorem pruneRaw_eq_of_canonical {f : Offspring} (hf : Canonical f) (u : Address) :
    pruneRaw f u = f u := by
  induction u generalizing f with
  | nil => rfl
  | cons j u ih =>
      have hs : Canonical (fun v => f (j :: v)) := fun v k hk => hf (j :: v) k hk
      by_cases hj : 1 ≤ j ∧ j ≤ f []
      · simpa only [pruneRaw, ite_eq_left hj] using ih hs
      · rw [pruneRaw, ite_eq_right hj]
        exact (hf.zero_of_absent_child [] j hj u).symm

@[simp] theorem prune_val (T : Tree) : prune T.val = T := by
  apply Subtype.ext
  funext u
  exact pruneRaw_eq_of_canonical T.property u

theorem measurable_pruneRaw_eval (u : Address) :
    Measurable (fun f : Offspring => pruneRaw f u) := by
  induction u with
  | nil => exact measurable_pi_apply []
  | cons j u ih =>
      have hs : Measurable (fun f : Offspring => fun v => f (j :: v)) :=
        Measurable.of_eval fun v => measurable_pi_apply (j :: v)
      have hP : MeasurableSet {f : Offspring | 1 ≤ j ∧ j ≤ f []} :=
        (show MeasurableSet {k : ℕ | 1 ≤ j ∧ j ≤ k} from trivial).preimage
          (measurable_pi_apply [])
      exact Measurable.ite hP (ih.comp hs) measurable_const

theorem measurable_prune : Measurable prune := by
  have he0 : Topology.IsClosedEmbedding (Subtype.val : Tree → Offspring) :=
    isClosed_canonical.isClosedEmbedding_subtypeVal
  have he : MeasurableEmbedding (Subtype.val : Tree → Offspring) := he0.measurableEmbedding
  apply he.measurable_comp_iff.mp
  exact Measurable.of_eval measurable_pruneRaw_eval

end HeightPaper.PlaneTree
