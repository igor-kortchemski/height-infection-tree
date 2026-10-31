module

public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Tactic

/-!
Adapted from the generic plane-tree utilities in the sibling `freezing1`
project, using the same pinned Lean and Mathlib 4.35.0.

# Locally finite plane trees with canonical offspring coordinates

An address is a finite list of positive child indices. Offspring counts are
zero at absent addresses. The immediate zero condition below propagates to
all descendants of an absent address. It is closed in the countable product
of discrete natural numbers, giving a Polish space of canonical tree data.
-/

@[expose] public section

namespace HeightPaper.PlaneTree

open Filter MeasureTheory Set
open scoped Topology Classical

set_option backward.isDefEq.respectTransparency false

abbrev Address := List ℕ

instance : MeasurableSpace Address := ⊤
instance : DiscreteMeasurableSpace Address := ⟨fun _ => trivial⟩

abbrev Offspring := Address → ℕ

def Canonical (f : Offspring) : Prop :=
  ∀ (u : Address) (j : ℕ), ¬(1 ≤ j ∧ j ≤ f u) → f (u ++ [j]) = 0

theorem isClosed_canonical : IsClosed {f : Offspring | Canonical f} := by
  have he : {f : Offspring | Canonical f} =
      ⋂ u : Address, ⋂ j : ℕ, {f | ¬(1 ≤ j ∧ j ≤ f u) → f (u ++ [j]) = 0} := by
    ext f
    simp only [Canonical, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [he]
  apply isClosed_iInter
  intro u
  apply isClosed_iInter
  intro j
  have hc : Continuous (fun f : Offspring => (f u, f (u ++ [j]))) :=
    (continuous_apply u).prodMk (continuous_apply (u ++ [j]))
  have hd : IsClosed {q : ℕ × ℕ | ¬(1 ≤ j ∧ j ≤ q.1) → q.2 = 0} := isClosed_discrete _
  exact hd.preimage hc

abbrev Tree := {f : Offspring // Canonical f}

instance : PolishSpace Tree := isClosed_canonical.polishSpace
instance : MeasurableSpace Tree := borel Tree
instance : BorelSpace Tree := ⟨rfl⟩

def degree (T : Tree) : ℕ := T.val []

theorem continuous_offspring (u : Address) : Continuous (fun T : Tree => T.val u) :=
  (continuous_apply u).comp continuous_subtype_val

theorem continuous_degree : Continuous degree := continuous_offspring []

def leaf : Tree := ⟨fun _ => 0, fun _ _ _ => rfl⟩

@[simp] theorem leaf_offspring (u : Address) : leaf.val u = 0 := rfl
@[simp] theorem degree_leaf : degree leaf = 0 := rfl

theorem Canonical.zero_descendants {f : Offspring} (hf : Canonical f)
    {u : Address} (hu : f u = 0) (v : Address) : f (u ++ v) = 0 := by
  induction v using List.reverseRecOn with
  | nil => simpa using hu
  | append_singleton v j ih =>
    rw [← List.append_assoc]
    exact hf (u ++ v) j (by rw [ih]; omega)

theorem Canonical.zero_of_absent_child {f : Offspring} (hf : Canonical f)
    (u : Address) (j : ℕ) (hj : ¬(1 ≤ j ∧ j ≤ f u)) (v : Address) :
    f (u ++ j :: v) = 0 := by
  simpa only [List.append_assoc, List.singleton_append] using
    hf.zero_descendants (hf u j hj) v

theorem eq_leaf_of_degree_zero {T : Tree} (hT : degree T = 0) : T = leaf := by
  apply Subtype.ext
  funext u
  simpa only [List.nil_append, leaf_offspring] using T.property.zero_descendants hT u

theorem degree_zero_iff (T : Tree) : degree T = 0 ↔ T = leaf :=
  ⟨eq_leaf_of_degree_zero, fun h => by rw [h]; rfl⟩

def child (T : Tree) (j : ℕ) : Tree :=
  ⟨fun u => T.val (j :: u), by
    intro u k hk
    exact T.property (j :: u) k hk⟩

@[simp] theorem child_offspring (T : Tree) (j : ℕ) (u : Address) :
    (child T j).val u = T.val (j :: u) := rfl

theorem child_eq_leaf_of_absent (T : Tree) (j : ℕ)
    (hj : ¬(1 ≤ j ∧ j ≤ degree T)) : child T j = leaf := by
  apply Subtype.ext
  funext u
  exact T.property.zero_of_absent_child [] j hj u

theorem continuous_child (j : ℕ) : Continuous (fun T : Tree => child T j) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun u => continuous_offspring (j :: u)

def dropFirstRaw (f : Offspring) : Offspring
  | [] => f [] - 1
  | j :: u => if j = 0 then 0 else f ((j + 1) :: u)

theorem Canonical.dropFirstRaw {f : Offspring} (hf : Canonical f) :
    Canonical (PlaneTree.dropFirstRaw f) := by
  intro u j hj
  cases u with
  | nil =>
    simp only [PlaneTree.dropFirstRaw] at hj
    simp only [List.nil_append, PlaneTree.dropFirstRaw]
    split_ifs with hj0
    · rfl
    · exact hf [] (j + 1) (by omega)
  | cons i u =>
    simp only [List.cons_append, PlaneTree.dropFirstRaw] at hj ⊢
    split_ifs at hj ⊢ with hi
    · rfl
    · exact hf ((i + 1) :: u) j hj

def dropFirst (T : Tree) : Tree := ⟨dropFirstRaw T.val, T.property.dropFirstRaw⟩

@[simp] theorem degree_dropFirst (T : Tree) : degree (dropFirst T) = degree T - 1 := rfl

theorem child_dropFirst (T : Tree) {j : ℕ} (hj : 1 ≤ j) :
    child (dropFirst T) j = child T (j + 1) := by
  apply Subtype.ext
  funext u
  simp [child, dropFirst, dropFirstRaw, show j ≠ 0 by omega]

theorem continuous_dropFirst : Continuous dropFirst := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro u
  cases u with
  | nil =>
    exact (continuous_of_discreteTopology : Continuous (fun k : ℕ => k - 1)).comp
      (continuous_offspring [])
  | cons j u =>
    by_cases hj : j = 0
    · subst j
      change Continuous (fun _ : Tree => if (0 : ℕ) = 0 then 0 else _)
      simpa using (continuous_const : Continuous (fun _ : Tree => (0 : ℕ)))
    · change Continuous (fun T : Tree => if j = 0 then 0 else T.val ((j + 1) :: u))
      simpa only [ite_eq_right hj] using continuous_offspring ((j + 1) :: u)

def graftRaw (a b : Offspring) : Offspring
  | [] => b [] + 1
  | j :: u => if j = 0 then 0 else if j = 1 then a u else b ((j - 1) :: u)

theorem Canonical.graftRaw {a b : Offspring} (ha : Canonical a) (hb : Canonical b) :
    Canonical (PlaneTree.graftRaw a b) := by
  intro u j hj
  cases u with
  | nil =>
    simp only [PlaneTree.graftRaw] at hj
    simp only [List.nil_append, PlaneTree.graftRaw]
    split_ifs with hj0 hj1
    · rfl
    · omega
    · exact hb [] (j - 1) (by omega)
  | cons i u =>
    simp only [List.cons_append, PlaneTree.graftRaw] at hj ⊢
    split_ifs at hj ⊢ with hi0 hi1
    · rfl
    · exact ha u j hj
    · exact hb ((i - 1) :: u) j hj

def graft (A B : Tree) : Tree := ⟨graftRaw A.val B.val, A.property.graftRaw B.property⟩

@[simp] theorem degree_graft (A B : Tree) : degree (graft A B) = degree B + 1 := rfl

@[simp] theorem child_one_graft (A B : Tree) : child (graft A B) 1 = A := by
  apply Subtype.ext
  funext u
  simp [child, graft, graftRaw]

theorem child_succ_graft (A B : Tree) {j : ℕ} (hj : 1 ≤ j) :
    child (graft A B) (j + 1) = child B j := by
  apply Subtype.ext
  funext u
  simp [child, graft, graftRaw, show j ≠ 0 by omega]

@[simp] theorem dropFirst_graft (A B : Tree) : dropFirst (graft A B) = B := by
  apply Subtype.ext
  funext u
  cases u with
  | nil => simp [dropFirst, dropFirstRaw, graft, graftRaw]
  | cons j u =>
    by_cases hj : j = 0
    · subst j
      simp only [dropFirst, dropFirstRaw]
      exact (B.property.zero_of_absent_child [] 0 (by omega) u).symm
    · simp [dropFirst, dropFirstRaw, graft, graftRaw, hj]

theorem graft_child_dropFirst {T : Tree} (hT : 0 < degree T) :
    graft (child T 1) (dropFirst T) = T := by
  apply Subtype.ext
  funext u
  cases u with
  | nil =>
    change T.val [] - 1 + 1 = T.val []
    change 0 < T.val [] at hT
    omega
  | cons j u =>
    by_cases hj0 : j = 0
    · subst j
      simp only [graft, graftRaw]
      exact (T.property.zero_of_absent_child [] 0 (by omega) u).symm
    · by_cases hj1 : j = 1
      · subst j
        simp [graft, graftRaw, child]
      · have hj' : j - 1 ≠ 0 := by omega
        have he : j - 1 + 1 = j := by omega
        simp [graft, graftRaw, dropFirst, dropFirstRaw, hj0, hj1, hj', he]

theorem continuous_graft : Continuous (fun p : Tree × Tree => graft p.1 p.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro u
  cases u with
  | nil =>
    exact (continuous_of_discreteTopology : Continuous (fun k : ℕ => k + 1)).comp
      ((continuous_offspring []).comp continuous_snd)
  | cons j u =>
    by_cases hj0 : j = 0
    · subst j
      change Continuous (fun _ : Tree × Tree => if (0 : ℕ) = 0 then 0 else _)
      simpa using
        (continuous_const : Continuous (fun _ : Tree × Tree => (0 : ℕ)))
    · by_cases hj1 : j = 1
      · subst j
        change Continuous (fun p : Tree × Tree => if (1 : ℕ) = 0 then 0 else
          if (1 : ℕ) = 1 then p.1.val u else _)
        simpa [Function.comp_def] using
          (continuous_offspring u).comp continuous_fst
      · change Continuous (fun p : Tree × Tree => if j = 0 then 0 else
          if j = 1 then _ else p.2.val ((j - 1) :: u))
        simpa only [ite_eq_right hj0, ite_eq_right hj1, Function.comp_def] using
          (continuous_offspring ((j - 1) :: u)).comp continuous_snd

end HeightPaper.PlaneTree
