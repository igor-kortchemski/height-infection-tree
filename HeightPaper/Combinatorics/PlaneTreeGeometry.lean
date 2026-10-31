module

public import HeightPaper.Combinatorics.PlaneTree
public import Mathlib.SetTheory.Descriptive.Tree

/-!
Adapted from the generic plane-tree utilities in the sibling `freezing1`
project, using the same pinned Lean and Mathlib 4.35.0.

# Ulam--Harris vertices and finite balls of the plane-tree encoding

Only positive child indices up to the parent's offspring count occur.
The encoded vertices form a nonempty prefix-closed tree, and each generation
and radius ball is an explicitly finite set.
-/

@[expose] public section

namespace HeightPaper.PlaneTree

open scoped Classical

def Present (T : Tree) : Address → Prop
  | [] => True
  | j :: u => 1 ≤ j ∧ j ≤ degree T ∧ Present (child T j) u

@[simp] theorem present_nil (T : Tree) : Present T [] := trivial

@[simp] theorem present_cons (T : Tree) (j : ℕ) (u : Address) :
    Present T (j :: u) ↔ 1 ≤ j ∧ j ≤ degree T ∧ Present (child T j) u := Iff.rfl

theorem not_present_offspring_zero (T : Tree) (u : Address) (hu : ¬Present T u) :
    T.val u = 0 := by
  induction u generalizing T with
  | nil => exact (hu trivial).elim
  | cons j u ih =>
    by_cases hj : 1 ≤ j ∧ j ≤ degree T
    · exact ih (child T j) (fun h => hu ⟨hj.1, hj.2, h⟩)
    · exact T.property.zero_of_absent_child [] j hj u

theorem present_append_singleton (T : Tree) (u : Address) (j : ℕ) :
    Present T (u ++ [j]) ↔ Present T u ∧ 1 ≤ j ∧ j ≤ T.val u := by
  induction u generalizing T with
  | nil => simp [Present, degree]
  | cons i u ih =>
    simp only [List.cons_append, present_cons, ih, child_offspring]
    tauto

theorem present_of_prefix {T : Tree} {u v : Address} (huv : u <+: v)
    (hv : Present T v) : Present T u := by
  obtain ⟨w, rfl⟩ := huv
  induction w using List.reverseRecOn with
  | nil => simpa using hv
  | append_singleton w j ih =>
    apply ih
    exact (present_append_singleton T (u ++ w) j).mp (by simpa [List.append_assoc] using hv) |>.1

def ulamTree (T : Tree) : Descriptive.tree ℕ :=
  ⟨{u | Present T u}, fun u j h => (present_append_singleton T u j).mp h |>.1⟩

@[simp] theorem mem_ulamTree (T : Tree) (u : Address) : u ∈ ulamTree T ↔ Present T u := Iff.rfl

theorem ulamTree_nonempty (T : Tree) : ([] : Address) ∈ ulamTree T := trivial

theorem ulamTree_children (T : Tree) (u : Address) (hu : u ∈ ulamTree T) (j : ℕ) :
    u ++ [j] ∈ ulamTree T ↔ 1 ≤ j ∧ j ≤ T.val u := by
  rw [mem_ulamTree, present_append_singleton]
  exact and_iff_right hu

noncomputable def generation (T : Tree) : ℕ → Finset Address
  | 0 => {[]}
  | n + 1 => (Finset.Icc 1 (degree T)).biUnion
      (fun j => (generation (child T j) n).image (List.cons j))

theorem mem_generation (T : Tree) (n : ℕ) (u : Address) :
    u ∈ generation T n ↔ Present T u ∧ u.length = n := by
  induction n generalizing T u with
  | zero =>
    cases u with
    | nil => simp [generation]
    | cons j u => simp [generation]
  | succ n ih =>
    cases u with
    | nil => simp [generation]
    | cons j u =>
      simp only [generation, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image,
        ih, List.cons.injEq, present_cons, List.length_cons]
      constructor
      · rintro ⟨i, hi, v, hv, ⟨rfl, rfl⟩⟩
        exact ⟨⟨hi.1, hi.2, hv.1⟩, by omega⟩
      · rintro ⟨⟨hj1, hjT, hu⟩, hlen⟩
        exact ⟨j, ⟨hj1, hjT⟩, u, ⟨hu, by omega⟩, rfl, rfl⟩

noncomputable def ball (T : Tree) (h : ℕ) : Finset Address :=
  (Finset.range (h + 1)).biUnion (generation T)

theorem mem_ball (T : Tree) (h : ℕ) (u : Address) :
    u ∈ ball T h ↔ Present T u ∧ u.length ≤ h := by
  simp only [ball, Finset.mem_biUnion, Finset.mem_range, mem_generation]
  constructor
  · rintro ⟨n, hn, hu, hlen⟩
    exact ⟨hu, by omega⟩
  · rintro ⟨hu, hh⟩
    exact ⟨u.length, by omega, hu, rfl⟩

theorem finite_vertices_below (T : Tree) (h : ℕ) :
    {u : Address | u ∈ ulamTree T ∧ u.length ≤ h}.Finite := by
  have he : {u : Address | u ∈ ulamTree T ∧ u.length ≤ h} = (ball T h : Set Address) := by
    ext u
    exact (mem_ball T h u).symm
  rw [he]
  exact Finset.finite_toSet _

theorem child_vertices (T : Tree) {j : ℕ} (hj : 1 ≤ j ∧ j ≤ degree T)
    (u : Address) : u ∈ ulamTree (child T j) ↔ j :: u ∈ ulamTree T := by
  simp only [mem_ulamTree, present_cons]
  exact ⟨fun h => ⟨hj.1, hj.2, h⟩, fun h => h.2.2⟩

end HeightPaper.PlaneTree
