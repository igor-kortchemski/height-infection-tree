module

public import HeightPaper.Combinatorics.PlaneFiniteState

/-!
Adapted from the generic plane-tree utilities in the sibling `freezing1`
project, using the same pinned Lean and Mathlib 4.35.0.

# Exact Ulam--Harris support of finite plane states

Validity requires the actual finite vertex set to be rooted, prefix closed
and to contain exactly the initial interval of children at every vertex.
The canonical offspring shape therefore has exactly these vertices.
-/

@[expose] public section

namespace HeightPaper.PlaneForward

open PlaneTree
open scoped Classical

structure Valid (s : State) : Prop where
  root_mem : [] ∈ s.vertices
  active_subset : s.active ⊆ s.vertices
  prefix_closed : ∀ u v : Address, u ++ v ∈ s.vertices → u ∈ s.vertices
  children_iff : ∀ u ∈ s.vertices, ∀ j : ℕ,
    u ++ [j] ∈ s.vertices ↔ 1 ≤ j ∧ j ≤ childCount s u

theorem Valid.children_eq_empty_of_not_mem {s : State} (hs : Valid s)
    {u : Address} (hu : u ∉ s.vertices) : children s u = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hw, j, rfl⟩ := Finset.mem_filter.mp hw
  exact hu (hs.prefix_closed u [j] hw)

theorem Valid.childCount_zero_of_not_mem {s : State} (hs : Valid s)
    {u : Address} (hu : u ∉ s.vertices) : childCount s u = 0 := by
  rw [childCount, hs.children_eq_empty_of_not_mem hu, Finset.card_empty]

theorem Valid.childCount_canonical {s : State} (hs : Valid s) : Canonical (childCount s) := by
  intro u j hj
  apply hs.childCount_zero_of_not_mem
  intro hmem
  have hu := hs.prefix_closed u [j] hmem
  exact hj ((hs.children_iff u hu j).mp hmem)

noncomputable def shape (s : State) : Tree :=
  if hs : Valid s then ⟨childCount s, hs.childCount_canonical⟩ else leaf

theorem Valid.shape_offspring {s : State} (hs : Valid s) :
    (shape s).val = childCount s := by simp only [shape, dite_eq_left hs]

theorem Valid.mem_vertices_iff_present {s : State} (hs : Valid s) (u : Address) :
    u ∈ s.vertices ↔ Present (shape s) u := by
  induction u using List.reverseRecOn with
  | nil => exact ⟨fun _ => trivial, fun _ => hs.root_mem⟩
  | append_singleton u j ih =>
    rw [present_append_singleton, hs.shape_offspring, ← ih]
    constructor
    · intro huj
      have hu := hs.prefix_closed u [j] huj
      exact ⟨hu, (hs.children_iff u hu j).mp huj⟩
    · rintro ⟨hu, hj⟩
      exact (hs.children_iff u hu j).mpr hj

theorem children_initial (u : Address) : children initial u = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hw, j, he⟩ := Finset.mem_filter.mp hw
  have hw0 : w = [] := Finset.mem_singleton.mp hw
  have hlen := congrArg List.length he
  simp only [hw0, List.length_nil, List.length_append, List.length_singleton] at hlen
  omega

theorem childCount_initial (u : Address) : childCount initial u = 0 := by
  rw [childCount, children_initial, Finset.card_empty]

theorem initial_valid : Valid initial := by
  constructor
  · simp [initial]
  · exact Finset.Subset.refl _
  · intro u v huv
    have he : u ++ v = [] := Finset.mem_singleton.mp huv
    have hu : u = [] := (List.append_eq_nil_iff.mp he).1
    simp [hu, initial]
  · intro u hu j
    have he : u = [] := Finset.mem_singleton.mp hu
    subst u
    rw [childCount_initial]
    simp [initial]
    omega

theorem shape_initial : shape initial = leaf := by
  apply Subtype.ext
  funext u
  rw [initial_valid.shape_offspring, childCount_initial]
  rfl

theorem Valid.freeze {s : State} (hs : Valid s) (u : Address) : Valid (PlaneForward.freeze s u) := by
  constructor
  · exact hs.root_mem
  · intro v hv
    exact hs.active_subset (Finset.mem_of_mem_erase hv)
  · exact hs.prefix_closed
  · exact hs.children_iff

theorem shape_freeze {s : State} (hs : Valid s) (u : Address) :
    shape (freeze s u) = shape s := by
  apply Subtype.ext
  rw [(hs.freeze u).shape_offspring, hs.shape_offspring]
  rfl

end HeightPaper.PlaneForward
