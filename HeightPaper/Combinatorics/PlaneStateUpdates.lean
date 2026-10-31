module

public import HeightPaper.Combinatorics.PlaneStateValidity

/-!
Adapted from the generic plane-tree utilities in the sibling `freezing1`
project, using the same pinned Lean and Mathlib 4.35.0.

# Legal updates preserve the exact finite plane-tree support

The attachment is the next child in chronological order. It is fresh on a
valid state, changes only its parent's offspring count, and is initially a
leaf. Prefix closure and the complete initial interval of children persist.
-/

@[expose] public section

namespace HeightPaper.PlaneForward

open PlaneTree
open scoped Classical

theorem children_attach (s : State) (u v : Address) :
    children (attach s u) v =
      if v = u then insert (newChild s u) (children s v) else children s v := by
  change ((insert (newChild s u) s.vertices).filter
    (fun w => ∃ j : ℕ, w = v ++ [j])) = _
  rw [Finset.filter_insert]
  have he : (∃ j : ℕ, newChild s u = v ++ [j]) ↔ v = u := by
    simp only [newChild, List.append_singleton_inj]
    constructor
    · rintro ⟨j, huv, _⟩
      exact huv.symm
    · rintro rfl
      exact ⟨childCount s v + 1, rfl, rfl⟩
  simp only [he]
  rfl

theorem Valid.newChild_not_mem {s : State} (hs : Valid s) {u : Address}
    (hu : u ∈ s.vertices) : newChild s u ∉ s.vertices := by
  intro hnew
  have hh := (hs.children_iff u hu (childCount s u + 1)).mp hnew
  omega

theorem newChild_ne_parent (s : State) (u : Address) : newChild s u ≠ u := by
  intro he
  have hh := congrArg List.length he
  simp only [newChild, List.length_append, List.length_singleton] at hh
  omega

theorem Valid.childCount_attach_self {s : State} (hs : Valid s) {u : Address}
    (hu : u ∈ s.vertices) : childCount (attach s u) u = childCount s u + 1 := by
  rw [childCount, children_attach, ite_eq_left rfl, Finset.card_insert_of_notMem]
  · rfl
  · intro hm
    exact hs.newChild_not_mem hu (Finset.mem_filter.mp hm).1

theorem childCount_attach_of_ne (s : State) {u v : Address} (hvu : v ≠ u) :
    childCount (attach s u) v = childCount s v := by
  rw [childCount, children_attach, ite_eq_right hvu]
  rfl

theorem Valid.children_attach_new {s : State} (hs : Valid s) {u : Address}
    (hu : u ∈ s.vertices) : children (attach s u) (newChild s u) = ∅ := by
  rw [children_attach, ite_eq_right (newChild_ne_parent s u)]
  exact hs.children_eq_empty_of_not_mem (hs.newChild_not_mem hu)

theorem Valid.childCount_attach_new {s : State} (hs : Valid s) {u : Address}
    (hu : u ∈ s.vertices) : childCount (attach s u) (newChild s u) = 0 := by
  rw [childCount, hs.children_attach_new hu, Finset.card_empty]

theorem Valid.attach {s : State} (hs : Valid s) {u : Address} (hu : u ∈ s.active) :
    Valid (PlaneForward.attach s u) := by
  have huV := hs.active_subset hu
  constructor
  · exact Finset.mem_insert_of_mem hs.root_mem
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hs.active_subset hv)
  · intro v w hvw
    rcases Finset.mem_insert.mp hvw with hnew | hold
    · have hp : v <+: u ++ [childCount s u + 1] := ⟨w, hnew⟩
      rcases List.prefix_concat_iff.mp hp with hv | hv
      · exact Finset.mem_insert.mpr (Or.inl hv)
      · obtain ⟨a, ha⟩ := hv
        exact Finset.mem_insert_of_mem (hs.prefix_closed v a (ha.symm ▸ huV))
    · exact Finset.mem_insert_of_mem (hs.prefix_closed v w hold)
  · intro v hv j
    by_cases hnew : v = newChild s u
    · subst v
      rw [hs.childCount_attach_new huV]
      constructor
      · intro hvj
        have hm : newChild s u ++ [j] ∈ children (PlaneForward.attach s u) (newChild s u) :=
          Finset.mem_filter.mpr ⟨hvj, j, rfl⟩
        rw [hs.children_attach_new huV] at hm
        exact (Finset.notMem_empty _ hm).elim
      · intro hj
        omega
    · have hvV : v ∈ s.vertices := (Finset.mem_insert.mp hv).resolve_left hnew
      by_cases hvu : v = u
      · subst v
        rw [hs.childCount_attach_self huV]
        change (u ++ [j] ∈ insert (newChild s u) s.vertices) ↔ _
        rw [Finset.mem_insert, hs.children_iff u huV j]
        simp only [newChild, List.append_singleton_inj, true_and]
        omega
      · rw [childCount_attach_of_ne s hvu]
        have hne : v ++ [j] ≠ newChild s u := by
          intro he
          exact hvu (List.append_singleton_inj.mp he).1
        change (v ++ [j] ∈ insert (newChild s u) s.vertices) ↔ _
        rw [Finset.mem_insert, or_iff_right hne]
        exact hs.children_iff v hvV j

theorem Valid.step {s : State} (hs : Valid s) (sign : Bool) (u : Address) :
    Valid (PlaneForward.step s sign u) := by
  by_cases hu : u ∈ s.active
  · rw [PlaneForward.step, ite_eq_left hu]
    cases sign
    · exact hs.freeze u
    · exact hs.attach hu
  · rw [PlaneForward.step, ite_eq_right hu]
    exact hs

end HeightPaper.PlaneForward
