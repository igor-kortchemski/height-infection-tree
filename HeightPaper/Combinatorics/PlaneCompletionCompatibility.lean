module

public import HeightPaper.Combinatorics.PlaneStateUpdates

/-!
# Compatibility with a finite target plane tree

A frozen vertex must already have all its target children. Active vertices
may still be missing children. This predicate is the support condition of
the completion potential; it is not an assumption on a stochastic law.
-/

@[expose] public section

namespace HeightPaper.PlaneForward

open PlaneTree
open scoped Classical

def CompletionCompatible (s t : State) : Prop :=
  s.vertices ⊆ t.vertices ∧
    ∀ u ∈ s.vertices, u ∉ s.active → childCount s u = childCount t u

theorem children_mono_of_vertices_subset {s t : State} (h : s.vertices ⊆ t.vertices) (u : Address) :
    children s u ⊆ children t u := by
  intro x hx
  obtain ⟨hx, hj⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨h hx, hj⟩

theorem CompletionCompatible.childCount_le {s t : State} (h : CompletionCompatible s t) (u : Address) :
    childCount s u ≤ childCount t u := Finset.card_le_card (children_mono_of_vertices_subset h.1 u)

theorem childCount_freeze (s : State) (u v : Address) : childCount (freeze s u) v = childCount s v := rfl

theorem CompletionCompatible.freeze_iff {s t : State} (hs : Valid s) {u : Address} (hu : u ∈ s.active) :
    CompletionCompatible (freeze s u) t ↔ CompletionCompatible s t ∧ childCount s u = childCount t u := by
  constructor
  · intro h
    refine ⟨⟨h.1, fun v hv hn ↦ ?_⟩, ?_⟩
    · exact h.2 v hv (fun hm ↦ hn (Finset.mem_of_mem_erase hm))
    · exact h.2 u (hs.active_subset hu) (Finset.notMem_erase _ _)
  · rintro ⟨h, he⟩
    refine ⟨h.1, ?_⟩
    intro v hv hn
    by_cases hvu : v = u
    · subst v
      exact he
    · exact h.2 v hv (fun hm ↦ hn (Finset.mem_erase.mpr ⟨hvu, hm⟩))

theorem CompletionCompatible.of_attach {s t : State} (hs : Valid s) {u : Address} (hu : u ∈ s.active)
    (h : CompletionCompatible (attach s u) t) : CompletionCompatible s t := by
  have huV := hs.active_subset hu
  refine ⟨(Finset.subset_insert _ _).trans h.1, ?_⟩
  intro v hv hn
  have hvu : v ≠ u := fun he ↦ hn (he ▸ hu)
  have hvnew : v ≠ newChild s u := fun he ↦ hs.newChild_not_mem huV (he ▸ hv)
  have hnot : v ∉ (attach s u).active := by
    simpa only [attach, Finset.mem_insert] using not_or_intro hvnew hn
  have he := h.2 v (Finset.mem_insert_of_mem hv) hnot
  rw [childCount_attach_of_ne s hvu] at he
  exact he

theorem CompletionCompatible.attach_iff {s t : State} (hs : Valid s) (ht : Valid t)
    {u : Address} (hu : u ∈ s.active) :
    CompletionCompatible (attach s u) t ↔ CompletionCompatible s t ∧ childCount s u < childCount t u := by
  have huV := hs.active_subset hu
  constructor
  · intro h
    have hc := CompletionCompatible.of_attach hs hu h
    have hnew : newChild s u ∈ t.vertices := h.1 (Finset.mem_insert_self _ _)
    have hi := (ht.children_iff u (hc.1 huV) (childCount s u + 1)).mp hnew
    exact ⟨hc, by omega⟩
  · rintro ⟨h, hlt⟩
    have hnew : newChild s u ∈ t.vertices :=
      (ht.children_iff u (h.1 huV) (childCount s u + 1)).mpr ⟨by omega, by omega⟩
    refine ⟨Finset.insert_subset hnew h.1, ?_⟩
    intro v hv hn
    have hvnew : v ≠ newChild s u := by
      intro he
      exact hn (he ▸ Finset.mem_insert_self _ _)
    have hvold : v ∈ s.vertices := (Finset.mem_insert.mp hv).resolve_left hvnew
    have hvnot : v ∉ s.active := fun hm ↦ hn (Finset.mem_insert_of_mem hm)
    have hvu : v ≠ u := fun he ↦ hvnot (he ▸ hu)
    rw [childCount_attach_of_ne s hvu]
    exact h.2 v hvold hvnot

theorem CompletionCompatible.initial {t : State} (ht : Valid t) : CompletionCompatible initial t := by
  constructor
  · exact Finset.singleton_subset_iff.mpr ht.root_mem
  · intro u hu hn
    exact False.elim (hn hu)

theorem CompletionCompatible.eq_vertices_of_empty {s t : State}
    (hs : Valid s) (ht : Valid t) (h : CompletionCompatible s t) (he : s.active = ∅) : s.vertices = t.vertices := by
  apply Finset.Subset.antisymm h.1
  intro u hu
  induction u using List.reverseRecOn with
  | nil => exact hs.root_mem
  | append_singleton u j ih =>
      have huT := ht.prefix_closed u [j] hu
      have huS := ih huT
      have hj := (ht.children_iff u huT j).mp hu
      apply (hs.children_iff u huS j).mpr
      rw [h.2 u huS (by simp [he])]
      exact hj

end HeightPaper.PlaneForward
