module

public import HeightPaper.Combinatorics.PlaneTreeGeometry
public import Mathlib.Tactic.DeriveCountable

/-!
Adapted from the generic plane-tree utilities in the sibling `freezing1`
project, using the same pinned Lean and Mathlib 4.35.0.

# Countable finite states for the chronologically ordered plane process

The raw state consists of two finite address sets. Validity is supplied by
the actual-tree projection, rather than made a hidden assumption in the
Markov kernel's state space. Transitions are defined on every raw state.
-/

@[expose] public section

namespace HeightPaper.PlaneForward

open PlaneTree
open scoped Classical

structure State where
  vertices : Finset Address
  active : Finset Address
  deriving DecidableEq, Countable

instance : MeasurableSpace State := ⊤
instance : MeasurableSingletonClass State := ⟨fun _ => trivial⟩

def initial : State := ⟨{[]}, {[]}⟩

noncomputable def children (s : State) (u : Address) : Finset Address :=
  s.vertices.filter fun w => ∃ j : ℕ, w = u ++ [j]

noncomputable def childCount (s : State) (u : Address) : ℕ := (children s u).card

noncomputable def newChild (s : State) (u : Address) : Address :=
  u ++ [childCount s u + 1]

noncomputable def attach (s : State) (u : Address) : State :=
  ⟨insert (newChild s u) s.vertices, insert (newChild s u) s.active⟩

def freeze (s : State) (u : Address) : State := ⟨s.vertices, s.active.erase u⟩

noncomputable def step (s : State) (sign : Bool) (u : Address) : State :=
  if u ∈ s.active then if sign then attach s u else freeze s u else s

theorem step_of_not_mem {s : State} {u : Address} (hu : u ∉ s.active) (sign : Bool) :
    step s sign u = s := by simp [step, hu]

theorem step_of_active_empty {s : State} (hs : s.active = ∅) (sign : Bool) (u : Address) :
    step s sign u = s := by simp [step, hs]

theorem attach_active_card_le (s : State) (u : Address) :
    (attach s u).active.card ≤ s.active.card + 1 := Finset.card_insert_le _ _

theorem freeze_active_card_le (s : State) (u : Address) :
    (freeze s u).active.card ≤ s.active.card := Finset.card_erase_le

theorem step_active_card_le (s : State) (sign : Bool) (u : Address) :
    (step s sign u).active.card ≤ s.active.card + 1 := by
  by_cases hu : u ∈ s.active
  · rw [step, ite_eq_left hu]
    cases sign
    · exact (freeze_active_card_le s u).trans (Nat.le_succ _)
    · exact attach_active_card_le s u
  · rw [step, ite_eq_right hu]
    exact Nat.le_succ _

theorem freeze_ne_of_mem {s : State} {u : Address} (hu : u ∈ s.active) :
    freeze s u ≠ s := by
  intro he
  have ha := congrArg State.active he
  have hn : u ∉ (freeze s u).active := Finset.notMem_erase _ _
  exact hn (ha.symm ▸ hu)

theorem vertices_subset_step (s : State) (sign : Bool) (u : Address) :
    s.vertices ⊆ (step s sign u).vertices := by
  by_cases hu : u ∈ s.active
  · rw [step, ite_eq_left hu]
    cases sign
    · exact Finset.Subset.refl _
    · exact Finset.subset_insert _ _
  · rw [step, ite_eq_right hu]

end HeightPaper.PlaneForward
