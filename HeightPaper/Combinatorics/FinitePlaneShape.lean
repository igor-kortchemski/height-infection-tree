module

public import HeightPaper.Combinatorics.PlaneCompletionPotential

/-!
# Countable finite ordered tree shapes

Activity is forgotten in a finite shape. The complete vertex support and
all its ordered parent edges remain; global numeric birth labels do not.
-/

@[expose] public section

namespace HeightPaper.PlaneForward

open PlaneTree MeasureTheory
open scoped Classical

def forgetActivity (s : State) : State := ⟨s.vertices, ∅⟩

theorem Valid.forgetActivity {s : State} (hs : Valid s) : Valid (forgetActivity s) := by
  constructor
  · exact hs.root_mem
  · exact Finset.empty_subset _
  · exact hs.prefix_closed
  · exact hs.children_iff

abbrev FiniteShape := {s : State // Valid s ∧ s.active = ∅}

instance : MeasurableSpace FiniteShape := ⊤
instance : MeasurableSingletonClass FiniteShape := ⟨fun _ ↦ trivial⟩

def leafShape : FiniteShape :=
  ⟨forgetActivity initial, initial_valid.forgetActivity, rfl⟩

noncomputable def toFiniteShape (s : State) : FiniteShape :=
  if hs : Valid s then ⟨forgetActivity s, hs.forgetActivity, rfl⟩ else leafShape

theorem toFiniteShape_vertices {s : State} (hs : Valid s) : (toFiniteShape s).1.vertices = s.vertices := by
  rw [toFiniteShape, dite_eq_left hs]
  rfl

theorem finiteShape_ext {t u : FiniteShape} (h : t.1.vertices = u.1.vertices) : t = u := by
  apply Subtype.ext
  cases ht : t.1 with
  | mk V A =>
      cases hu : u.1 with
      | mk W B =>
          have hA : A = ∅ := by simpa only [ht] using t.2.2
          have hB : B = ∅ := by simpa only [hu] using u.2.2
          simp only [ht, hu] at h ⊢
          cases h
          rw [hA, hB]

theorem toFiniteShape_eq_iff {s : State} (hs : Valid s) (t : FiniteShape) :
    toFiniteShape s = t ↔ s.vertices = t.1.vertices := by
  constructor
  · intro he
    rw [← toFiniteShape_vertices hs, he]
  · intro he
    exact finiteShape_ext ((toFiniteShape_vertices hs).trans he)

theorem toFiniteShape_self (t : FiniteShape) : toFiniteShape t.1 = t :=
  (toFiniteShape_eq_iff t.2.1 t).mpr rfl

noncomputable def FiniteShape.tree (t : FiniteShape) : Tree := shape t.1

theorem FiniteShape.tree_injective : Function.Injective FiniteShape.tree := by
  intro t u he
  apply finiteShape_ext
  ext v
  rw [t.2.1.mem_vertices_iff_present, u.2.1.mem_vertices_iff_present]
  change Present t.tree v ↔ Present u.tree v
  rw [he]

theorem FiniteShape.vertices_finite (t : FiniteShape) : {u | Present t.tree u}.Finite := by
  have he : {u | Present t.tree u} = (t.1.vertices : Set Address) := by
    ext u
    exact (t.2.1.mem_vertices_iff_present u).symm
  rw [he]
  exact Finset.finite_toSet _

def FiniteShape.size (t : FiniteShape) : ℕ := t.1.vertices.card

theorem FiniteShape.size_pos (t : FiniteShape) : 0 < t.size :=
  Finset.card_pos.mpr ⟨[], t.2.1.root_mem⟩

theorem completionPotential_of_empty_shape {s : State} (hs : Valid s) (he : s.active = ∅)
    (t : FiniteShape) (a : ℝ) :
    completionPotential t.1 a s = if toFiniteShape s = t then 1 else 0 := by
  rw [completionPotential_of_empty hs t.2.1 he a]
  simp only [toFiniteShape_eq_iff hs t]

end HeightPaper.PlaneForward
