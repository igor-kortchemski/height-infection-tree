module

public import HeightPaper.Combinatorics.FiniteShapeGeometry

/-!
# Root-height-zero conventions and the first-child height decomposition
-/

@[expose] public section

namespace HeightPaper.PlaneForward

open PlaneTree

def FiniteShape.height (t : FiniteShape) : ℕ := t.1.vertices.sup List.length

def belowLevel (t : FiniteShape) (h : ℕ) : Prop := ∀ u ∈ t.1.vertices, u.length < h

theorem belowLevel_iff_tree (t : FiniteShape) (h : ℕ) :
    belowLevel t h ↔ ∀ u, Present t.tree u → u.length < h := by
  simp only [belowLevel, t.2.1.mem_vertices_iff_present]
  rfl

theorem not_belowLevel_zero (t : FiniteShape) : ¬belowLevel t 0 := by
  intro ht
  exact Nat.not_lt_zero _ (ht [] t.2.1.root_mem)

theorem belowLevel_leaf_succ (h : ℕ) : belowLevel leafShape (h + 1) := by
  rw [belowLevel_iff_tree, leafShape_tree]
  intro u hu
  have he := (present_leaf_iff u).mp hu
  subst u
  simp

theorem belowLevel_graft (A B : FiniteShape) (h : ℕ) :
    belowLevel (graftShapes A B) (h + 1) ↔ belowLevel A h ∧ belowLevel B (h + 1) := by
  rw [belowLevel_iff_tree, belowLevel_iff_tree, belowLevel_iff_tree, graftShapes_tree]
  have hlen (u : Address) : (graftRightAddress u).length = u.length := by cases u <;> rfl
  constructor
  · intro hg
    constructor
    · intro u hu
      have hp : Present (graft A.tree B.tree) (1 :: u) := by
        exact (present_cons _ _ _).mpr ⟨by omega, by simp, by simpa only [child_one_graft] using hu⟩
      have hh := hg (1 :: u) hp
      simp only [List.length_cons] at hh
      omega
    · intro u hu
      have hh := hg (graftRightAddress u) (present_graftRightAddress A.tree B.tree hu)
      rwa [hlen] at hh
  · rintro ⟨hA, hB⟩ u hu
    change u ∈ {v | Present (graft A.tree B.tree) v} at hu
    rw [present_graft_set] at hu
    rcases hu with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · have := hA v hv
      simp only [List.length_cons]
      omega
    · rw [hlen]
      exact hB v hv

theorem belowLevel_iff_height_lt (t : FiniteShape) (h : ℕ) : belowLevel t h ↔ t.height < h := by
  by_cases hh : h = 0
  · subst h
    simp only [not_belowLevel_zero, Nat.not_lt_zero]
  · have hhpos : 0 < h := Nat.pos_of_ne_zero hh
    change (∀ u ∈ t.1.vertices, u.length < h) ↔ t.1.vertices.sup List.length < h
    simp only [Nat.lt_iff_le_pred hhpos, Finset.sup_le_iff]

end HeightPaper.PlaneForward
