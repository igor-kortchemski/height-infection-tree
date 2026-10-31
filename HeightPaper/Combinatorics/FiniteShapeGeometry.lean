module

public import HeightPaper.Combinatorics.FinitePlaneShape
public import HeightPaper.Combinatorics.FinitePlaneGeometry

/-!
# Finite shapes and the genuine locally finite plane-tree space

The two representations are inverses on finite trees. Binary grafting and
the first-child decomposition therefore have their usual tree meaning.
-/

@[expose] public section

namespace HeightPaper.PlaneForward

open PlaneTree
open scoped Classical

noncomputable def stateOfFiniteTree (T : Tree) (hT : FiniteVertices T) : State :=
  ⟨hT.toFinset, ∅⟩

theorem mem_stateOfFiniteTree_vertices (T : Tree) (hT : FiniteVertices T) (u : Address) :
    u ∈ (stateOfFiniteTree T hT).vertices ↔ Present T u := by
  exact Set.Finite.mem_toFinset (show {v | Present T v}.Finite from hT)

theorem stateOfFiniteTree_children (T : Tree) (hT : FiniteVertices T) (u : Address) :
    children (stateOfFiniteTree T hT) u =
      if Present T u then (Finset.Icc 1 (T.val u)).image (fun j ↦ u ++ [j]) else ∅ := by
  ext w
  by_cases hu : Present T u
  · simp only [ite_eq_left hu, children, Finset.mem_filter,
      mem_stateOfFiniteTree_vertices, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨hw, j, rfl⟩
      have hj := (present_append_singleton T u j).mp hw
      exact ⟨j, hj.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(present_append_singleton T u j).mpr ⟨hu, hj⟩, j, rfl⟩
  · simp only [ite_eq_right hu, Finset.notMem_empty, iff_false]
    intro hw
    obtain ⟨hw, j, rfl⟩ := Finset.mem_filter.mp hw
    have hp : Present T (u ++ [j]) := (mem_stateOfFiniteTree_vertices T hT _).mp hw
    exact hu ((present_append_singleton T u j).mp hp).1

theorem stateOfFiniteTree_childCount (T : Tree) (hT : FiniteVertices T) (u : Address) :
    childCount (stateOfFiniteTree T hT) u = T.val u := by
  rw [childCount, stateOfFiniteTree_children]
  by_cases hu : Present T u
  · rw [ite_eq_left hu, Finset.card_image_of_injective]
    · rw [Nat.card_Icc]
      omega
    · intro i j he
      exact List.singleton_inj.mp (List.append_cancel_left he)
  · rw [ite_eq_right hu, Finset.card_empty]
    exact (not_present_offspring_zero T u hu).symm

theorem stateOfFiniteTree_valid (T : Tree) (hT : FiniteVertices T) : Valid (stateOfFiniteTree T hT) := by
  constructor
  · exact (mem_stateOfFiniteTree_vertices T hT []).mpr (present_nil T)
  · exact Finset.empty_subset _
  · intro u v huv
    exact (mem_stateOfFiniteTree_vertices T hT _).mpr
      (present_of_prefix ⟨v, rfl⟩ ((mem_stateOfFiniteTree_vertices T hT _).mp huv))
  · intro u hu j
    have hu' : Present T u := (mem_stateOfFiniteTree_vertices T hT _).mp hu
    rw [stateOfFiniteTree_childCount]
    rw [mem_stateOfFiniteTree_vertices, present_append_singleton]
    exact and_iff_right hu'

noncomputable def finiteShapeOfTree (T : Tree) (hT : FiniteVertices T) : FiniteShape :=
  ⟨stateOfFiniteTree T hT, stateOfFiniteTree_valid T hT, rfl⟩

theorem finiteShapeOfTree_tree (T : Tree) (hT : FiniteVertices T) : (finiteShapeOfTree T hT).tree = T := by
  apply Subtype.ext
  funext u
  change (shape (stateOfFiniteTree T hT)).val u = T.val u
  rw [(stateOfFiniteTree_valid T hT).shape_offspring, stateOfFiniteTree_childCount]

theorem FiniteShape.vertexCount_tree (t : FiniteShape) : finiteVertexCount t.tree = t.size := by
  have he : {u | Present t.tree u} = (t.1.vertices : Set Address) := by
    ext u
    exact (t.2.1.mem_vertices_iff_present u).symm
  rw [finiteVertexCount, he, Set.ncard_coe_finset]
  rfl

theorem finiteShapeOfTree_size (T : Tree) (hT : FiniteVertices T) :
    (finiteShapeOfTree T hT).size = finiteVertexCount T := by
  rw [← FiniteShape.vertexCount_tree, finiteShapeOfTree_tree]

theorem finiteShapeOfTree_self (t : FiniteShape) : finiteShapeOfTree t.tree t.vertices_finite = t := by
  apply FiniteShape.tree_injective
  exact finiteShapeOfTree_tree _ _

noncomputable def graftShapes (t u : FiniteShape) : FiniteShape :=
  finiteShapeOfTree (graft t.tree u.tree) (finiteVertices_graft t.vertices_finite u.vertices_finite)

theorem graftShapes_tree (t u : FiniteShape) : (graftShapes t u).tree = graft t.tree u.tree :=
  finiteShapeOfTree_tree _ _

theorem graftShapes_size (t u : FiniteShape) : (graftShapes t u).size = t.size + u.size := by
  rw [graftShapes, finiteShapeOfTree_size, finiteVertexCount_graft t.vertices_finite u.vertices_finite,
    t.vertexCount_tree, u.vertexCount_tree]

theorem graftShapes_injective : Function.Injective (fun z : FiniteShape × FiniteShape ↦ graftShapes z.1 z.2) := by
  intro x y he
  have htree := congrArg FiniteShape.tree he
  rw [graftShapes_tree, graftShapes_tree] at htree
  apply Prod.ext
  · apply FiniteShape.tree_injective
    simpa only [child_one_graft] using congrArg (fun T ↦ child T 1) htree
  · apply FiniteShape.tree_injective
    simpa only [dropFirst_graft] using congrArg dropFirst htree

theorem leafShape_tree : leafShape.tree = leaf := by
  apply Subtype.ext
  funext u
  rw [show leafShape.tree = shape (forgetActivity initial) from rfl,
    initial_valid.forgetActivity.shape_offspring]
  exact childCount_initial u

theorem leafShape_size : leafShape.size = 1 := rfl

theorem finiteShape_split (t : FiniteShape) :
    t = leafShape ∨ ∃ A B : FiniteShape, graftShapes A B = t := by
  by_cases hd : degree t.tree = 0
  · left
    apply FiniteShape.tree_injective
    rw [eq_leaf_of_degree_zero hd, leafShape_tree]
  · right
    have hp := Nat.pos_of_ne_zero hd
    let A := finiteShapeOfTree (child t.tree 1) (finiteVertices_child t.vertices_finite ⟨le_rfl, hp⟩)
    let B := finiteShapeOfTree (dropFirst t.tree) (finiteVertices_dropFirst t.vertices_finite)
    refine ⟨A, B, ?_⟩
    apply FiniteShape.tree_injective
    rw [graftShapes_tree, show A.tree = child t.tree 1 from finiteShapeOfTree_tree _ _,
      show B.tree = dropFirst t.tree from finiteShapeOfTree_tree _ _, graft_child_dropFirst hp]

end HeightPaper.PlaneForward
