module

public import HeightPaper.Combinatorics.PlaneTreeGeometry
public import Mathlib.Data.Set.Card

/-!
# Genuine vertex counts and first-child decomposition for finite plane trees

The deterministic geometry is adapted from the sibling `freezing1` project,
with its stochastic imports removed.
-/

@[expose] public section

namespace HeightPaper.PlaneTree

open Set
open scoped Classical

set_option backward.isDefEq.respectTransparency false

def FiniteVertices (T : Tree) : Prop := {u : Address | Present T u}.Finite

noncomputable def finiteVertexCount (T : Tree) : ℕ := {u : Address | Present T u}.ncard

theorem present_leaf_iff (u : Address) : Present leaf u ↔ u = [] := by
  cases u with
  | nil => simp
  | cons j u =>
    constructor
    · intro h
      obtain ⟨hj, hzero, _⟩ := (present_cons leaf j u).mp h
      change j ≤ 0 at hzero
      omega
    · intro h
      cases h

theorem present_leaf_set : {u : Address | Present leaf u} = {[]} := by
  ext u
  exact present_leaf_iff u

theorem finiteVertices_leaf : FiniteVertices leaf := by
  change {u : Address | Present leaf u}.Finite
  rw [present_leaf_set]
  exact Set.finite_singleton _

theorem finiteVertexCount_leaf : finiteVertexCount leaf = 1 := by
  rw [finiteVertexCount, present_leaf_set, Set.ncard_singleton]

theorem finiteVertexCount_pos {T : Tree} (hT : FiniteVertices T) : 0 < finiteVertexCount T :=
  (Set.ncard_pos hT).mpr ⟨[], present_nil T⟩

theorem finiteVertices_child {T : Tree} (hT : FiniteVertices T) {j : ℕ}
    (hj : 1 ≤ j ∧ j ≤ degree T) : FiniteVertices (child T j) := by
  have hi : (List.cons j '' {u : Address | Present (child T j) u}) ⊆ {u | Present T u} := by
    rintro _ ⟨u, hu, rfl⟩
    exact (present_cons T j u).mpr ⟨hj.1, hj.2, hu⟩
  exact (hT.subset hi).of_finite_image (fun _ _ _ _ h => (List.cons.inj h).2)

theorem finiteVertexCount_child_le {T : Tree} (hT : FiniteVertices T) {j : ℕ}
    (hj : 1 ≤ j ∧ j ≤ degree T) : finiteVertexCount (child T j) ≤ finiteVertexCount T := by
  have hi : (List.cons j '' {u : Address | Present (child T j) u}) ⊆ {u | Present T u} := by
    rintro _ ⟨u, hu, rfl⟩
    exact (present_cons T j u).mpr ⟨hj.1, hj.2, hu⟩
  rw [finiteVertexCount, ← Set.ncard_image_of_injective _
    (show Function.Injective (List.cons j) from fun _ _ h => (List.cons.inj h).2)]
  exact Set.ncard_le_ncard hi hT

def graftRightAddress : Address → Address
  | [] => []
  | j :: u => (j + 1) :: u

theorem graftRightAddress_injective : Function.Injective graftRightAddress := by
  intro u v h
  cases u <;> cases v <;> simp_all [graftRightAddress]

theorem present_graftRightAddress (A B : Tree) {u : Address} (hu : Present B u) :
    Present (graft A B) (graftRightAddress u) := by
  cases u with
  | nil => trivial
  | cons j u =>
    obtain ⟨hj, hdeg, htail⟩ := (present_cons B j u).mp hu
    simp only [graftRightAddress, present_cons, degree_graft, child_succ_graft A B hj]
    exact ⟨by omega, by omega, htail⟩

theorem present_graft_set (A B : Tree) :
    {u : Address | Present (graft A B) u} =
      List.cons 1 '' {u : Address | Present A u} ∪
        graftRightAddress '' {u : Address | Present B u} := by
  ext u
  constructor
  · intro hu
    cases u with
    | nil => exact Or.inr ⟨[], trivial, rfl⟩
    | cons j u =>
      obtain ⟨hj, hdeg, htail⟩ := (present_cons (graft A B) j u).mp hu
      by_cases hj1 : j = 1
      · subst j
        exact Or.inl ⟨u, by
          change Present A u
          simpa only [child_one_graft] using htail, rfl⟩
      · have hj' : 1 ≤ j - 1 := by omega
        have he : j = (j - 1) + 1 := by omega
        have hv : Present B ((j - 1) :: u) := by
          refine (present_cons B (j - 1) u).mpr ⟨hj', ?_, ?_⟩
          · simpa only [degree_graft] using (show j - 1 ≤ degree B from by
              change j ≤ degree B + 1 at hdeg
              omega)
          · rw [he, child_succ_graft A B hj'] at htail
            exact htail
        exact Or.inr ⟨(j - 1) :: u, hv, by simp only [graftRightAddress]; congr 1; omega⟩
  · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · change Present (graft A B) (1 :: v)
      change Present A v at hv
      exact (present_cons _ _ _).mpr ⟨le_rfl, by simp, by simpa only [child_one_graft] using hv⟩
    · exact present_graftRightAddress A B hv

theorem graft_present_images_disjoint (A B : Tree) :
    Disjoint (List.cons 1 '' {u : Address | Present A u})
      (graftRightAddress '' {u : Address | Present B u}) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨u, _, hu⟩ ⟨v, hv, hve⟩
  cases v with
  | nil =>
    have he : (1 : ℕ) :: u = ([] : Address) := hu.trans hve.symm
    cases he
  | cons j v =>
    have hj := ((present_cons B j v).mp hv).1
    have he : (j + 1) :: v = 1 :: u := hve.trans hu.symm
    have hh := (List.cons.inj he).1
    omega

theorem finiteVertices_graft {A B : Tree} (hA : FiniteVertices A) (hB : FiniteVertices B) :
    FiniteVertices (graft A B) := by
  change {u : Address | Present (graft A B) u}.Finite
  rw [present_graft_set]
  exact (hA.image (List.cons 1)).union (hB.image graftRightAddress)

theorem finiteVertexCount_graft {A B : Tree} (hA : FiniteVertices A) (hB : FiniteVertices B) :
    finiteVertexCount (graft A B) = finiteVertexCount A + finiteVertexCount B := by
  rw [finiteVertexCount, present_graft_set,
    Set.ncard_union_eq (graft_present_images_disjoint A B)
      (hA.image (List.cons 1)) (hB.image graftRightAddress),
    Set.ncard_image_of_injective _
      (show Function.Injective (List.cons 1) from fun _ _ h => (List.cons.inj h).2),
    Set.ncard_image_of_injective _ graftRightAddress_injective]
  rfl

theorem finiteVertices_dropFirst {T : Tree} (hT : FiniteVertices T) :
    FiniteVertices (dropFirst T) := by
  by_cases hd : degree T = 0
  · rw [eq_leaf_of_degree_zero hd]
    have he : dropFirst leaf = leaf := eq_leaf_of_degree_zero (by simp)
    rw [he]
    exact finiteVertices_leaf
  · have hdecomp := graft_child_dropFirst (Nat.pos_of_ne_zero hd)
    have hi : (graftRightAddress '' {u : Address | Present (dropFirst T) u}) ⊆
        {u : Address | Present T u} := by
      rintro u ⟨v, hv, rfl⟩
      change Present T (graftRightAddress v)
      rw [← hdecomp]
      exact present_graftRightAddress (child T 1) (dropFirst T) hv
    exact (hT.subset hi).of_finite_image graftRightAddress_injective.injOn

theorem finiteVertexCount_first_split {T : Tree} (hT : FiniteVertices T)
    (hd : 0 < degree T) :
    finiteVertexCount T = finiteVertexCount (child T 1) + finiteVertexCount (dropFirst T) := by
  nth_rw 1 [← graft_child_dropFirst hd]
  exact finiteVertexCount_graft (finiteVertices_child hT ⟨le_rfl, hd⟩) (finiteVertices_dropFirst hT)

end HeightPaper.PlaneTree
