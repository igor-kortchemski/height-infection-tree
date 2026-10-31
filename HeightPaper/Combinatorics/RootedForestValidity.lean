module

public import HeightPaper.Combinatorics.RootedForestEmbedding

/-!
# Rooted forest validity and transport through a vertex/edge isomorphism
-/

@[expose] public section

namespace HeightPaper.RootedForest

variable {α β : Type*} {N : ℕ}

structure WellRooted (A : RootedForest α N) : Prop where
  root_mem : ∀ i, A.root i ∈ A.vertices
  root_injective : Function.Injective A.root
  edge_vertices : ∀ x y, A.edge x y → x ∈ A.vertices ∧ y ∈ A.vertices
  no_edge_to_root : ∀ x i, ¬A.edge x (A.root i)
  unique_parent : ∀ x ∈ A.vertices, (∀ i, x ≠ A.root i) → ∃! p, A.edge p x
  reachable : ∀ x ∈ A.vertices, ∃ i, Relation.ReflTransGen A.edge (A.root i) x
  acyclic : ∀ x, ¬Relation.TransGen A.edge x x

theorem Embedding.map_transGen {A : RootedForest α N} {B : RootedForest β N}
    (e : Embedding A B) {x y : α} (h : Relation.TransGen A.edge x y) :
    Relation.TransGen B.edge (e.map x) (e.map y) := by
  induction h with
  | single h => exact Relation.TransGen.single (e.map_edge _ _ h)
  | tail hxy hyz ih => exact ih.tail (e.map_edge _ _ hyz)

theorem WellRooted.of_embedding [Nonempty α]
    {A : RootedForest α N} {B : RootedForest β N} (hA : WellRooted A) (e : Embedding A B)
    (hsurj : Set.SurjOn e.map A.vertices B.vertices)
    (hedges : ∀ x y, B.edge x y → x ∈ B.vertices ∧ y ∈ B.vertices)
    (hreflect : ∀ x ∈ A.vertices, ∀ y ∈ A.vertices,
      B.edge (e.map x) (e.map y) → A.edge x y) : WellRooted B := by
  constructor
  · exact fun i ↦ e.map_root i ▸ e.mapsTo (hA.root_mem i)
  · intro i j he
    apply hA.root_injective
    apply e.injOn (hA.root_mem i) (hA.root_mem j)
    rw [e.map_root, e.map_root]
    exact he
  · exact hedges
  · intro y i he
    have hy := (hedges y (B.root i) he).1
    obtain ⟨x, hx, hxy⟩ := hsurj hy
    apply hA.no_edge_to_root x i
    apply hreflect x hx (A.root i) (hA.root_mem i)
    rw [hxy, e.map_root]
    exact he
  · intro y hy hyr
    obtain ⟨x, hx, hxy⟩ := hsurj hy
    have hxr : ∀ i, x ≠ A.root i := by
      intro i he
      apply hyr i
      rw [← hxy, he, e.map_root]
    obtain ⟨p, hp, huniq⟩ := hA.unique_parent x hx hxr
    refine ⟨e.map p, ?_, ?_⟩
    · rw [← hxy]
      exact e.map_edge p x hp
    · intro q hq
      obtain ⟨v, hv, hvq⟩ := hsurj (hedges q y hq).1
      have he : A.edge v x := by
        apply hreflect v hv x hx
        rw [hvq, hxy]
        exact hq
      rw [← hvq, huniq v he]
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hsurj hy
    obtain ⟨i, hpath⟩ := hA.reachable x hx
    refine ⟨i, ?_⟩
    have hp := (e.mapsTo_component i ⟨hx, hpath⟩).2
    rwa [hxy] at hp
  · intro y hcycle
    let f := e.reverse hsurj hA.root_mem hedges hreflect
    exact hA.acyclic (f.map y) (f.map_transGen hcycle)

end HeightPaper.RootedForest
