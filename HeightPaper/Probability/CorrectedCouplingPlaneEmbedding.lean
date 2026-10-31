module

public import HeightPaper.Probability.CorrectedCouplingChronologicalEmbedding
public import HeightPaper.Probability.CorrectedCouplingForestPotential

/-!
# Rooted graph isomorphisms between finite labelled genealogies and their plane shapes

The plane forms carry the Bienaymé law. The shared numeric labels carry the
coupling inclusions. These explicit embeddings, in both directions, are the
bridge between the representations.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

open PlaneForward PlaneTree
open scoped Classical

def finiteGenealogyForest (N : ℕ) (s : CouplingGenealogy) : RootedForest ℕ N where
  vertices := s.carrier.vertices
  edge := fun x y ↦ y ∈ s.carrier.vertices ∧ y ∉ Finset.range N ∧ s.parent y = x
  root := Fin.val

def planeForest {N : ℕ} (T : Fin N → Tree) : RootedForest (Fin N × Address) N where
  vertices := {z | Present (T z.1) z.2}
  edge := fun a b ↦ a.1 = b.1 ∧ ∃ j : ℕ, b.2 = a.2 ++ [j] ∧ Present (T b.1) b.2
  root := fun i ↦ (i, [])

noncomputable def shapeForest {N : ℕ} (t : Fin N → FiniteShape) : RootedForest (Fin N × Address) N :=
  planeForest (fun i ↦ (t i).tree)

theorem planeForest_edge_vertices {N : ℕ} (T : Fin N → Tree)
    (a b : Fin N × Address) (he : (planeForest T).edge a b) :
    a ∈ (planeForest T).vertices ∧ b ∈ (planeForest T).vertices := by
  obtain ⟨hi, j, haddr, hb⟩ := he
  refine ⟨?_, hb⟩
  change Present (T a.1) a.2
  have hp : Present (T b.1) a.2 := present_of_prefix ⟨[j], haddr.symm⟩ hb
  rwa [hi]

noncomputable def componentRootIndex (N : ℕ) (hN : 0 < N) (s : CouplingGenealogy) (x : ℕ) : Fin N :=
  if h : s.rootOf (Finset.range N) x < N then ⟨s.rootOf (Finset.range N) x, h⟩ else ⟨0, hN⟩

theorem componentRootIndex_val (N : ℕ) (hN : 0 < N) (s : CouplingGenealogy)
    (hs : s.Valid (Finset.range N)) {x : ℕ} (hx : x ∈ s.carrier.vertices) :
    (componentRootIndex N hN s x).val = s.rootOf (Finset.range N) x := by
  have hr : s.rootOf (Finset.range N) x < N := Finset.mem_range.mp (s.rootOf_mem_roots hs hx)
  simp only [componentRootIndex, dite_eq_left hr]

noncomputable def genealogyPlaneMap (N : ℕ) (hN : 0 < N) (s : CouplingGenealogy) (x : ℕ) : Fin N × Address :=
  (componentRootIndex N hN s x, s.orderedAddress (Finset.range N) x)

theorem genealogyPlaneMap_mem (N : ℕ) (hN : 0 < N) (s : CouplingGenealogy)
    (hs : s.Valid (Finset.range N)) {x : ℕ} (hx : x ∈ s.carrier.vertices) :
    genealogyPlaneMap N hN s x ∈ (shapeForest (forestShape N s)).vertices := by
  let i := componentRootIndex N hN s x
  apply ((forestShape N s i).2.1.mem_vertices_iff_present _).mp
  change s.orderedAddress (Finset.range N) x ∈ (toFiniteShape (s.planeComponent (Finset.range N) i.val)).1.vertices
  rw [toFiniteShape_vertices (s.planeComponent_valid hs (Finset.mem_range.mpr i.isLt))]
  exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr
    ⟨hx, (componentRootIndex_val N hN s hs hx).symm⟩, rfl⟩

noncomputable def genealogyPlaneEmbedding (N : ℕ) (hN : 0 < N) (s : CouplingGenealogy)
    (hs : s.Valid (Finset.range N)) :
    RootedForest.Embedding (finiteGenealogyForest N s) (shapeForest (forestShape N s)) where
  map := genealogyPlaneMap N hN s
  mapsTo := fun _ hx ↦ genealogyPlaneMap_mem N hN s hs hx
  injOn := by
    intro x hx y hy he
    have hidx := congrArg (fun z : Fin N × Address ↦ z.1.val) he
    have haddr := congrArg Prod.snd he
    change (componentRootIndex N hN s x).val = (componentRootIndex N hN s y).val at hidx
    rw [componentRootIndex_val N hN s hs hx, componentRootIndex_val N hN s hs hy] at hidx
    exact s.rootedAddress_injOn hs hx hy (Prod.ext hidx haddr)
  map_root := by
    intro i
    have hi : i.val ∈ Finset.range N := Finset.mem_range.mpr i.isLt
    have hroot : s.rootOf (Finset.range N) i.val = i.val := by simp [CouplingGenealogy.rootOf, hi]
    apply Prod.ext
    · apply Fin.ext
      exact (componentRootIndex_val N hN s hs (hs.1 hi)).trans hroot
    · exact s.orderedAddress_root (Finset.range N) hi
  map_edge := by
    intro x y he
    obtain ⟨hy, hyN, hp⟩ := he
    have hx : x ∈ s.carrier.vertices := by
      have h := ((hs.2 y hy hyN).1)
      rwa [hp] at h
    have hroots : s.rootOf (Finset.range N) x = s.rootOf (Finset.range N) y := by
      rw [s.rootOf_parent hs hy hyN, hp]
    refine ⟨?_, couplingLabelRank (s.children (Finset.range N) x) y + 1, ?_, ?_⟩
    · apply Fin.ext
      exact (componentRootIndex_val N hN s hs hx).trans
        (hroots.trans (componentRootIndex_val N hN s hs hy).symm)
    · change s.orderedAddress (Finset.range N) y = s.orderedAddress (Finset.range N) x ++ [_]
      rw [s.orderedAddress_nonroot hs hy hyN, hp]
    · exact genealogyPlaneMap_mem N hN s hs hy

theorem genealogyPlaneMap_surjOn (N : ℕ) (hN : 0 < N) (s : CouplingGenealogy)
    (hs : s.Valid (Finset.range N)) :
    Set.SurjOn (genealogyPlaneMap N hN s) (finiteGenealogyForest N s).vertices
      (shapeForest (forestShape N s)).vertices := by
  rintro ⟨i, u⟩ hu
  have hmem : u ∈ (s.planeComponent (Finset.range N) i.val).vertices := by
    have hm := ((forestShape N s i).2.1.mem_vertices_iff_present u).mpr hu
    change u ∈ (toFiniteShape (s.planeComponent (Finset.range N) i.val)).1.vertices at hm
    rw [toFiniteShape_vertices (s.planeComponent_valid hs (Finset.mem_range.mpr i.isLt))] at hm
    exact hm
  obtain ⟨x, hx, haddr⟩ := Finset.mem_image.mp hmem
  obtain ⟨hxV, hxroot⟩ := Finset.mem_filter.mp hx
  refine ⟨x, hxV, ?_⟩
  apply Prod.ext
  · apply Fin.ext
    exact (componentRootIndex_val N hN s hs hxV).trans hxroot
  · exact haddr

theorem genealogyPlane_edge_reflects (N : ℕ) (hN : 0 < N) (s : CouplingGenealogy)
    (hs : s.Valid (Finset.range N)) (x : ℕ) (hx : x ∈ s.carrier.vertices)
    (y : ℕ) (hy : y ∈ s.carrier.vertices)
    (he : (shapeForest (forestShape N s)).edge (genealogyPlaneMap N hN s x) (genealogyPlaneMap N hN s y)) :
    (finiteGenealogyForest N s).edge x y := by
  obtain ⟨hi, j, haddr, _⟩ := he
  have hroot : s.rootOf (Finset.range N) y = s.rootOf (Finset.range N) x := by
    have hval := congrArg Fin.val hi
    change (componentRootIndex N hN s x).val = (componentRootIndex N hN s y).val at hval
    rw [componentRootIndex_val N hN s hs hx, componentRootIndex_val N hN s hs hy] at hval
    exact hval.symm
  have hchild := (s.address_child_iff hs hx hy hroot j).mp haddr
  obtain ⟨_, hyN, hp⟩ := Finset.mem_filter.mp hchild.1
  exact ⟨hy, hyN, hp⟩

noncomputable def genealogyPlaneInverseEmbedding (N : ℕ) (hN : 0 < N) (s : CouplingGenealogy)
    (hs : s.Valid (Finset.range N)) :
    RootedForest.Embedding (shapeForest (forestShape N s)) (finiteGenealogyForest N s) :=
  (genealogyPlaneEmbedding N hN s hs).reverse (genealogyPlaneMap_surjOn N hN s hs)
    (fun i ↦ hs.1 (Finset.mem_range.mpr i.isLt))
    (planeForest_edge_vertices _) (genealogyPlane_edge_reflects N hN s hs)

end HeightPaper.CountCoupling
