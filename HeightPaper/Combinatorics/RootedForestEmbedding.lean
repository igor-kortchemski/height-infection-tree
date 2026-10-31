module

public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Relation

/-!
# Root-preserving embeddings of countable forests

The carriers may differ. Vertex injectivity and preservation of the actual
parent edges are explicit, and each indexed initial root is fixed.
-/

@[expose] public section

namespace HeightPaper

structure RootedForest (α : Type*) (N : ℕ) where
  vertices : Set α
  edge : α → α → Prop
  root : Fin N → α

namespace RootedForest

variable {α β γ : Type*} {N : ℕ}

def component (A : RootedForest α N) (i : Fin N) : Set α :=
  {x | x ∈ A.vertices ∧ Relation.ReflTransGen A.edge (A.root i) x}

structure Embedding (A : RootedForest α N) (B : RootedForest β N) where
  map : α → β
  mapsTo : Set.MapsTo map A.vertices B.vertices
  injOn : Set.InjOn map A.vertices
  map_root : ∀ i, map (A.root i) = B.root i
  map_edge : ∀ x y, A.edge x y → B.edge (map x) (map y)

def Embedding.refl (A : RootedForest α N) : Embedding A A :=
  ⟨id, fun _ hx ↦ hx, fun _ _ _ _ he ↦ he, fun _ ↦ rfl, fun _ _ he ↦ he⟩

def Embedding.trans {A : RootedForest α N} {B : RootedForest β N} {C : RootedForest γ N}
    (e : Embedding A B) (f : Embedding B C) : Embedding A C where
  map := f.map ∘ e.map
  mapsTo := fun _ hx ↦ f.mapsTo (e.mapsTo hx)
  injOn := fun _ hx _ hy he ↦ e.injOn hx hy (f.injOn (e.mapsTo hx) (e.mapsTo hy) he)
  map_root := fun i ↦ by simp only [Function.comp_def, e.map_root, f.map_root]
  map_edge := fun x y h ↦ f.map_edge _ _ (e.map_edge x y h)

theorem Embedding.mapsTo_component {A : RootedForest α N} {B : RootedForest β N}
    (e : Embedding A B) (i : Fin N) : Set.MapsTo e.map (A.component i) (B.component i) := by
  rintro x ⟨hx, hpath⟩
  refine ⟨e.mapsTo hx, ?_⟩
  have hp : Relation.ReflTransGen B.edge (e.map (A.root i)) (e.map x) := by
    clear hx
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | tail hxy hyz ih => exact ih.tail (e.map_edge _ _ hyz)
  rwa [e.map_root] at hp

noncomputable def Embedding.reverse [Nonempty α]
    {A : RootedForest α N} {B : RootedForest β N} (e : Embedding A B)
    (hsurj : Set.SurjOn e.map A.vertices B.vertices)
    (hroots : ∀ i, A.root i ∈ A.vertices)
    (hedges : ∀ x y, B.edge x y → x ∈ B.vertices ∧ y ∈ B.vertices)
    (hreflect : ∀ x ∈ A.vertices, ∀ y ∈ A.vertices,
      B.edge (e.map x) (e.map y) → A.edge x y) : Embedding B A where
  map := Function.invFunOn e.map A.vertices
  mapsTo := hsurj.mapsTo_invFunOn
  injOn := (Function.invFunOn_injOn_image e.map A.vertices).mono
    (fun _ hy ↦ hsurj hy)
  map_root := fun i ↦ by
    rw [← e.map_root i]
    exact e.injOn.leftInvOn_invFunOn (hroots i)
  map_edge := fun x y h ↦ by
    have hx := (hedges x y h).1
    have hy := (hedges x y h).2
    apply hreflect _ (hsurj.mapsTo_invFunOn hx) _ (hsurj.mapsTo_invFunOn hy)
    rw [hsurj.rightInvOn_invFunOn hx, hsurj.rightInvOn_invFunOn hy]
    exact h

def Embedding.of_inclusion {A B : RootedForest α N}
    (hV : A.vertices ⊆ B.vertices) (hE : ∀ x y, A.edge x y → B.edge x y)
    (hR : A.root = B.root) : Embedding A B where
  map := id
  mapsTo := hV
  injOn := fun _ _ _ _ he ↦ he
  map_root := congrFun hR
  map_edge := hE

end RootedForest
end HeightPaper
