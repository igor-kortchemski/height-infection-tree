module

public import HeightPaper.Probability.CorrectedCouplingRanks
public import HeightPaper.Probability.CorrectedCouplingComponents
public import HeightPaper.Combinatorics.PlaneStateUpdates

/-!
# Ordered component addresses for finite coupled genealogies

Children are ordered by their birth labels. Root parent pointers are excluded
from the child sets: they are totalization values, not genealogy edges.
The resulting rooted addresses are injective on every valid finite forest.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

def CouplingGenealogy.children (s : CouplingGenealogy) (roots : Finset ℕ) (v : ℕ) : Finset ℕ :=
  s.carrier.vertices.filter (fun x ↦ x ∉ roots ∧ s.parent x = v)

def CouplingGenealogy.orderedAddress (s : CouplingGenealogy) (roots : Finset ℕ) (x : ℕ) : List ℕ :=
  if x ∈ roots then []
  else if _h : s.parent x < x then
    s.orderedAddress roots (s.parent x) ++ [couplingLabelRank (s.children roots (s.parent x)) x + 1]
  else []
termination_by x

def CouplingGenealogy.rootedAddress (s : CouplingGenealogy) (roots : Finset ℕ) (x : ℕ) : ℕ × List ℕ :=
  (s.rootOf roots x, s.orderedAddress roots x)

theorem CouplingGenealogy.rootOf_mem_roots (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {x : ℕ} (hx : x ∈ s.carrier.vertices) : s.rootOf roots x ∈ roots := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
      by_cases hr : x ∈ roots
      · simp [CouplingGenealogy.rootOf, hr]
      · obtain ⟨hp, hlt⟩ := hs.2 x hx hr
        rw [CouplingGenealogy.rootOf]
        simp only [hr, ↓reduceIte, dite_eq_left hlt]
        exact ih (s.parent x) hlt hp

theorem CouplingGenealogy.orderedAddress_root (s : CouplingGenealogy) (roots : Finset ℕ)
    {x : ℕ} (hx : x ∈ roots) : s.orderedAddress roots x = [] := by
  rw [CouplingGenealogy.orderedAddress, ite_eq_left hx]

theorem CouplingGenealogy.orderedAddress_nonroot (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {x : ℕ} (hx : x ∈ s.carrier.vertices) (hr : x ∉ roots) :
    s.orderedAddress roots x = s.orderedAddress roots (s.parent x) ++
      [couplingLabelRank (s.children roots (s.parent x)) x + 1] := by
  rw [CouplingGenealogy.orderedAddress, ite_eq_right hr, dite_eq_left (hs.2 x hx hr).2]

theorem CouplingGenealogy.rootOf_parent (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {x : ℕ} (hx : x ∈ s.carrier.vertices) (hr : x ∉ roots) :
    s.rootOf roots x = s.rootOf roots (s.parent x) := by
  rw [CouplingGenealogy.rootOf, ite_eq_right hr, dite_eq_left (hs.2 x hx hr).2]

theorem CouplingGenealogy.rootedAddress_injOn (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) : Set.InjOn (s.rootedAddress roots) s.carrier.vertices := by
  intro x hx
  induction x using Nat.strong_induction_on with
  | h x ih =>
      intro y hy he
      have hroot := congrArg Prod.fst he
      have haddr := congrArg Prod.snd he
      change s.rootOf roots x = s.rootOf roots y at hroot
      change s.orderedAddress roots x = s.orderedAddress roots y at haddr
      by_cases hxr : x ∈ roots
      · by_cases hyr : y ∈ roots
        · simpa [CouplingGenealogy.rootOf, hxr, hyr] using hroot
        · rw [s.orderedAddress_root roots hxr, s.orderedAddress_nonroot hs hy hyr] at haddr
          have hl := congrArg List.length haddr
          simp only [List.length_nil, List.length_append, List.length_singleton] at hl
          omega
      · by_cases hyr : y ∈ roots
        · rw [s.orderedAddress_nonroot hs hx hxr, s.orderedAddress_root roots hyr] at haddr
          have hl := congrArg List.length haddr
          simp only [List.length_nil, List.length_append, List.length_singleton] at hl
          omega
        · obtain ⟨hpx, hltx⟩ := hs.2 x hx hxr
          obtain ⟨hpy, _⟩ := hs.2 y hy hyr
          rw [s.orderedAddress_nonroot hs hx hxr, s.orderedAddress_nonroot hs hy hyr] at haddr
          obtain ⟨hparents, hranks⟩ := List.append_singleton_inj.mp haddr
          rw [s.rootOf_parent hs hx hxr, s.rootOf_parent hs hy hyr] at hroot
          have hp : s.parent x = s.parent y :=
            ih (s.parent x) hltx hpx hpy (Prod.ext hroot hparents)
          have hxc : x ∈ s.children roots (s.parent x) := Finset.mem_filter.mpr ⟨hx, hxr, rfl⟩
          have hyc : y ∈ s.children roots (s.parent x) := Finset.mem_filter.mpr ⟨hy, hyr, hp.symm⟩
          rw [← hp] at hranks
          exact couplingLabelRank_injOn _ hxc hyc (Nat.add_right_cancel hranks)

theorem CouplingGenealogy.children_eq_of_vertices_parent
    (s t : CouplingGenealogy) (roots : Finset ℕ)
    (hV : s.carrier.vertices = t.carrier.vertices)
    (hP : ∀ x ∈ s.carrier.vertices, s.parent x = t.parent x) (v : ℕ) :
    s.children roots v = t.children roots v := by
  ext x
  simp only [CouplingGenealogy.children, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hr, hp⟩
    exact ⟨hV ▸ hx, hr, (hP x hx).symm.trans hp⟩
  · rintro ⟨hx, hr, hp⟩
    have hx' : x ∈ s.carrier.vertices := hV.symm ▸ hx
    exact ⟨hx', hr, (hP x hx').trans hp⟩

theorem CouplingGenealogy.orderedAddress_eq_of_vertices_parent
    (s t : CouplingGenealogy) {roots : Finset ℕ} (hs : s.Valid roots)
    (hV : s.carrier.vertices = t.carrier.vertices)
    (hP : ∀ x ∈ s.carrier.vertices, s.parent x = t.parent x)
    {x : ℕ} (hx : x ∈ s.carrier.vertices) : s.orderedAddress roots x = t.orderedAddress roots x := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
      by_cases hr : x ∈ roots
      · rw [s.orderedAddress_root roots hr, t.orderedAddress_root roots hr]
      · obtain ⟨hp, hlt⟩ := hs.2 x hx hr
        rw [s.orderedAddress_nonroot hs hx hr]
        conv_rhs => rw [CouplingGenealogy.orderedAddress]
        simp only [hr, ↓reduceIte, ← hP x hx, dite_eq_left hlt]
        rw [ih (s.parent x) hlt hp,
          s.children_eq_of_vertices_parent t roots hV hP (s.parent x)]

noncomputable def CouplingGenealogy.planeComponent (s : CouplingGenealogy)
    (roots : Finset ℕ) (root : ℕ) : PlaneForward.State :=
  { vertices := (s.component roots root).image (s.orderedAddress roots)
    active := (s.carrier.active.filter (fun x ↦ s.rootOf roots x = root)).image
      (s.orderedAddress roots) }

theorem CouplingGenealogy.planeComponent_active_subset (s : CouplingGenealogy)
    (roots : Finset ℕ) (root : ℕ) :
    (s.planeComponent roots root).active ⊆ (s.planeComponent roots root).vertices := by
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr
    ⟨s.carrier.active_sub_vertices (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩, rfl⟩

theorem CouplingGenealogy.planeComponent_address_injOn (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) (root : ℕ) :
    Set.InjOn (s.orderedAddress roots) (s.component roots root) := by
  intro x hx y hy he
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  exact s.rootedAddress_injOn hs hx'.1 hy'.1 (Prod.ext (hx'.2.trans hy'.2.symm) he)

theorem CouplingGenealogy.planeComponent_card (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) (root : ℕ) :
    (s.planeComponent roots root).vertices.card = (s.component roots root).card :=
  Finset.card_image_of_injOn (s.planeComponent_address_injOn hs root)

end HeightPaper.CountCoupling
