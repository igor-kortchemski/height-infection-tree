module

public import HeightPaper.Probability.CorrectedCouplingAddresses

/-!
# Exact plane-tree support of each finite component

Ordered addresses preserve every parent edge and contain the complete
initial interval of siblings. Thus the plane encoding has exactly the
original component's vertices, with no extra or missing branches.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

open scoped Classical

theorem CouplingGenealogy.address_prefix_label (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {x : ℕ} (hx : x ∈ s.carrier.vertices) {u : List ℕ}
    (hu : u <+: s.orderedAddress roots x) :
    ∃ y ∈ s.carrier.vertices, s.rootOf roots y = s.rootOf roots x ∧ s.orderedAddress roots y = u := by
  induction x using Nat.strong_induction_on generalizing u with
  | h x ih =>
      by_cases hr : x ∈ roots
      · have hxaddr := s.orderedAddress_root roots hr
        have hu0 : u = [] := List.prefix_nil.mp (hxaddr ▸ hu)
        exact ⟨x, hx, rfl, hxaddr.trans hu0.symm⟩
      · obtain ⟨hp, hlt⟩ := hs.2 x hx hr
        rw [s.orderedAddress_nonroot hs hx hr] at hu
        rcases List.prefix_concat_iff.mp hu with he | hpref
        · exact ⟨x, hx, rfl, (s.orderedAddress_nonroot hs hx hr).trans he.symm⟩
        · obtain ⟨y, hy, hyroot, hyaddr⟩ := ih (s.parent x) hlt hp hpref
          exact ⟨y, hy, hyroot.trans (s.rootOf_parent hs hx hr).symm, hyaddr⟩

theorem CouplingGenealogy.address_child_iff (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {v x : ℕ} (hv : v ∈ s.carrier.vertices) (hx : x ∈ s.carrier.vertices)
    (hroot : s.rootOf roots x = s.rootOf roots v) (j : ℕ) :
    s.orderedAddress roots x = s.orderedAddress roots v ++ [j] ↔
      x ∈ s.children roots v ∧ j = couplingLabelRank (s.children roots v) x + 1 := by
  constructor
  · intro he
    have hr : x ∉ roots := by
      intro hr
      rw [s.orderedAddress_root roots hr] at he
      have := congrArg List.length he
      simp only [List.length_nil, List.length_append, List.length_singleton] at this
      omega
    obtain ⟨hp, _⟩ := hs.2 x hx hr
    obtain ⟨haddr, hrank⟩ := List.append_singleton_inj.mp
      ((s.orderedAddress_nonroot hs hx hr).symm.trans he)
    have hpar : s.parent x = v := s.rootedAddress_injOn hs hp hv
      (Prod.ext ((s.rootOf_parent hs hx hr).symm.trans hroot) haddr)
    refine ⟨Finset.mem_filter.mpr ⟨hx, hr, hpar⟩, ?_⟩
    simpa only [hpar] using hrank.symm
  · rintro ⟨hc, hj⟩
    obtain ⟨_, hr, hp⟩ := Finset.mem_filter.mp hc
    rw [s.orderedAddress_nonroot hs hx hr, hp, hj]

theorem CouplingGenealogy.child_mem_component (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) (v : ℕ) {x : ℕ} (hx : x ∈ s.children roots v) :
    x ∈ s.component roots (s.rootOf roots v) := by
  obtain ⟨hxV, hr, hp⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxV, (s.rootOf_parent hs hxV hr).trans (congrArg (s.rootOf roots) hp)⟩

theorem CouplingGenealogy.planeComponent_children (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {v : ℕ} (hv : v ∈ s.carrier.vertices) :
    PlaneForward.children (s.planeComponent roots (s.rootOf roots v)) (s.orderedAddress roots v) =
      (s.children roots v).image (s.orderedAddress roots) := by
  ext u
  constructor
  · intro hu
    obtain ⟨huV, j, huj⟩ := Finset.mem_filter.mp hu
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp huV
    obtain ⟨hxV, hxroot⟩ := Finset.mem_filter.mp hx
    have hchild := (s.address_child_iff hs hv hxV hxroot j).mp (hxu.trans huj)
    exact Finset.mem_image.mpr ⟨x, hchild.1, hxu⟩
  · intro hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    have hcomp := s.child_mem_component hs v hx
    obtain ⟨hxV, hxroot⟩ := Finset.mem_filter.mp hcomp
    have haddr := (s.address_child_iff hs hv hxV hxroot
      (couplingLabelRank (s.children roots v) x + 1)).mpr ⟨hx, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hcomp, rfl⟩, _, haddr⟩

theorem CouplingGenealogy.planeComponent_childCount (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {v : ℕ} (hv : v ∈ s.carrier.vertices) :
    PlaneForward.childCount (s.planeComponent roots (s.rootOf roots v)) (s.orderedAddress roots v) =
      (s.children roots v).card := by
  change (PlaneForward.children _ _).card = _
  rw [s.planeComponent_children hs hv]
  apply Finset.card_image_of_injOn
  exact (s.planeComponent_address_injOn hs (s.rootOf roots v)).mono
    (fun _ hx ↦ s.child_mem_component hs v hx)

theorem CouplingGenealogy.planeComponent_valid (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {root : ℕ} (hr : root ∈ roots) : PlaneForward.Valid (s.planeComponent roots root) := by
  constructor
  · have hroot : s.rootOf roots root = root := by simp [CouplingGenealogy.rootOf, hr]
    exact Finset.mem_image.mpr ⟨root, Finset.mem_filter.mpr ⟨hs.1 hr, hroot⟩,
      s.orderedAddress_root roots hr⟩
  · exact s.planeComponent_active_subset roots root
  · intro u v huv
    obtain ⟨x, hx, haddr⟩ := Finset.mem_image.mp huv
    obtain ⟨hxV, hxroot⟩ := Finset.mem_filter.mp hx
    obtain ⟨y, hy, hyroot, hyaddr⟩ := s.address_prefix_label hs hxV ⟨v, haddr.symm⟩
    exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hyroot.trans hxroot⟩, hyaddr⟩
  · intro u hu j
    obtain ⟨v, hv, hvaddr⟩ := Finset.mem_image.mp hu
    obtain ⟨hvV, hvroot⟩ := Finset.mem_filter.mp hv
    have hc := s.planeComponent_childCount hs hvV
    rw [hvroot, hvaddr] at hc
    rw [hc]
    constructor
    · intro huj
      obtain ⟨x, hx, hxaddr⟩ := Finset.mem_image.mp huj
      obtain ⟨hxV, hxroot⟩ := Finset.mem_filter.mp hx
      have hchild := (s.address_child_iff hs hvV hxV (hxroot.trans hvroot.symm) j).mp
        (by rw [hvaddr]; exact hxaddr)
      rw [hchild.2]
      exact ⟨by omega, Nat.succ_le_of_lt (couplingLabelRank_lt_card _ hchild.1)⟩
    · rintro ⟨hj0, hjcard⟩
      have himg : j - 1 ∈ (s.children roots v).image (couplingLabelRank (s.children roots v)) := by
        rw [couplingLabelRank_image]
        exact Finset.mem_range.mpr (by omega)
      obtain ⟨x, hx, hrank⟩ := Finset.mem_image.mp himg
      have hcomp := s.child_mem_component hs v hx
      obtain ⟨hxV, hxroot⟩ := Finset.mem_filter.mp hcomp
      have haddr := (s.address_child_iff hs hvV hxV hxroot j).mpr ⟨hx, by omega⟩
      rw [hvaddr] at haddr
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxV, hxroot.trans hvroot⟩, haddr⟩

end HeightPaper.CountCoupling
