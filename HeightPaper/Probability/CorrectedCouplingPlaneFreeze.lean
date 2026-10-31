module

public import HeightPaper.Probability.CorrectedCouplingPlaneUpdates

/-!
# Recovery and skipped proposals in component coordinates
-/

@[expose] public section

namespace HeightPaper.CountCoupling

open scoped Classical

theorem finset_image_erase_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) (hf : Set.InjOn f A) {v : α} (hv : v ∈ A) :
    (A.erase v).image f = (A.image f).erase (f v) := by
  ext b
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨x, ⟨hxv, hx⟩, rfl⟩
    exact ⟨fun he ↦ hxv (hf hx hv he), ⟨x, hx, rfl⟩⟩
  · rintro ⟨hbv, x, hx, he⟩
    refine ⟨x, ⟨?_, hx⟩, he⟩
    intro hxv
    subst x
    exact hbv he.symm

theorem CouplingGenealogy.update_eq_of_not_active (s : CouplingGenealogy)
    {v fresh : ℕ} (hv : v ∉ s.carrier.active) (b : Bool) : s.update v fresh b = s := by
  simp [CouplingGenealogy.update, CouplingCarrier.update, hv]

theorem CouplingGenealogy.component_freeze (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) (v fresh : ℕ) (hf : fresh ∉ s.carrier.vertices) (root : ℕ) :
    (s.update v fresh false).component roots root = s.component roots root := by
  have hV : (s.update v fresh false).carrier.vertices = s.carrier.vertices := by
    by_cases hv : v ∈ s.carrier.active <;> simp [CouplingGenealogy.update, CouplingCarrier.update, hv]
  ext x
  by_cases hx : x ∈ s.carrier.vertices
  · have hr := (CouplingGenealogy.rootOf_eq_of_treeLE (s.treeLE_update v fresh hf false) hs hx).symm
    simp [CouplingGenealogy.component, hV, hx, hr]
  · simp [CouplingGenealogy.component, hV, hx]

theorem CouplingGenealogy.activeComponent_freeze (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {v fresh : ℕ} (hv : v ∈ s.carrier.active)
    (hf : fresh ∉ s.carrier.vertices) (root : ℕ) :
    ((s.update v fresh false).carrier.active.filter (fun x ↦ (s.update v fresh false).rootOf roots x = root)) =
      (s.carrier.active.filter (fun x ↦ s.rootOf roots x = root)).erase v := by
  have hA : (s.update v fresh false).carrier.active = s.carrier.active.erase v := by
    simp [CouplingGenealogy.update, CouplingCarrier.update, hv]
  ext x
  simp only [hA, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hxv, hx⟩, hr⟩
    have hold := CouplingGenealogy.rootOf_eq_of_treeLE (s.treeLE_update v fresh hf false) hs
      (s.carrier.active_sub_vertices hx)
    exact ⟨hxv, hx, hold.trans hr⟩
  · rintro ⟨hxv, hx, hr⟩
    have hold := CouplingGenealogy.rootOf_eq_of_treeLE (s.treeLE_update v fresh hf false) hs
      (s.carrier.active_sub_vertices hx)
    exact ⟨⟨hxv, hx⟩, hold.symm.trans hr⟩

theorem CouplingGenealogy.planeComponent_freeze (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {v fresh : ℕ} (hv : v ∈ s.carrier.active)
    (hf : fresh ∉ s.carrier.vertices) (root : ℕ) :
    (s.update v fresh false).planeComponent roots root =
      if s.rootOf roots v = root then
        PlaneForward.freeze (s.planeComponent roots root) (s.orderedAddress roots v)
      else s.planeComponent roots root := by
  have hVimage : (s.component roots root).image ((s.update v fresh false).orderedAddress roots) =
      (s.component roots root).image (s.orderedAddress roots) := by
    apply Finset.image_congr
    intro x hx
    exact s.orderedAddress_freeze hs v fresh (Finset.mem_filter.mp hx).1
  let A := s.carrier.active.filter (fun x ↦ s.rootOf roots x = root)
  have hAimage : (A.erase v).image ((s.update v fresh false).orderedAddress roots) =
      (A.erase v).image (s.orderedAddress roots) := by
    apply Finset.image_congr
    intro x hx
    exact s.orderedAddress_freeze hs v fresh
      (s.carrier.active_sub_vertices (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).1)
  have hvertices : ((s.update v fresh false).planeComponent roots root).vertices =
      (s.planeComponent roots root).vertices := by
    change ((s.update v fresh false).component roots root).image _ = _
    rw [s.component_freeze hs v fresh hf root]
    exact hVimage
  have hactive : ((s.update v fresh false).planeComponent roots root).active =
      (A.erase v).image (s.orderedAddress roots) := by
    change ((s.update v fresh false).carrier.active.filter _).image _ = _
    rw [s.activeComponent_freeze hs hv hf root]
    exact hAimage
  by_cases hr : s.rootOf roots v = root
  · rw [ite_eq_left hr]
    apply PlaneForward.State.ext_vertices_active
    · exact hvertices
    · change ((s.update v fresh false).planeComponent roots root).active =
        ((s.planeComponent roots root).active.erase (s.orderedAddress roots v))
      rw [hactive]
      have hvA : v ∈ A := Finset.mem_filter.mpr ⟨hv, hr⟩
      apply finset_image_erase_of_injOn A (s.orderedAddress roots) _ hvA
      exact (s.planeComponent_address_injOn hs root).mono (fun x hx ↦
        Finset.mem_filter.mpr ⟨s.carrier.active_sub_vertices (Finset.mem_filter.mp hx).1,
          (Finset.mem_filter.mp hx).2⟩)
  · rw [ite_eq_right hr]
    apply PlaneForward.State.ext_vertices_active hvertices
    rw [hactive, Finset.erase_eq_of_notMem (show v ∉ A from fun hm ↦ hr (Finset.mem_filter.mp hm).2)]
    rfl

theorem CouplingGenealogy.planeComponent_update (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) (v fresh : ℕ) (hgt : ∀ x ∈ s.carrier.vertices, x < fresh)
    (b : Bool) (root : ℕ) :
    (s.update v fresh b).planeComponent roots root =
      if v ∈ s.carrier.active ∧ s.rootOf roots v = root then
        PlaneForward.step (s.planeComponent roots root) b (s.orderedAddress roots v)
      else s.planeComponent roots root := by
  by_cases hv : v ∈ s.carrier.active
  · have hmember (hr : s.rootOf roots v = root) :
        s.orderedAddress roots v ∈ (s.planeComponent roots root).active :=
      Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hr⟩, rfl⟩
    have hf : fresh ∉ s.carrier.vertices := fun hm ↦ (Nat.lt_irrefl _) (hgt fresh hm)
    cases b
    · rw [s.planeComponent_freeze hs hv hf root]
      by_cases hr : s.rootOf roots v = root <;> simp [hv, hr, PlaneForward.step, hmember]
    · rw [s.planeComponent_birth hs hv hgt root]
      by_cases hr : s.rootOf roots v = root <;> simp [hv, hr, PlaneForward.step, hmember]
  · rw [s.update_eq_of_not_active hv]
    simp only [hv, false_and, ↓reduceIte]

end HeightPaper.CountCoupling
