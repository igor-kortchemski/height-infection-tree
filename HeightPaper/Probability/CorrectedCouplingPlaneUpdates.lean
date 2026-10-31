module

public import HeightPaper.Probability.CorrectedCouplingAddressUpdates

/-!
# Component projections commute with the genealogy updates
-/

@[expose] public section

namespace HeightPaper.PlaneForward

theorem State.ext_vertices_active {s t : State}
    (hV : s.vertices = t.vertices) (hA : s.active = t.active) : s = t := by
  cases s
  cases t
  cases hV
  cases hA
  rfl

end HeightPaper.PlaneForward

namespace HeightPaper.CountCoupling

open scoped Classical

theorem CouplingGenealogy.rootOf_eq_of_treeLE {s t : CouplingGenealogy} {roots : Finset ℕ}
    (h : s.TreeLE t) (hs : s.Valid roots) {x : ℕ} (hx : x ∈ s.carrier.vertices) :
    s.rootOf roots x = t.rootOf roots x := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
      by_cases hr : x ∈ roots
      · simp [CouplingGenealogy.rootOf, hr]
      · obtain ⟨hp, hlt⟩ := hs.2 x hx hr
        conv_lhs => rw [CouplingGenealogy.rootOf]
        conv_rhs => rw [CouplingGenealogy.rootOf]
        simp only [hr, ↓reduceIte, ← h.2 x hx, dite_eq_left hlt]
        exact ih (s.parent x) hlt hp

theorem CouplingGenealogy.rootOf_birth_new (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {v fresh : ℕ} (hv : v ∈ s.carrier.active)
    (hgt : ∀ x ∈ s.carrier.vertices, x < fresh) :
    (s.update v fresh true).rootOf roots fresh = s.rootOf roots v := by
  have hf : fresh ∉ s.carrier.vertices := fun hm ↦ (Nat.lt_irrefl _) (hgt fresh hm)
  have hfr : fresh ∉ roots := fun hr ↦ hf (hs.1 hr)
  have hfV : fresh ∈ (s.update v fresh true).carrier.vertices := by
    simp [CouplingGenealogy.update, CouplingCarrier.update, hv]
  have hparent : (s.update v fresh true).parent fresh = v := by simp [CouplingGenealogy.update, hv]
  rw [(s.update v fresh true).rootOf_parent (s.valid_update hs v fresh hgt true) hfV hfr, hparent]
  exact (CouplingGenealogy.rootOf_eq_of_treeLE (s.treeLE_update v fresh hf true) hs
    (s.carrier.active_sub_vertices hv)).symm

theorem CouplingGenealogy.component_birth (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {v fresh : ℕ} (hv : v ∈ s.carrier.active)
    (hgt : ∀ x ∈ s.carrier.vertices, x < fresh) (root : ℕ) :
    (s.update v fresh true).component roots root =
      if s.rootOf roots v = root then insert fresh (s.component roots root) else s.component roots root := by
  have hf : fresh ∉ s.carrier.vertices := fun hm ↦ (Nat.lt_irrefl _) (hgt fresh hm)
  have hnew := s.rootOf_birth_new hs hv hgt
  have hvertices : (s.update v fresh true).carrier.vertices = insert fresh s.carrier.vertices := by
    simp [CouplingGenealogy.update, CouplingCarrier.update, hv]
  ext x
  by_cases hxf : x = fresh
  · subst x
    by_cases hr : s.rootOf roots v = root <;>
      simp [CouplingGenealogy.component, hvertices, hf, hnew, hr]
  · have hold (hx : x ∈ s.carrier.vertices) : (s.update v fresh true).rootOf roots x = s.rootOf roots x :=
      (CouplingGenealogy.rootOf_eq_of_treeLE (s.treeLE_update v fresh hf true) hs hx).symm
    by_cases hx : x ∈ s.carrier.vertices
    · by_cases hr : s.rootOf roots v = root <;>
        simp [CouplingGenealogy.component, hvertices, hxf, hx, hold hx, hr]
    · by_cases hr : s.rootOf roots v = root <;>
        simp [CouplingGenealogy.component, hvertices, hxf, hx, hr]

theorem CouplingGenealogy.activeComponent_birth (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {v fresh : ℕ} (hv : v ∈ s.carrier.active)
    (hgt : ∀ x ∈ s.carrier.vertices, x < fresh) (root : ℕ) :
    ((s.update v fresh true).carrier.active.filter (fun x ↦ (s.update v fresh true).rootOf roots x = root)) =
      if s.rootOf roots v = root then insert fresh
        (s.carrier.active.filter (fun x ↦ s.rootOf roots x = root))
      else s.carrier.active.filter (fun x ↦ s.rootOf roots x = root) := by
  have hf : fresh ∉ s.carrier.vertices := fun hm ↦ (Nat.lt_irrefl _) (hgt fresh hm)
  have hnew := s.rootOf_birth_new hs hv hgt
  have hactive : (s.update v fresh true).carrier.active = insert fresh s.carrier.active := by
    simp [CouplingGenealogy.update, CouplingCarrier.update, hv]
  ext x
  by_cases hxf : x = fresh
  · subst x
    have hfA : fresh ∉ s.carrier.active := fun h ↦ hf (s.carrier.active_sub_vertices h)
    by_cases hr : s.rootOf roots v = root <;>
      simp [hactive, hfA, hnew, hr]
  · by_cases hx : x ∈ s.carrier.active
    · have hold := (CouplingGenealogy.rootOf_eq_of_treeLE (s.treeLE_update v fresh hf true) hs
        (s.carrier.active_sub_vertices hx)).symm
      by_cases hr : s.rootOf roots v = root <;>
        simp [hactive, hxf, hx, hold, hr]
    · by_cases hr : s.rootOf roots v = root <;>
        simp [hactive, hxf, hx, hr]

theorem CouplingGenealogy.planeComponent_birth (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {v fresh : ℕ} (hv : v ∈ s.carrier.active)
    (hgt : ∀ x ∈ s.carrier.vertices, x < fresh) (root : ℕ) :
    (s.update v fresh true).planeComponent roots root =
      if s.rootOf roots v = root then
        PlaneForward.attach (s.planeComponent roots root) (s.orderedAddress roots v)
      else s.planeComponent roots root := by
  have hVimage : (s.component roots root).image ((s.update v fresh true).orderedAddress roots) =
      (s.component roots root).image (s.orderedAddress roots) := by
    apply Finset.image_congr
    intro x hx
    exact s.orderedAddress_birth_old hs hv hgt (Finset.mem_filter.mp hx).1
  have hAimage : (s.carrier.active.filter (fun x ↦ s.rootOf roots x = root)).image
      ((s.update v fresh true).orderedAddress roots) =
      (s.carrier.active.filter (fun x ↦ s.rootOf roots x = root)).image (s.orderedAddress roots) := by
    apply Finset.image_congr
    intro x hx
    exact s.orderedAddress_birth_old hs hv hgt (s.carrier.active_sub_vertices (Finset.mem_filter.mp hx).1)
  by_cases hr : s.rootOf roots v = root
  · rw [ite_eq_left hr]
    have hnew : (s.update v fresh true).orderedAddress roots fresh =
        PlaneForward.newChild (s.planeComponent roots root) (s.orderedAddress roots v) := by
      rw [s.orderedAddress_birth_new hs hv hgt]
      unfold PlaneForward.newChild
      rw [← hr, s.planeComponent_childCount hs (s.carrier.active_sub_vertices hv)]
    apply PlaneForward.State.ext_vertices_active
    · change ((s.update v fresh true).component roots root).image _ = _
      rw [s.component_birth hs hv hgt root, ite_eq_left hr, Finset.image_insert, hVimage, hnew]
      rfl
    · change ((s.update v fresh true).carrier.active.filter _).image _ = _
      rw [s.activeComponent_birth hs hv hgt root, ite_eq_left hr, Finset.image_insert, hAimage, hnew]
      rfl
  · rw [ite_eq_right hr]
    apply PlaneForward.State.ext_vertices_active
    · change ((s.update v fresh true).component roots root).image _ = _
      rw [s.component_birth hs hv hgt root, ite_eq_right hr]
      exact hVimage
    · change ((s.update v fresh true).carrier.active.filter _).image _ = _
      rw [s.activeComponent_birth hs hv hgt root, ite_eq_right hr]
      exact hAimage

end HeightPaper.CountCoupling
