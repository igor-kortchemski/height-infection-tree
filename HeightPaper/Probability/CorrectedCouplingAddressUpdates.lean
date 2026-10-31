module

public import HeightPaper.Probability.CorrectedCouplingPlaneValidity

/-!
# Stability of ordered addresses under fresh births

Old vertices retain their addresses. A new vertex receives the next sibling
index at its parent's address, exactly as in the finite plane process.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

open scoped Classical

theorem CouplingGenealogy.children_birth (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {v fresh : ℕ} (hv : v ∈ s.carrier.active)
    (hf : fresh ∉ s.carrier.vertices) (u : ℕ) :
    (s.update v fresh true).children roots u =
      if u = v then insert fresh (s.children roots u) else s.children roots u := by
  have hfr : fresh ∉ roots := fun hr ↦ hf (hs.1 hr)
  ext x
  by_cases hxf : x = fresh
  · subst x
    by_cases huv : u = v <;>
      simp [CouplingGenealogy.children, CouplingGenealogy.update, CouplingCarrier.update,
        hv, hfr, hf, huv, eq_comm]
  · by_cases huv : u = v <;>
      simp [CouplingGenealogy.children, CouplingGenealogy.update, CouplingCarrier.update,
        hv, hxf, huv]

theorem CouplingGenealogy.orderedAddress_birth_old (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {v fresh : ℕ} (hv : v ∈ s.carrier.active)
    (hgt : ∀ x ∈ s.carrier.vertices, x < fresh)
    {x : ℕ} (hx : x ∈ s.carrier.vertices) :
    (s.update v fresh true).orderedAddress roots x = s.orderedAddress roots x := by
  have hf : fresh ∉ s.carrier.vertices := fun hm ↦ (Nat.lt_irrefl _) (hgt fresh hm)
  have hvalid := s.valid_update hs v fresh hgt true
  have hV : s.carrier.vertices ⊆ (s.update v fresh true).carrier.vertices := by
    simp only [CouplingGenealogy.update, CouplingCarrier.update, hv, ↓reduceIte]
    exact Finset.subset_insert _ _
  induction x using Nat.strong_induction_on with
  | h x ih =>
      by_cases hr : x ∈ roots
      · rw [(s.update v fresh true).orderedAddress_root roots hr, s.orderedAddress_root roots hr]
      · obtain ⟨hp, hlt⟩ := hs.2 x hx hr
        have hxf : x ≠ fresh := fun he ↦ hf (he ▸ hx)
        have hparent : (s.update v fresh true).parent x = s.parent x := by
          simp [CouplingGenealogy.update, hv, Function.update_of_ne hxf]
        rw [(s.update v fresh true).orderedAddress_nonroot hvalid (hV hx) hr,
          s.orderedAddress_nonroot hs hx hr, hparent, ih (s.parent x) hlt hp,
          s.children_birth hs hv hf (s.parent x)]
        by_cases hpu : s.parent x = v
        · rw [ite_eq_left hpu]
          have hxc : x ∈ s.children roots (s.parent x) := Finset.mem_filter.mpr ⟨hx, hr, rfl⟩
          rw [couplingLabelRank_insert_old (s.children roots (s.parent x))
            (fun y hy ↦ hgt y (Finset.mem_filter.mp hy).1) hxc]
        · rw [ite_eq_right hpu]

theorem CouplingGenealogy.orderedAddress_birth_new (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) {v fresh : ℕ} (hv : v ∈ s.carrier.active)
    (hgt : ∀ x ∈ s.carrier.vertices, x < fresh) :
    (s.update v fresh true).orderedAddress roots fresh =
      s.orderedAddress roots v ++ [(s.children roots v).card + 1] := by
  have hf : fresh ∉ s.carrier.vertices := fun hm ↦ (Nat.lt_irrefl _) (hgt fresh hm)
  have hfr : fresh ∉ roots := fun hr ↦ hf (hs.1 hr)
  have hfV : fresh ∈ (s.update v fresh true).carrier.vertices := by
    simp [CouplingGenealogy.update, CouplingCarrier.update, hv]
  have hvalid := s.valid_update hs v fresh hgt true
  have hparent : (s.update v fresh true).parent fresh = v := by
    simp [CouplingGenealogy.update, hv]
  rw [(s.update v fresh true).orderedAddress_nonroot hvalid hfV hfr, hparent,
    s.orderedAddress_birth_old hs hv hgt (s.carrier.active_sub_vertices hv),
    s.children_birth hs hv hf v, ite_eq_left rfl,
    couplingLabelRank_insert_new (s.children roots v) (fun y hy ↦ hgt y (Finset.mem_filter.mp hy).1)]

theorem CouplingGenealogy.orderedAddress_freeze (s : CouplingGenealogy) {roots : Finset ℕ}
    (hs : s.Valid roots) (v fresh : ℕ) {x : ℕ} (hx : x ∈ s.carrier.vertices) :
    (s.update v fresh false).orderedAddress roots x = s.orderedAddress roots x := by
  have hV : s.carrier.vertices = (s.update v fresh false).carrier.vertices := by
    by_cases hv : v ∈ s.carrier.active <;> simp [CouplingGenealogy.update, CouplingCarrier.update, hv]
  exact (s.orderedAddress_eq_of_vertices_parent (s.update v fresh false) hs hV
    (fun _ _ ↦ by simp [CouplingGenealogy.update]) hx).symm

end HeightPaper.CountCoupling
