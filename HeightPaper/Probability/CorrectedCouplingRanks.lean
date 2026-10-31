module

public import HeightPaper.Probability.CorrectedCouplingFiniteState
public import HeightPaper.Probability.CorrectedCouplingStageStructure

/-!
# Chronological ranks of finite genealogy labels

Global coupling labels can have gaps. Increasing ranks remove these gaps while
preserving roots, parents and the order of later births.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

def couplingLabelRank (V : Finset ℕ) (x : ℕ) : ℕ :=
  (V.filter (fun y ↦ y < x)).card

theorem couplingLabelRank_lt_card (V : Finset ℕ) {x : ℕ} (hx : x ∈ V) :
    couplingLabelRank V x < V.card := by
  apply Finset.card_lt_card
  exact Finset.filter_ssubset.mpr ⟨x, hx, by simp⟩

theorem couplingLabelRank_strictMono (V : Finset ℕ) {x y : ℕ}
    (hx : x ∈ V) (_hy : y ∈ V) (hxy : x < y) :
    couplingLabelRank V x < couplingLabelRank V y := by
  have hs : V.filter (fun z ↦ z < x) ⊆ V.filter (fun z ↦ z < y) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
      ((Finset.mem_filter.mp hz).2).trans hxy⟩
  apply Finset.card_lt_card
  exact (Finset.ssubset_iff_of_subset hs).mpr
    ⟨x, Finset.mem_filter.mpr ⟨hx, hxy⟩, by simp⟩

theorem couplingLabelRank_injOn (V : Finset ℕ) : Set.InjOn (couplingLabelRank V) V := by
  intro x hx y hy he
  rcases lt_trichotomy x y with h | h | h
  · have := couplingLabelRank_strictMono V hx hy h
    omega
  · exact h
  · have := couplingLabelRank_strictMono V hy hx h
    omega

theorem couplingLabelRank_image (V : Finset ℕ) :
    V.image (couplingLabelRank V) = Finset.range V.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (couplingLabelRank_lt_card V hx)
  · rw [Finset.card_range, Finset.card_image_of_injOn (couplingLabelRank_injOn V)]

theorem couplingLabelRank_insert_old (V : Finset ℕ) {fresh x : ℕ}
    (hgt : ∀ y ∈ V, y < fresh) (hx : x ∈ V) :
    couplingLabelRank (insert fresh V) x = couplingLabelRank V x := by
  have hf : ¬ fresh < x := by have := hgt x hx; omega
  simp [couplingLabelRank, Finset.filter_insert, hf]

theorem couplingLabelRank_insert_new (V : Finset ℕ) {fresh : ℕ}
    (hgt : ∀ y ∈ V, y < fresh) : couplingLabelRank (insert fresh V) fresh = V.card := by
  have heq : V.filter (fun y ↦ y < fresh) = V := Finset.filter_eq_self.mpr hgt
  simp [couplingLabelRank, Finset.filter_insert, heq]

theorem couplingLabelRank_root (V : Finset ℕ) (N : ℕ)
    (hroots : Finset.range N ⊆ V) {r : ℕ} (hr : r < N) : couplingLabelRank V r = r := by
  have heq : V.filter (fun y ↦ y < r) = Finset.range r := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨hroots (Finset.mem_range.mpr (hx.trans hr)), hx⟩⟩
  simp [couplingLabelRank, heq]

noncomputable def couplingLabelAtRank (V : Finset ℕ) (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ x ∈ V, couplingLabelRank V x = n then Nat.find h else 0

theorem couplingLabelAtRank_rank (V : Finset ℕ) {x : ℕ} (hx : x ∈ V) :
    couplingLabelAtRank V (couplingLabelRank V x) = x := by
  classical
  have hex : ∃ y ∈ V, couplingLabelRank V y = couplingLabelRank V x := ⟨x, hx, rfl⟩
  rw [couplingLabelAtRank, dite_eq_left hex]
  exact couplingLabelRank_injOn V (Nat.find_spec hex).1 hx (Nat.find_spec hex).2

theorem couplingLabelAtRank_spec (V : Finset ℕ) {n : ℕ} (hn : n < V.card) :
    couplingLabelAtRank V n ∈ V ∧ couplingLabelRank V (couplingLabelAtRank V n) = n := by
  classical
  have himg : n ∈ V.image (couplingLabelRank V) := by
    rw [couplingLabelRank_image]
    exact Finset.mem_range.mpr hn
  have hex : ∃ x ∈ V, couplingLabelRank V x = n := Finset.mem_image.mp himg
  rw [couplingLabelAtRank, dite_eq_left hex]
  exact Nat.find_spec hex

noncomputable def CouplingGenealogy.chronological (s : CouplingGenealogy) : CouplingGenealogy :=
  { carrier :=
      { vertices := Finset.range s.carrier.vertices.card
        active := s.carrier.active.image (couplingLabelRank s.carrier.vertices)
        active_sub_vertices := by
          intro n hn
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
          exact Finset.mem_range.mpr
            (couplingLabelRank_lt_card _ (s.carrier.active_sub_vertices hx)) }
    parent := fun n ↦ if n < s.carrier.vertices.card then
      couplingLabelRank s.carrier.vertices (s.parent (couplingLabelAtRank s.carrier.vertices n))
      else 0 }

theorem CouplingGenealogy.chronological_normalized (s : CouplingGenealogy) :
    s.chronological.Normalized := by
  intro n hn
  simp only [CouplingGenealogy.chronological, Finset.mem_range] at hn ⊢
  simp [hn]

theorem CouplingGenealogy.chronological_parent_rank (s : CouplingGenealogy)
    {x : ℕ} (hx : x ∈ s.carrier.vertices) :
    s.chronological.parent (couplingLabelRank s.carrier.vertices x) =
      couplingLabelRank s.carrier.vertices (s.parent x) := by
  simp [CouplingGenealogy.chronological, couplingLabelRank_lt_card _ hx,
    couplingLabelAtRank_rank _ hx]

theorem CouplingGenealogy.chronological_valid (s : CouplingGenealogy) (N : ℕ)
    (hs : s.Valid (Finset.range N)) : s.chronological.Valid (Finset.range N) := by
  constructor
  · have hc : N ≤ s.carrier.vertices.card := by
      simpa using Finset.card_le_card hs.1
    exact Finset.range_mono hc
  · intro n hn hnroot
    have hn' : n < s.carrier.vertices.card := Finset.mem_range.mp hn
    let x := couplingLabelAtRank s.carrier.vertices n
    obtain ⟨hx, hxn⟩ := couplingLabelAtRank_spec s.carrier.vertices hn'
    have hxroot : x ∉ Finset.range N := by
      intro hxr
      have he := couplingLabelRank_root s.carrier.vertices N hs.1 (Finset.mem_range.mp hxr)
      apply hnroot
      have hnx : n = x := hxn.symm.trans he
      simpa only [hnx] using hxr
    obtain ⟨hparent, hlt⟩ := hs.2 x hx hxroot
    have hp : s.chronological.parent n = couplingLabelRank s.carrier.vertices (s.parent x) := by
      rw [← hxn]
      exact s.chronological_parent_rank hx
    rw [hp]
    constructor
    · exact Finset.mem_range.mpr (couplingLabelRank_lt_card _ hparent)
    · rw [← hxn]
      exact couplingLabelRank_strictMono _ hparent hx hlt

theorem CouplingCarrier.ext_vertices_active {a b : CouplingCarrier}
    (hv : a.vertices = b.vertices) (ha : a.active = b.active) : a = b := by
  cases a
  cases b
  cases hv
  cases ha
  rfl

theorem CouplingGenealogy.ext_normalized {a b : CouplingGenealogy}
    (ha : a.Normalized) (hb : b.Normalized) (hc : a.carrier = b.carrier)
    (hp : ∀ x ∈ a.carrier.vertices, a.parent x = b.parent x) : a = b := by
  apply CouplingGenealogy.ext_carrier_parent hc
  funext x
  by_cases hx : x ∈ a.carrier.vertices
  · exact hp x hx
  · rw [ha x hx, hb x (by simpa only [← hc] using hx)]

theorem couplingLabelRank_image_erase (V A : Finset ℕ) (hA : A ⊆ V)
    {v : ℕ} (hv : v ∈ V) :
    (A.erase v).image (couplingLabelRank V) = (A.image (couplingLabelRank V)).erase
      (couplingLabelRank V v) := by
  ext n
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨x, ⟨hxv, hx⟩, rfl⟩
    exact ⟨fun he ↦ hxv (couplingLabelRank_injOn V (hA hx) hv he), ⟨x, hx, rfl⟩⟩
  · rintro ⟨hnv, x, hx, he⟩
    refine ⟨x, ⟨?_, hx⟩, he⟩
    intro hxv
    subst x
    exact hnv he.symm

theorem CouplingGenealogy.chronological_freeze (s : CouplingGenealogy)
    {v fresh : ℕ} (hv : v ∈ s.carrier.active) :
    (s.update v fresh false).chronological =
      s.chronological.update (couplingLabelRank s.carrier.vertices v)
        s.carrier.vertices.card false := by
  have hcv : couplingLabelRank s.carrier.vertices v ∈ s.chronological.carrier.active :=
    Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have hcv' : ∃ x ∈ s.carrier.active,
      couplingLabelRank s.carrier.vertices x = couplingLabelRank s.carrier.vertices v :=
    ⟨v, hv, rfl⟩
  apply CouplingGenealogy.ext_carrier_parent
  · apply CouplingCarrier.ext_vertices_active
    · simp [CouplingGenealogy.chronological, CouplingGenealogy.update,
        CouplingCarrier.update, hv, hcv']
    · simpa [CouplingGenealogy.chronological, CouplingGenealogy.update,
        CouplingCarrier.update, hv, hcv'] using
        couplingLabelRank_image_erase s.carrier.vertices s.carrier.active
          s.carrier.active_sub_vertices (s.carrier.active_sub_vertices hv)
  · funext n
    simp [CouplingGenealogy.chronological, CouplingGenealogy.update,
      CouplingCarrier.update, hv]

theorem CouplingGenealogy.chronological_birth (s : CouplingGenealogy)
    {v fresh : ℕ} (hv : v ∈ s.carrier.active)
    (hgt : ∀ x ∈ s.carrier.vertices, x < fresh)
    (hparent : ∀ x ∈ s.carrier.vertices, s.parent x ∈ s.carrier.vertices) :
    (s.update v fresh true).chronological =
      s.chronological.update (couplingLabelRank s.carrier.vertices v)
        s.carrier.vertices.card true := by
  let V := s.carrier.vertices
  let m := V.card
  let a := s.update v fresh true
  let b := s.chronological.update (couplingLabelRank V v) m true
  have hvV : v ∈ V := s.carrier.active_sub_vertices hv
  have hf : fresh ∉ V := fun hx ↦ (hgt fresh hx).false
  have hcv : couplingLabelRank V v ∈ s.chronological.carrier.active :=
    Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have hcv' : ∃ x ∈ s.carrier.active,
      couplingLabelRank s.carrier.vertices x = couplingLabelRank s.carrier.vertices v :=
    ⟨v, hv, rfl⟩
  have haV : a.carrier.vertices = insert fresh V := by
    simp [a, V, CouplingGenealogy.update, CouplingCarrier.update, hv]
  have hcard : a.carrier.vertices.card = m + 1 := by rw [haV, Finset.card_insert_of_notMem hf]
  have hacts : a.chronological.carrier.active = insert m s.chronological.carrier.active := by
    change (a.carrier.active.image (couplingLabelRank a.carrier.vertices)) = _
    have haa : a.carrier.active = insert fresh s.carrier.active := by
      simp [a, CouplingGenealogy.update, CouplingCarrier.update, hv]
    rw [haa, haV, Finset.image_insert, couplingLabelRank_insert_new V hgt]
    congr 1
    apply Finset.image_congr
    intro x hx
    exact couplingLabelRank_insert_old V hgt (s.carrier.active_sub_vertices hx)
  have hc : a.chronological.carrier = b.carrier := by
    apply CouplingCarrier.ext_vertices_active
    · change Finset.range a.carrier.vertices.card = _
      rw [hcard]
      simp [b, CouplingGenealogy.update, CouplingCarrier.update, hcv',
        CouplingGenealogy.chronological, V, m, Finset.range_add_one]
    · simpa [b, CouplingGenealogy.update, CouplingCarrier.update, hcv] using hacts
  apply CouplingGenealogy.ext_normalized a.chronological_normalized
    (CouplingGenealogy.normalized_update s.chronological_normalized _ _ _) hc
  intro n hn
  have hn' : n ∈ a.carrier.vertices.image (couplingLabelRank a.carrier.vertices) := by
    rw [couplingLabelRank_image]
    exact hn
  obtain ⟨x, hx, hxn⟩ := Finset.mem_image.mp hn'
  rw [← hxn, a.chronological_parent_rank hx]
  have hx' : x ∈ insert fresh V := by rwa [haV] at hx
  rcases Finset.mem_insert.mp hx' with hxf | hxV
  · subst x
    have hpa : a.parent fresh = v := by simp [a, CouplingGenealogy.update, hv]
    rw [hpa, haV, couplingLabelRank_insert_new V hgt,
      couplingLabelRank_insert_old V hgt hvV]
    simp [CouplingGenealogy.update, hcv, m]
  · have hxf : x ≠ fresh := fun he ↦ hf (he ▸ hxV)
    have hpa : a.parent x = s.parent x :=
      (s.parent_update_old v fresh hf true x hxV).symm
    have hxm : couplingLabelRank V x ≠ m := (couplingLabelRank_lt_card V hxV).ne
    rw [hpa, haV, couplingLabelRank_insert_old V hgt (hparent x hxV),
      couplingLabelRank_insert_old V hgt hxV]
    simpa [b, CouplingGenealogy.update, hcv, Function.update_of_ne hxm] using
      (s.chronological_parent_rank hxV).symm

theorem couplingLabelRank_selectFinite (V A : Finset ℕ) (hA : A.Nonempty)
    (hAV : A ⊆ V) (u : ℝ) :
    couplingLabelRank V (selectFinite A hA u) =
      selectFinite (A.image (couplingLabelRank V)) (hA.image _) u := by
  have hcard : (A.image (couplingLabelRank V)).card = A.card :=
    Finset.card_image_of_injOn (fun _ hx _ hy he ↦
      couplingLabelRank_injOn V (hAV hx) (hAV hy) he)
  have hmono : StrictMono (fun i : Fin A.card ↦ couplingLabelRank V (A.orderEmbOfFin rfl i)) := by
    intro i j hij
    exact couplingLabelRank_strictMono V (hAV (Finset.orderEmbOfFin_mem A rfl i))
      (hAV (Finset.orderEmbOfFin_mem A rfl j)) ((A.orderEmbOfFin rfl).strictMono hij)
  have huniq := Finset.orderEmbOfFin_unique hcard
    (fun i : Fin A.card ↦ Finset.mem_image.mpr
      ⟨A.orderEmbOfFin rfl i, Finset.orderEmbOfFin_mem A rfl i, rfl⟩) hmono
  change couplingLabelRank V (A.orderEmbOfFin rfl (Model.uniformRank A.card hA.card_pos u)) =
    (A.image (couplingLabelRank V)).orderEmbOfFin rfl
      (Model.uniformRank (A.image (couplingLabelRank V)).card (hA.image _).card_pos u)
  rw [congrFun huniq (Model.uniformRank A.card hA.card_pos u)]
  apply Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr
  simp only [Model.uniformRank, hcard]

theorem CouplingGenealogy.chronological_initial (N : ℕ) :
    (CouplingGenealogy.initial (Finset.range N)).chronological =
      CouplingGenealogy.initial (Finset.range N) := by
  apply CouplingGenealogy.ext_carrier_parent
  · apply CouplingCarrier.ext_vertices_active
    · simp [CouplingGenealogy.chronological, CouplingGenealogy.initial]
    · simpa [CouplingGenealogy.chronological, CouplingGenealogy.initial] using
        couplingLabelRank_image (Finset.range N)
  · funext n
    simp [CouplingGenealogy.chronological, CouplingGenealogy.initial, couplingLabelRank]

theorem CouplingGenealogy.chronological_update (s : CouplingGenealogy)
    {v fresh : ℕ} (hv : v ∈ s.carrier.active)
    (hgt : ∀ x ∈ s.carrier.vertices, x < fresh)
    (hparent : ∀ x ∈ s.carrier.vertices, s.parent x ∈ s.carrier.vertices) (b : Bool) :
    (s.update v fresh b).chronological =
      s.chronological.update (couplingLabelRank s.carrier.vertices v)
        s.carrier.vertices.card b := by
  cases b
  · exact s.chronological_freeze hv
  · exact s.chronological_birth hv hgt hparent

theorem correctedCouplingStage_root_parent
    (roots : Finset ℕ) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) {x : ℕ} (hx : x ∈ roots) :
    (correctedCouplingStage roots p q r w j).trees.lower.parent x = 0 ∧
      (correctedCouplingStage roots p q r w j).trees.middle.parent x = 0 ∧
      (correctedCouplingStage roots p q r w j).trees.upper.parent x = 0 := by
  have h := correctedCouplingStage_treeLE_of_le roots hpq r w (Nat.zero_le j)
  exact ⟨(h.1.2 x hx).symm, (h.2.1.2 x hx).symm, (h.2.2.2 x hx).symm⟩

theorem CouplingGenealogy.parent_mem_of_valid_roots (s : CouplingGenealogy)
    (N : ℕ) (hN : 0 < N) (hs : s.Valid (Finset.range N))
    (hroot : ∀ x ∈ Finset.range N, s.parent x = 0) :
    ∀ x ∈ s.carrier.vertices, s.parent x ∈ s.carrier.vertices := by
  intro x hx
  by_cases hr : x ∈ Finset.range N
  · rw [hroot x hr]
    exact hs.1 (Finset.mem_range.mpr hN)
  · exact (hs.2 x hx hr).1

theorem correctedCouplingStage_middle_parent_mem
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) :
    ∀ x ∈ (correctedCouplingStage (Finset.range N) p q r w j).trees.middle.carrier.vertices,
      (correctedCouplingStage (Finset.range N) p q r w j).trees.middle.parent x ∈
        (correctedCouplingStage (Finset.range N) p q r w j).trees.middle.carrier.vertices :=
  CouplingGenealogy.parent_mem_of_valid_roots _ N hN
    (correctedCouplingStage_valid _ hpq r w j).2.1
    (fun _ hx ↦ (correctedCouplingStage_root_parent _ hpq r w j hx).2.1)

end HeightPaper.CountCoupling
