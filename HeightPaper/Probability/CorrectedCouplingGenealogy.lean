module

public import HeightPaper.Probability.CorrectedCouplingCarrier

/-!
# A common genealogy for the corrected coupling

Fresh births are given a common global label.  Their parent is the selected
active vertex.  The theorem below upgrades carrier inclusion to agreement of
parent edges on every vertex of the smaller forest.  This is a deterministic
part of the corrected tree sandwich; the stochastic marginal laws and the
time-changed uniform-active selection remain separate obligations.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

structure CouplingGenealogy where
  carrier : CouplingCarrier
  parent : ℕ → ℕ

def CouplingGenealogy.LE (a b : CouplingGenealogy) : Prop :=
  a.carrier.LE b.carrier ∧
    ∀ x ∈ a.carrier.vertices, a.parent x = b.parent x

/-- A finite rooted forest on the shared labels: every nonroot has an
earlier parent in the carrier.  Strictly decreasing parent labels rule out
cycles. -/
def CouplingGenealogy.Valid (s : CouplingGenealogy)
    (roots : Finset ℕ) : Prop :=
  roots ⊆ s.carrier.vertices ∧
    ∀ x ∈ s.carrier.vertices, x ∉ roots →
      s.parent x ∈ s.carrier.vertices ∧ s.parent x < x

/-- Births update the global parent pointer at a fresh label; recovery or a
skipped event leaves the genealogy unchanged. -/
def CouplingGenealogy.update (s : CouplingGenealogy) (v fresh : ℕ)
    (birth : Bool) : CouplingGenealogy :=
  { carrier := s.carrier.update v fresh birth
    parent := if v ∈ s.carrier.active ∧ birth = true then
        Function.update s.parent fresh v
      else s.parent }

theorem CouplingGenealogy.valid_update {s : CouplingGenealogy}
    {roots : Finset ℕ} (hs : s.Valid roots)
    (v fresh : ℕ)
    (hgt : ∀ x ∈ s.carrier.vertices, x < fresh)
    (birth : Bool) : (s.update v fresh birth).Valid roots := by
  by_cases hv : v ∈ s.carrier.active
  · cases birth
    · simpa [CouplingGenealogy.Valid, CouplingGenealogy.update,
        CouplingCarrier.update, hv] using hs
    · refine ⟨?_, ?_⟩
      · simpa [CouplingGenealogy.update, CouplingCarrier.update, hv] using
          hs.1.trans (Finset.subset_insert fresh s.carrier.vertices)
      · intro x hx hroot
        have hxinsert : x ∈ insert fresh s.carrier.vertices := by
          simpa [CouplingGenealogy.update, CouplingCarrier.update, hv] using hx
        by_cases hxf : x = fresh
        · subst x
          have hvvertex : v ∈ s.carrier.vertices :=
            s.carrier.active_sub_vertices hv
          have hvlt := hgt v hvvertex
          simpa [CouplingGenealogy.update, CouplingCarrier.update, hv]
            using And.intro (Finset.mem_insert_of_mem hvvertex) hvlt
        · have hxold : x ∈ s.carrier.vertices := by
            simpa [Finset.mem_insert, hxf] using hxinsert
          obtain ⟨hpar, hlt⟩ := hs.2 x hxold hroot
          simpa [CouplingGenealogy.update, CouplingCarrier.update, hv,
            Function.update_of_ne hxf] using
            (And.intro (Finset.mem_insert_of_mem hpar) hlt)
  · simpa [CouplingGenealogy.Valid, CouplingGenealogy.update,
      CouplingCarrier.update, hv] using hs

/-- The shared-label construction preserves genealogical inclusion. -/
theorem CouplingGenealogy.update_mono {a b : CouplingGenealogy}
    (hab : a.LE b) (v fresh : ℕ)
    (hfresh : fresh ∉ b.carrier.vertices)
    {birthA birthB : Bool}
    (hbirth : v ∈ a.carrier.active → birthA = true → birthB = true) :
    (a.update v fresh birthA).LE (b.update v fresh birthB) := by
  obtain ⟨hcar, hparent⟩ := hab
  have hcar' := CouplingCarrier.update_mono hcar v fresh hbirth
  refine ⟨hcar', ?_⟩
  intro x hx
  have hnotfresh : ∀ y ∈ a.carrier.vertices, y ≠ fresh := by
    intro y hy he
    exact hfresh (he ▸ hcar.1 hy)
  by_cases hva : v ∈ a.carrier.active
  · have hvb : v ∈ b.carrier.active := hcar.2 hva
    cases birthA <;> cases birthB
    · have hxold : x ∈ a.carrier.vertices := by
        simpa [CouplingGenealogy.update, CouplingCarrier.update, hva] using hx
      simpa [CouplingGenealogy.update, CouplingCarrier.update, hva, hvb]
        using hparent x hxold
    · have hxold : x ∈ a.carrier.vertices := by
        simpa [CouplingGenealogy.update, CouplingCarrier.update, hva] using hx
      have hne : x ≠ fresh := hnotfresh x hxold
      simpa [CouplingGenealogy.update, CouplingCarrier.update, hva, hvb,
        Function.update_of_ne hne] using hparent x hxold
    · exact False.elim (by have := hbirth hva rfl; contradiction)
    · by_cases hxf : x = fresh
      · subst x
        simp [CouplingGenealogy.update, hva, hvb]
      · have hxold : x ∈ a.carrier.vertices := by
          simpa [CouplingGenealogy.update, CouplingCarrier.update, hva, hxf] using hx
        simpa [CouplingGenealogy.update, hva, hvb, hxf]
          using hparent x hxold
  · have hxold : x ∈ a.carrier.vertices := by
      simpa [CouplingGenealogy.update, CouplingCarrier.update, hva] using hx
    have hne : x ≠ fresh := hnotfresh x hxold
    by_cases hvb : v ∈ b.carrier.active
    · cases birthB
      · simpa [CouplingGenealogy.update, hva, hvb] using hparent x hxold
      · simpa [CouplingGenealogy.update, hva, hvb, hne] using hparent x hxold
    · simpa [CouplingGenealogy.update, hva, hvb] using hparent x hxold

theorem CouplingGenealogy.triple_update_sandwich
    {lower middle upper : CouplingGenealogy}
    (hlm : lower.LE middle) (hmu : middle.LE upper)
    {p r q u : ℝ} (hpr : p ≤ r) (hrq : r ≤ q)
    (v fresh : ℕ) (hfresh : fresh ∉ upper.carrier.vertices) :
    (lower.update v fresh (recoveryThresholdBirth q u)).LE
      (middle.update v fresh (recoveryThresholdBirth r u)) ∧
    (middle.update v fresh (recoveryThresholdBirth r u)).LE
      (upper.update v fresh (recoveryThresholdBirth p u)) := by
  have hfreshMid : fresh ∉ middle.carrier.vertices :=
    fun hx ↦ hfresh (hmu.1.1 hx)
  exact ⟨CouplingGenealogy.update_mono hlm v fresh hfreshMid
      (fun _ ↦ recoveryThresholdBirth_mono_lower hrq),
    CouplingGenealogy.update_mono hmu v fresh hfresh
      (fun _ ↦ recoveryThresholdBirth_mono_upper hpr)⟩

def CouplingGenealogy.fresh (s : CouplingGenealogy) : ℕ :=
  s.carrier.vertices.sup id + 1

theorem CouplingGenealogy.fresh_not_mem (s : CouplingGenealogy) :
    s.fresh ∉ s.carrier.vertices := by
  intro hmem
  have hle : s.fresh ≤ s.carrier.vertices.sup id :=
    Finset.le_sup (f := id) hmem
  unfold CouplingGenealogy.fresh at hle
  omega

theorem CouplingGenealogy.mem_lt_fresh (s : CouplingGenealogy)
    {x : ℕ} (hx : x ∈ s.carrier.vertices) : x < s.fresh := by
  have hle : x ≤ s.carrier.vertices.sup id :=
    Finset.le_sup (f := id) hx
  unfold CouplingGenealogy.fresh
  omega

def CouplingGenealogy.initial (roots : Finset ℕ) : CouplingGenealogy :=
  { carrier := { vertices := roots
                 active := roots
                 active_sub_vertices := by intro x hx; exact hx }
    parent := fun _ ↦ 0 }

theorem CouplingGenealogy.initial_valid (roots : Finset ℕ) :
    (CouplingGenealogy.initial roots).Valid roots := by
  constructor
  · intro x hx
    exact hx
  · intro x hx hnot
    exact False.elim (hnot hx)

structure CouplingTriple where
  lower : CouplingGenealogy
  middle : CouplingGenealogy
  upper : CouplingGenealogy

def CouplingTriple.Ordered (s : CouplingTriple) : Prop :=
  s.lower.LE s.middle ∧ s.middle.LE s.upper

def CouplingTriple.Valid (s : CouplingTriple) (roots : Finset ℕ) : Prop :=
  s.lower.Valid roots ∧ s.middle.Valid roots ∧ s.upper.Valid roots

def CouplingTriple.initial (roots : Finset ℕ) : CouplingTriple :=
  { lower := CouplingGenealogy.initial roots
    middle := CouplingGenealogy.initial roots
    upper := CouplingGenealogy.initial roots }

theorem CouplingTriple.initial_ordered (roots : Finset ℕ) :
    (CouplingTriple.initial roots).Ordered := by
  simp [CouplingTriple.Ordered, CouplingTriple.initial,
    CouplingGenealogy.LE, CouplingCarrier.LE]

theorem CouplingTriple.initial_valid (roots : Finset ℕ) :
    (CouplingTriple.initial roots).Valid roots := by
  exact ⟨CouplingGenealogy.initial_valid roots,
    CouplingGenealogy.initial_valid roots,
    CouplingGenealogy.initial_valid roots⟩

/-- One common draw updates all three genealogies with the same fresh label. -/
noncomputable def CouplingTriple.step (s : CouplingTriple) (p q r u : ℝ)
    (v : ℕ) : CouplingTriple :=
  { lower := s.lower.update v s.upper.fresh (recoveryThresholdBirth q u)
    middle := s.middle.update v s.upper.fresh (recoveryThresholdBirth r u)
    upper := s.upper.update v s.upper.fresh (recoveryThresholdBirth p u) }

theorem CouplingTriple.step_ordered {s : CouplingTriple}
    (hs : s.Ordered) {p q r u : ℝ} (hpr : p ≤ r) (hrq : r ≤ q)
    (v : ℕ) : (s.step p q r u v).Ordered := by
  exact CouplingGenealogy.triple_update_sandwich hs.1 hs.2 hpr hrq
    v s.upper.fresh s.upper.fresh_not_mem

/-- No bound on the middle recovery probability is needed once its active
set is empty.  This is the terminal-step distinction in the corrected event:
the bound is used for the final recovery, then the smaller forests freeze. -/
theorem CouplingTriple.step_ordered_of_middle_active {s : CouplingTriple}
    (hs : s.Ordered) {p q r u : ℝ}
    (hbound : s.middle.carrier.active.Nonempty → p ≤ r ∧ r ≤ q)
    (v : ℕ) : (s.step p q r u v).Ordered := by
  have hfreshMid : s.upper.fresh ∉ s.middle.carrier.vertices :=
    fun hx ↦ s.upper.fresh_not_mem (hs.2.1.1 hx)
  refine ⟨CouplingGenealogy.update_mono hs.1 v s.upper.fresh hfreshMid ?_,
    CouplingGenealogy.update_mono hs.2 v s.upper.fresh
      s.upper.fresh_not_mem ?_⟩
  · intro hv hb
    have hm : s.middle.carrier.active.Nonempty :=
      ⟨v, hs.1.1.2 hv⟩
    exact recoveryThresholdBirth_mono_lower (hbound hm).2 hb
  · intro hv hb
    have hm : s.middle.carrier.active.Nonempty := ⟨v, hv⟩
    exact recoveryThresholdBirth_mono_upper (hbound hm).1 hb

theorem CouplingTriple.step_valid {s : CouplingTriple} {roots : Finset ℕ}
    (hs : s.Ordered) (hv : s.Valid roots) (p q r u : ℝ) (v : ℕ) :
    (s.step p q r u v).Valid roots := by
  have hgtLower : ∀ x ∈ s.lower.carrier.vertices, x < s.upper.fresh := by
    intro x hx
    exact s.upper.mem_lt_fresh (hs.2.1.1 (hs.1.1.1 hx))
  have hgtMiddle : ∀ x ∈ s.middle.carrier.vertices, x < s.upper.fresh := by
    intro x hx
    exact s.upper.mem_lt_fresh (hs.2.1.1 hx)
  exact ⟨s.lower.valid_update hv.1 v s.upper.fresh hgtLower
      (recoveryThresholdBirth q u),
    s.middle.valid_update hv.2.1 v s.upper.fresh hgtMiddle
      (recoveryThresholdBirth r u),
    s.upper.valid_update hv.2.2 v s.upper.fresh
      (fun x hx ↦ s.upper.mem_lt_fresh hx) (recoveryThresholdBirth p u)⟩

structure CouplingDraw where
  recovery : ℝ
  uniform : ℝ
  selected : ℕ

/-- A finite common-draw construction, with the current upper carrier choosing
the next shared fresh label.  Uniform-active-vertex sampling is not built into
this deterministic operation. -/
noncomputable def CouplingTriple.run (s : CouplingTriple) (p q : ℝ)
    (draws : List CouplingDraw) : CouplingTriple :=
  draws.foldl
    (fun t d ↦ t.step p q d.recovery d.uniform d.selected) s

/-- Bounds are required only while the middle forest has an active vertex.
In particular they cover its extinction step and are unnecessary afterwards. -/
def CouplingTriple.RunGood (s : CouplingTriple) (p q : ℝ) :
    List CouplingDraw → Prop
  | [] => True
  | d :: ds =>
      (s.middle.carrier.active.Nonempty →
        p ≤ d.recovery ∧ d.recovery ≤ q) ∧
      (s.step p q d.recovery d.uniform d.selected).RunGood p q ds

theorem CouplingTriple.run_ordered_of_good {s : CouplingTriple}
    (hs : s.Ordered) {p q : ℝ} (draws : List CouplingDraw)
    (hgood : s.RunGood p q draws) :
    (s.run p q draws).Ordered := by
  induction draws generalizing s with
  | nil => simpa [CouplingTriple.run] using hs
  | cons d ds ih =>
      have hd := hgood.1
      have htail := hgood.2
      simpa [CouplingTriple.run, List.foldl_cons] using
        ih (s := s.step p q d.recovery d.uniform d.selected)
          (s.step_ordered_of_middle_active hs hd d.selected) htail

theorem CouplingTriple.run_valid_of_good {s : CouplingTriple}
    {roots : Finset ℕ} (hs : s.Ordered) (hv : s.Valid roots)
    {p q : ℝ} (draws : List CouplingDraw)
    (hgood : s.RunGood p q draws) :
    (s.run p q draws).Valid roots := by
  induction draws generalizing s with
  | nil => simpa [CouplingTriple.run] using hv
  | cons d ds ih =>
      have hd := hgood.1
      have htail := hgood.2
      simpa [CouplingTriple.run, List.foldl_cons] using
        ih (s := s.step p q d.recovery d.uniform d.selected)
          (s.step_ordered_of_middle_active hs hd d.selected)
          (s.step_valid hs hv p q d.recovery d.uniform d.selected) htail

theorem CouplingTriple.run_ordered {s : CouplingTriple}
    (hs : s.Ordered) {p q : ℝ} (draws : List CouplingDraw)
    (hbound : ∀ d ∈ draws, p ≤ d.recovery ∧ d.recovery ≤ q) :
    (s.run p q draws).Ordered := by
  induction draws generalizing s with
  | nil => simpa [CouplingTriple.run] using hs
  | cons d ds ih =>
      have hd := hbound d (by simp)
      have htail : ∀ d' ∈ ds, p ≤ d'.recovery ∧ d'.recovery ≤ q :=
        fun d' hmem ↦ hbound d' (by simp [hmem])
      simpa [CouplingTriple.run, List.foldl_cons] using
        ih (s := s.step p q d.recovery d.uniform d.selected)
          (s.step_ordered hs hd.1 hd.2 d.selected) htail

end HeightPaper.CountCoupling
