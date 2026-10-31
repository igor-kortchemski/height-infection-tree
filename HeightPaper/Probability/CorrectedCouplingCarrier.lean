module

public import HeightPaper.Probability.CorrectedCouplingWord

/-!
# Carrier inclusion in the corrected three-tree construction

The source coupling uses one selected vertex and one uniform recovery draw for
three forests.  A vertex absent from a smaller forest is skipped there.  This
module verifies the deterministic inclusion invariant for the vertex and active
sets.  A common parent map, uniform selection law, time changes, and the
Bienaymé marginal laws are still needed for the complete corrected lemma.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

structure CouplingCarrier where
  vertices : Finset ℕ
  active : Finset ℕ
  active_sub_vertices : active ⊆ vertices

def CouplingCarrier.LE (a b : CouplingCarrier) : Prop :=
  a.vertices ⊆ b.vertices ∧ a.active ⊆ b.active

/-- A shared fresh label is attached at an active vertex on birth, or that
vertex freezes on recovery.  If the vertex is absent, this forest skips. -/
def CouplingCarrier.update (s : CouplingCarrier) (v fresh : ℕ)
    (birth : Bool) : CouplingCarrier :=
  if v ∈ s.active then
    if birth then
      { vertices := insert fresh s.vertices
        active := insert fresh s.active
        active_sub_vertices := Finset.insert_subset_insert fresh s.active_sub_vertices }
    else
      { vertices := s.vertices
        active := s.active.erase v
        active_sub_vertices := (Finset.erase_subset v s.active).trans s.active_sub_vertices }
  else s

private theorem subset_erase_right {A B : Finset ℕ} (hAB : A ⊆ B)
    {v : ℕ} (hv : v ∉ A) : A ⊆ B.erase v := by
  intro x hx
  simp only [Finset.mem_erase]
  exact ⟨by intro he; exact hv (he ▸ hx), hAB hx⟩

/-- The smaller carrier stays inside the larger one when its births are a
subset of the larger carrier's births. -/
theorem CouplingCarrier.update_mono {a b : CouplingCarrier}
    (hab : a.LE b) (v fresh : ℕ) {birthA birthB : Bool}
    (hbirth : v ∈ a.active → birthA = true → birthB = true) :
    (a.update v fresh birthA).LE (b.update v fresh birthB) := by
  obtain ⟨hvertices, hactive⟩ := hab
  by_cases hva : v ∈ a.active
  · have hvb : v ∈ b.active := hactive hva
    cases birthA <;> cases birthB
    · simpa [CouplingCarrier.LE, CouplingCarrier.update, hva, hvb]
        using And.intro hvertices (Finset.erase_subset_erase v hactive)
    · simpa [CouplingCarrier.LE, CouplingCarrier.update, hva, hvb]
        using And.intro
          (hvertices.trans (Finset.subset_insert fresh b.vertices))
          ((Finset.erase_subset v a.active).trans
            (hactive.trans (Finset.subset_insert fresh b.active)))
    · exact False.elim (by have := hbirth hva rfl; contradiction)
    · simpa [CouplingCarrier.LE, CouplingCarrier.update, hva, hvb]
        using And.intro (Finset.insert_subset_insert fresh hvertices)
          (Finset.insert_subset_insert fresh hactive)
  · by_cases hvb : v ∈ b.active
    · cases birthB
      · simpa [CouplingCarrier.LE, CouplingCarrier.update, hva, hvb]
          using And.intro hvertices (subset_erase_right hactive hva)
      · simpa [CouplingCarrier.LE, CouplingCarrier.update, hva, hvb]
          using And.intro
            (hvertices.trans (Finset.subset_insert fresh b.vertices))
            (hactive.trans (Finset.subset_insert fresh b.active))
    · simpa [CouplingCarrier.LE, CouplingCarrier.update, hva, hvb]
        using And.intro hvertices hactive

/-- The common draw preserves both inclusions in the lower/middle/upper
triple when `p ≤ r ≤ q`. -/
theorem CouplingCarrier.triple_update_sandwich
    {lower middle upper : CouplingCarrier}
    (hlm : lower.LE middle) (hmu : middle.LE upper)
    {p r q u : ℝ} (hpr : p ≤ r) (hrq : r ≤ q)
    (v fresh : ℕ) :
    (lower.update v fresh (recoveryThresholdBirth q u)).LE
      (middle.update v fresh (recoveryThresholdBirth r u)) ∧
    (middle.update v fresh (recoveryThresholdBirth r u)).LE
      (upper.update v fresh (recoveryThresholdBirth p u)) := by
  exact ⟨CouplingCarrier.update_mono hlm v fresh
      (fun _ ↦ recoveryThresholdBirth_mono_lower hrq),
    CouplingCarrier.update_mono hmu v fresh
      (fun _ ↦ recoveryThresholdBirth_mono_upper hpr)⟩

end HeightPaper.CountCoupling
