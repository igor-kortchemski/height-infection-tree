module

public import HeightPaper.Combinatorics.PlaneCompletionCompatibility

/-!
# The finite-tree completion potential

The harmonic identity is pointwise in the selected active vertex. It is
therefore usable for the lower process even when its parent proposals are
thinned from an enclosing genealogy.
-/

@[expose] public section

namespace HeightPaper.PlaneForward

open PlaneTree
open scoped Classical

def frozen (s : State) : Finset Address := s.vertices \ s.active

noncomputable def completionPotential (t : State) (a : ℝ) (s : State) : ℝ :=
  if CompletionCompatible s t then
    a ^ (t.vertices.card - (frozen s).card) * (1 - a) ^ (t.vertices.card - s.vertices.card)
  else 0

theorem frozen_card_le (s : State) : (frozen s).card ≤ s.vertices.card :=
  Finset.card_le_card Finset.sdiff_subset

theorem frozen_card_lt_of_active {s : State} (hs : Valid s) {u : Address} (hu : u ∈ s.active) :
    (frozen s).card < s.vertices.card := by
  have hcard := Finset.card_le_card hs.active_subset
  have hpos := Finset.card_pos.mpr (show s.active.Nonempty from ⟨u, hu⟩)
  rw [frozen, Finset.card_sdiff_of_subset hs.active_subset]
  omega

theorem frozen_freeze {s : State} {u : Address} (huV : u ∈ s.vertices) :
    frozen (freeze s u) = insert u (frozen s) := by
  ext v
  by_cases hv : v = u
  · subst v
    simp [frozen, freeze, huV]
  · simp [frozen, freeze, hv]

theorem frozen_freeze_card {s : State} {u : Address} (hs : Valid s) (hu : u ∈ s.active) :
    (frozen (freeze s u)).card = (frozen s).card + 1 := by
  rw [frozen_freeze (hs.active_subset hu), Finset.card_insert_of_notMem]
  simp [frozen, hu]

theorem frozen_attach {s : State} (hs : Valid s) {u : Address} (hu : u ∈ s.active) :
    frozen (attach s u) = frozen s := by
  ext v
  have hf := hs.newChild_not_mem (hs.active_subset hu)
  by_cases hv : v = newChild s u
  · subst v
    simp [frozen, attach, hf]
  · simp [frozen, attach, hv]

theorem vertices_attach_card {s : State} (hs : Valid s) {u : Address} (hu : u ∈ s.active) :
    (attach s u).vertices.card = s.vertices.card + 1 :=
  Finset.card_insert_of_notMem (hs.newChild_not_mem (hs.active_subset hu))

theorem completionPotential_nonneg (t : State) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (s : State) :
    0 ≤ completionPotential t a s := by
  unfold completionPotential
  split
  · exact mul_nonneg (pow_nonneg ha0 _) (pow_nonneg (sub_nonneg.mpr ha1) _)
  · exact le_rfl

theorem completionPotential_le_one (t : State) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (s : State) :
    completionPotential t a s ≤ 1 := by
  unfold completionPotential
  split
  · exact (mul_le_mul (pow_le_one₀ ha0 ha1)
      (pow_le_one₀ (sub_nonneg.mpr ha1) (by linarith))
      (pow_nonneg (sub_nonneg.mpr ha1) _) zero_le_one).trans_eq (one_mul 1)
  · exact zero_le_one

theorem completionPotential_harmonic {s t : State} (hs : Valid s) (ht : Valid t)
    (a : ℝ) {u : Address} (hu : u ∈ s.active) :
    a * completionPotential t a (freeze s u) + (1 - a) * completionPotential t a (attach s u) =
      completionPotential t a s := by
  have hfr := CompletionCompatible.freeze_iff (t := t) hs hu
  have hat := CompletionCompatible.attach_iff (t := t) hs ht hu
  by_cases hc : CompletionCompatible s t
  · have hvle := Finset.card_le_card hc.1
    have hflt := frozen_card_lt_of_active hs hu
    have hcount := hc.childCount_le u
    by_cases hlt : childCount s u < childCount t u
    · have haf : ¬ CompletionCompatible (freeze s u) t := by
        rw [hfr]
        omega
      have hab : CompletionCompatible (attach s u) t := hat.mpr ⟨hc, hlt⟩
      have hnew : newChild s u ∈ t.vertices := hab.1 (Finset.mem_insert_self _ _)
      have hvlt : s.vertices.card < t.vertices.card := by
        apply Finset.card_lt_card
        exact (Finset.ssubset_iff_of_subset hc.1).mpr
          ⟨newChild s u, hnew, hs.newChild_not_mem (hs.active_subset hu)⟩
      have hexp : t.vertices.card - s.vertices.card =
          (t.vertices.card - (s.vertices.card + 1)) + 1 := by omega
      simp only [completionPotential, ite_eq_right haf, ite_eq_left hab, ite_eq_left hc,
        frozen_attach hs hu, vertices_attach_card hs hu, mul_zero, zero_add]
      rw [hexp, pow_succ]
      ring
    · have heq : childCount s u = childCount t u := by omega
      have haf : CompletionCompatible (freeze s u) t := hfr.mpr ⟨hc, heq⟩
      have hab : ¬ CompletionCompatible (attach s u) t := by rw [hat]; exact fun h ↦ hlt h.2
      have hexp : t.vertices.card - (frozen s).card =
          (t.vertices.card - ((frozen s).card + 1)) + 1 := by omega
      have hVc : (freeze s u).vertices.card = s.vertices.card := rfl
      simp only [completionPotential, ite_eq_left haf, ite_eq_right hab, ite_eq_left hc,
        frozen_freeze_card hs hu, hVc, mul_zero, add_zero]
      rw [hexp, pow_succ]
      ring
  · have haf : ¬ CompletionCompatible (freeze s u) t := fun h ↦ hc (hfr.mp h).1
    have hab : ¬ CompletionCompatible (attach s u) t := fun h ↦ hc (hat.mp h).1
    simp only [completionPotential, ite_eq_right haf, ite_eq_right hab, ite_eq_right hc,
      mul_zero, add_zero]

theorem completionPotential_step_harmonic {s t : State} (hs : Valid s) (ht : Valid t)
    (a : ℝ) (u : Address) :
    a * completionPotential t a (step s false u) + (1 - a) * completionPotential t a (step s true u) =
      completionPotential t a s := by
  by_cases hu : u ∈ s.active
  · simpa only [step, ite_eq_left hu, Bool.false_eq_true, ↓reduceIte] using
      completionPotential_harmonic hs ht a hu
  · rw [step_of_not_mem hu, step_of_not_mem hu]
    ring

theorem completionPotential_initial {t : State} (ht : Valid t) (a : ℝ) :
    completionPotential t a initial = a ^ t.vertices.card * (1 - a) ^ (t.vertices.card - 1) := by
  rw [completionPotential, ite_eq_left (CompletionCompatible.initial ht)]
  simp [frozen, initial]

theorem completionPotential_of_empty {s t : State} (hs : Valid s) (ht : Valid t)
    (he : s.active = ∅) (a : ℝ) :
    completionPotential t a s = if s.vertices = t.vertices then 1 else 0 := by
  by_cases hc : CompletionCompatible s t
  · have hv := CompletionCompatible.eq_vertices_of_empty hs ht hc he
    simp [completionPotential, hc, frozen, he, hv]
  · have hv : s.vertices ≠ t.vertices := by
      intro hv
      apply hc
      refine ⟨hv ▸ Finset.Subset.refl _, ?_⟩
      intro u _ _
      unfold childCount children
      rw [hv]
    simp [completionPotential, hc, hv]

end HeightPaper.PlaneForward
