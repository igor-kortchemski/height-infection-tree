module

public import HeightPaper.Model.HeightPotential
public import HeightPaper.Model.PrescribedPath
public import HeightPaper.Model.ProfileMoments
public import HeightPaper.Model.Urn

/-! # The urn count projection of disjoint fresh outgrowths -/

@[expose] public section

open MeasureTheory
open scoped BigOperators Classical

namespace HeightPaper.Model

/-- The active population in a fixed collection of cutoff components. -/
noncomputable def outgrowthRedCount (cutoff : ℕ) (hc : 0 < cutoff) (roots : Finset ℕ)
    (s : State) : ℤ :=
  ∑ v ∈ s.active, if selectedOutgrowth cutoff hc roots s v then 1 else 0

theorem outgrowthRedCount_eq_card (cutoff : ℕ) (hc : 0 < cutoff) (roots : Finset ℕ)
    (s : State) : outgrowthRedCount cutoff hc roots s =
      ((s.active.filter (selectedOutgrowth cutoff hc roots s)).card : ℤ) := by
  simp only [outgrowthRedCount, Finset.sum_boole]

theorem outgrowthRedCount_bounds (cutoff : ℕ) (hc : 0 < cutoff) (roots : Finset ℕ)
    (s : State) : 0 ≤ outgrowthRedCount cutoff hc roots s ∧
      outgrowthRedCount cutoff hc roots s ≤ (infectious s : ℤ) := by
  rw [outgrowthRedCount_eq_card]
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast Finset.card_filter_le s.active _⟩

theorem outgrowthRedCount_recover (cutoff : ℕ) (hc : 0 < cutoff) (roots : Finset ℕ)
    (s : State) (v : Fin s.vertices) (hv : v ∈ s.active) :
    outgrowthRedCount cutoff hc roots (recover s v) = outgrowthRedCount cutoff hc roots s -
      if selectedOutgrowth cutoff hc roots s v then 1 else 0 := by
  change (∑ w ∈ s.active.erase v, if selectedOutgrowth cutoff hc roots s w then (1 : ℤ) else 0) = _
  exact eq_sub_iff_add_eq.mpr (Finset.sum_erase_add s.active _ hv)

theorem outgrowthRedCount_infect (cutoff : ℕ) (hc : 0 < cutoff) (roots : Finset ℕ)
    (s : State) (v : Fin s.vertices) (hcut : cutoff ≤ s.vertices) :
    outgrowthRedCount cutoff hc roots (infect s v) = outgrowthRedCount cutoff hc roots s +
      if selectedOutgrowth cutoff hc roots s v then 1 else 0 := by
  have hnew : Fin.last s.vertices ∉ s.active.map Fin.castSuccEmb := by
    simp only [Finset.mem_map, not_exists, not_and]
    intro w _ hw
    have hh := congrArg Fin.val hw
    change w.val = s.vertices at hh
    have := w.isLt
    omega
  unfold outgrowthRedCount
  change (∑ w ∈ insert (Fin.last s.vertices) (s.active.map Fin.castSuccEmb),
    if selectedOutgrowth cutoff hc roots (infect s v) w then (1 : ℤ) else 0) = _
  rw [Finset.sum_insert hnew, Finset.sum_map]
  simp only [Fin.coe_castSuccEmb, selectedOutgrowth_infect_old]
  have hlast : selectedOutgrowth cutoff hc roots (infect s v) (Fin.last s.vertices) ↔
      selectedOutgrowth cutoff hc roots s v := by
    simp only [selectedOutgrowth, infect,
      Tree.attachmentRoot_attach_new s.tree v cutoff hc hcut, Fin.val_castSucc]
  rw [if_congr hlast rfl rfl]
  ring

theorem outgrowthRedCount_prescribedUpdate (cutoff : ℕ) (hc : 0 < cutoff)
    (roots : Finset ℕ) (birth : Bool) (s : State) (v : Fin s.vertices)
    (hv : v ∈ s.active) (hcut : cutoff ≤ s.vertices) :
    outgrowthRedCount cutoff hc roots (prescribedUpdate birth s v) =
      outgrowthRedCount cutoff hc roots s +
        if selectedOutgrowth cutoff hc roots s v then (if birth then 1 else -1) else 0 := by
  cases birth
  · simp only [prescribedUpdate, Bool.false_eq_true, ↓reduceIte]
    rw [outgrowthRedCount_recover cutoff hc roots s v hv]
    split_ifs <;> ring
  · simp only [prescribedUpdate, ↓reduceIte]
    rw [outgrowthRedCount_infect cutoff hc roots s v hcut]

/-- The component population has exactly the two-colour urn transition mean
for every test function, under the actual uniform active-vertex choice. -/
theorem prescribedStep_outgrowthRedCount_integral (cutoff : ℕ) (hc : 0 < cutoff)
    (roots : Finset ℕ) (birth : Bool) (s : State) (ha : s.active.Nonempty)
    (hcut : cutoff ≤ s.vertices) (f : ℤ → ℝ) :
    (∫ t, f (outgrowthRedCount cutoff hc roots t) ∂(prescribedStep birth s).toMeasure) =
      Urn.proportion (infectious s) (outgrowthRedCount cutoff hc roots s) *
        f (outgrowthRedCount cutoff hc roots s + if birth then 1 else -1) +
      (1 - Urn.proportion (infectious s) (outgrowthRedCount cutoff hc roots s)) *
        f (outgrowthRedCount cutoff hc roots s) := by
  rw [prescribedStep, dite_eq_left ha,
    ← PMF.toMeasure_map _ _ (measurable_of_countable _),
    integral_map_of_stronglyMeasurable (measurable_of_countable _)
      (measurable_state _).stronglyMeasurable, uniformActive_integral_real]
  have hred : (∑ v ∈ s.active, if selectedOutgrowth cutoff hc roots s v then (1 : ℝ) else 0) =
      (outgrowthRedCount cutoff hc roots s : ℝ) := by
    simp only [outgrowthRedCount, Int.cast_sum, Int.cast_ite, Int.cast_one, Int.cast_zero]
  have heq : (∑ v ∈ s.active, f (outgrowthRedCount cutoff hc roots
      (prescribedUpdate birth s v))) =
      (infectious s : ℝ) * f (outgrowthRedCount cutoff hc roots s) +
        (outgrowthRedCount cutoff hc roots s : ℝ) *
          (f (outgrowthRedCount cutoff hc roots s + if birth then 1 else -1) -
            f (outgrowthRedCount cutoff hc roots s)) := by
    calc
      _ = ∑ v ∈ s.active,
          (f (outgrowthRedCount cutoff hc roots s) +
            (if selectedOutgrowth cutoff hc roots s v then (1 : ℝ) else 0) *
              (f (outgrowthRedCount cutoff hc roots s + if birth then 1 else -1) -
                f (outgrowthRedCount cutoff hc roots s))) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [outgrowthRedCount_prescribedUpdate cutoff hc roots birth s v hv hcut]
        split_ifs <;> simp
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hred]
        simp only [Finset.sum_const, nsmul_eq_mul, infectious]
  rw [heq]
  unfold Urn.proportion
  push_cast
  have hi : (infectious s : ℝ) ≠ 0 := by exact_mod_cast ha.card_pos.ne'
  field_simp
  ring

end HeightPaper.Model
