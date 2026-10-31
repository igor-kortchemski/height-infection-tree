module

public import HeightPaper.Probability.CorrectedCouplingFiniteState
public import HeightPaper.Probability.CorrectedCouplingLimit

/-!
# Structural invariants of the concrete coupled recursion

The invariants hold even off the corrected event. In particular the middle
can continue on its own labels after the coupling condition fails.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

theorem CouplingGenealogy.update_eq_self_of_empty
    (s : CouplingGenealogy) (hs : s.carrier.active = ∅)
    (v fresh : ℕ) (b : Bool) : s.update v fresh b = s := by
  simp [CouplingGenealogy.update, CouplingCarrier.update, hs]

theorem CorrectedCouplingState.step_middle_eq_of_empty
    (s : CorrectedCouplingState) (hm : s.trees.middle.carrier.active = ∅)
    (p q : ℝ) (r : List Bool → ℝ) (u recovery : ℝ) :
    (s.step p q r u recovery).trees.middle = s.trees.middle := by
  by_cases hg : s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q
  · by_cases hu : s.trees.upper.carrier.active.Nonempty <;>
      simp [CorrectedCouplingState.step, hg, hu, CouplingTriple.step,
        CouplingGenealogy.update, CouplingCarrier.update, hm]
  · simp [CorrectedCouplingState.step, hg, CouplingGenealogy.update,
      CouplingCarrier.update, hm]

/-- The lower projection always uses the same upper proposal and its own
constant threshold, independently of the middle word or switch flag. -/
theorem CorrectedCouplingState.step_lower
    (s : CorrectedCouplingState) (hl : s.trees.lower.LE s.trees.upper)
    (p q : ℝ) (r : List Bool → ℝ) (u recovery : ℝ) :
    (s.step p q r u recovery).trees.lower =
      s.trees.lower.update (s.trees.upper.totalSelected u) s.trees.upper.fresh
        (recoveryThresholdBirth q recovery) := by
  by_cases hg : s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q
  · by_cases hu : s.trees.upper.carrier.active.Nonempty
    · simp [CorrectedCouplingState.step, hg, hu, CouplingTriple.step,
        CouplingGenealogy.totalSelected]
    · have heu := Finset.not_nonempty_iff_eq_empty.mp hu
      have hel : s.trees.lower.carrier.active = ∅ := by
        apply Finset.subset_empty.mp
        simpa [heu] using hl.1.2
      simp [CorrectedCouplingState.step, hg, hu, CouplingGenealogy.totalSelected,
        s.trees.lower.update_eq_self_of_empty hel]
  · simp [CorrectedCouplingState.step, hg, CouplingGenealogy.totalSelected]

theorem CorrectedCouplingState.treeLE_step
    (s : CorrectedCouplingState)
    (hl : s.trees.lower.LE s.trees.upper)
    (hf : s.faithful = true → s.trees.Ordered)
    (p q : ℝ) (r : List Bool → ℝ) (u recovery : ℝ) :
    s.trees.TreeLE (s.step p q r u recovery).trees := by
  by_cases hg : s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q
  · by_cases hu : s.trees.upper.carrier.active.Nonempty
    · simpa [CorrectedCouplingState.step, hg, hu] using
        s.trees.treeLE_step (hf hg.1) p q (r s.word) recovery
          (s.trees.upper.selectedActive hu u)
    · simpa [CorrectedCouplingState.step, hg, hu, CouplingTriple.TreeLE] using
        (show s.trees.lower.TreeLE s.trees.lower ∧
          s.trees.middle.TreeLE s.trees.middle ∧ s.trees.upper.TreeLE s.trees.upper from
          ⟨s.trees.lower.treeLE_refl, s.trees.middle.treeLE_refl, s.trees.upper.treeLE_refl⟩)
  · have hfl : s.trees.upper.fresh ∉ s.trees.lower.carrier.vertices :=
      fun hx ↦ s.trees.upper.fresh_not_mem (hl.1.1 hx)
    simpa [CorrectedCouplingState.step, hg, CouplingTriple.TreeLE] using
      (show
        s.trees.lower.TreeLE (s.trees.lower.update _ s.trees.upper.fresh _) ∧
        s.trees.middle.TreeLE (s.trees.middle.update _ s.trees.middle.fresh _) ∧
        s.trees.upper.TreeLE (s.trees.upper.update _ s.trees.upper.fresh _) from
        ⟨s.trees.lower.treeLE_update _ _ hfl _,
          s.trees.middle.treeLE_update _ _ s.trees.middle.fresh_not_mem _,
          s.trees.upper.treeLE_update _ _ s.trees.upper.fresh_not_mem _⟩)

theorem correctedCouplingStage_treeLE_succ
    (roots : Finset ℕ) {p q : ℝ} (hpq : p ≤ q)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) :
    (correctedCouplingStage roots p q r w k).trees.TreeLE
      (correctedCouplingStage roots p q r w (k + 1)).trees :=
  CorrectedCouplingState.treeLE_step _
    (correctedCouplingStage_lower_upper roots hpq r w k)
    (correctedCouplingStage_faithful_ordered roots p q r w k)
    p q r (w (0, k)) (w (1, k))

theorem correctedCouplingStage_treeLE_of_le
    (roots : Finset ℕ) {p q : ℝ} (hpq : p ≤ q)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    {k m : ℕ} (hkm : k ≤ m) :
    (correctedCouplingStage roots p q r w k).trees.TreeLE
      (correctedCouplingStage roots p q r w m).trees := by
  induction m, hkm using Nat.le_induction with
  | base => exact ⟨CouplingGenealogy.treeLE_refl _,
      CouplingGenealogy.treeLE_refl _, CouplingGenealogy.treeLE_refl _⟩
  | succ m _ ih =>
      exact CouplingTriple.treeLE_trans ih (correctedCouplingStage_treeLE_succ roots hpq r w m)

end HeightPaper.CountCoupling
