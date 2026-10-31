module

public import HeightPaper.Probability.CorrectedCouplingRecordedHistory

/-!
# The middle remains fixed throughout its upper rejection interval

This is the deterministic bridge from the conditional upper-acceptance law
to the next actual middle event in the faithful branch.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

theorem correctedCouplingStage_upper_carrier (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) :
    (correctedCouplingStage roots p q r w j).trees.upper.carrier = upperCarrier roots p w j :=
  (congrArg CouplingGenealogy.carrier
    (correctedCouplingStage_upper_eq_upperStage roots p q r w j)).trans
      (upperStage_carrier_eq_upperCarrier roots p w j)

theorem upperPastPending_event (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (j : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ))
    (w : (Fin 2 × ℕ) → ℝ) (n : ℕ)
    (hn : upperPastPending A roots hA p j H w n = true) : w ∈ H := by
  induction n with
  | zero => exact (upperPastPending_start A roots hA p j H w).mp hn
  | succ n ih => exact ih ((upperPastPending_succ A roots hA p j H w n).mp hn).1

theorem upperPastPending_selection_eq_totalSelected (A roots : Finset ℕ) (hA : A.Nonempty)
    (p q : ℝ) (r : List Bool → ℝ) (j : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ))
    (hinit : ∀ w ∈ H, A ⊆ (upperCarrier roots p w j).active)
    (w : (Fin 2 × ℕ) → ℝ) (n : ℕ)
    (hn : upperPastPending A roots hA p j H w n = true) :
    selectFinite ((upperCarrier roots p w (j + n)).active ∪ A)
        (hA.mono Finset.subset_union_right) (w (0, j + n)) =
      (correctedCouplingStage roots p q r w (j + n)).trees.upper.totalSelected (w (0, j + n)) := by
  let t := correctedCouplingStage roots p q r w (j + n)
  have hB : t.trees.upper.carrier.active = (upperCarrier roots p w (j + n)).active :=
    congrArg CouplingCarrier.active (correctedCouplingStage_upper_carrier roots p q r w (j + n))
  have hs := upperPastPending_subset_active A roots hA p j H hinit w n hn
  have hu : t.trees.upper.carrier.active.Nonempty := by rw [hB]; exact hA.mono hs
  change _ = t.trees.upper.totalSelected _
  rw [CouplingGenealogy.totalSelected, dite_eq_left hu]
  change _ = selectFinite t.trees.upper.carrier.active hu _
  have heq : (upperCarrier roots p w (j + n)).active ∪ A = t.trees.upper.carrier.active :=
    (Finset.union_eq_left.mpr hs).trans hB.symm
  simp only [heq]

theorem faithful_middle_subset_upper_on_event
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ) (j : ℕ)
    (H : Set ((Fin 2 × ℕ) → ℝ)) (s : FiniteCouplingState)
    (hreal : ∀ w ∈ H, correctedCouplingStage roots p q r w j = s.toState)
    (hfaith : s.faithful = true) :
    ∀ w ∈ H, s.middle.1.carrier.active ⊆ (upperCarrier roots p w j).active := by
  intro w hw
  have hf : (correctedCouplingStage roots p q r w j).faithful = true := by
    rw [hreal w hw]
    exact hfaith
  have ho := (correctedCouplingStage_faithful_ordered roots p q r w j hf).2.1.2
  have hM : (correctedCouplingStage roots p q r w j).trees.middle.carrier.active =
      s.middle.1.carrier.active := congrArg (fun t : CorrectedCouplingState ↦
        t.trees.middle.carrier.active) (hreal w hw)
  have hU := congrArg CouplingCarrier.active (correctedCouplingStage_upper_carrier roots p q r w j)
  simpa only [hM, hU] using ho

/-- Rejected upper proposals leave the entire middle genealogy, its word,
and the faithful flag fixed. The rate bounds are used through acceptance. -/
theorem middle_state_while_upper_pending
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ) (j : ℕ)
    (H : Set ((Fin 2 × ℕ) → ℝ)) (s : FiniteCouplingState)
    (hreal : ∀ w ∈ H, correctedCouplingStage roots p q r w j = s.toState)
    (hfaith : s.faithful = true) (hrate : p ≤ r s.word ∧ r s.word ≤ q)
    (hA : s.middle.1.carrier.active.Nonempty)
    (w : (Fin 2 × ℕ) → ℝ) (n : ℕ)
    (hn : upperPastPending s.middle.1.carrier.active roots hA p j H w n = true) :
    (correctedCouplingStage roots p q r w (j + n)).trees.middle = s.middle.1 ∧
      (correctedCouplingStage roots p q r w (j + n)).word = s.word ∧
      (correctedCouplingStage roots p q r w (j + n)).faithful = true := by
  let A := s.middle.1.carrier.active
  have hinit := faithful_middle_subset_upper_on_event roots p q r j H s hreal hfaith
  induction n with
  | zero =>
      have hw := upperPastPending_event A roots hA p j H w 0 hn
      have he := hreal w hw
      exact ⟨congrArg (fun t : CorrectedCouplingState ↦ t.trees.middle) he,
        congrArg CorrectedCouplingState.word he,
        (congrArg CorrectedCouplingState.faithful he).trans hfaith⟩
  | succ n ih =>
      obtain ⟨hprev, hmiss⟩ := (upperPastPending_succ A roots hA p j H w n).mp hn
      obtain ⟨hM, hW, hF⟩ := ih hprev
      let t := correctedCouplingStage roots p q r w (j + n)
      change t.trees.middle = s.middle.1 at hM
      change t.word = s.word at hW
      change t.faithful = true at hF
      have hg : t.faithful = true ∧ p ≤ r t.word ∧ r t.word ≤ q :=
        ⟨hF, by simpa only [hW] using hrate⟩
      have hB : t.trees.upper.carrier.active = (upperCarrier roots p w (j + n)).active :=
        congrArg CouplingCarrier.active (correctedCouplingStage_upper_carrier roots p q r w (j + n))
      have hsub := upperPastPending_subset_active A roots hA p j H hinit w n hprev
      have hu : t.trees.upper.carrier.active.Nonempty := by rw [hB]; exact hA.mono hsub
      have hsel := upperPastPending_selection_eq_totalSelected A roots hA p q r j H hinit w n hprev
      change _ = t.trees.upper.totalSelected _ at hsel
      rw [CouplingGenealogy.totalSelected, dite_eq_left hu] at hsel
      have hmid : t.trees.middle.carrier.active = A :=
        congrArg (fun g : CouplingGenealogy ↦ g.carrier.active) hM
      have hnot : t.trees.upper.selectedActive hu (w (0, j + n)) ∉ t.trees.middle.carrier.active := by
        rw [hmid]
        exact hsel ▸ hmiss
      have hemit : t.emit p q r (w (0, j + n)) = false := by
        simp [CorrectedCouplingState.emit, hg, hu, hnot]
      have hwNext : (t.step p q r (w (0, j + n)) (w (1, j + n))).word = t.word := by
        rw [t.word_step, hemit]
        rfl
      change (t.step p q r (w (0, j + n)) (w (1, j + n))).trees.middle = s.middle.1 ∧
        (t.step p q r (w (0, j + n)) (w (1, j + n))).word = s.word ∧
        (t.step p q r (w (0, j + n)) (w (1, j + n))).faithful = true
      exact ⟨(t.middle_eq_of_no_emission p q r _ _ hemit).trans hM, hwNext.trans hW,
        by simp [CorrectedCouplingState.step, hg, hu]⟩

/-- An accepted upper proposal is an actual next middle event, with exactly
the source update after chronological relabelling. -/
theorem middle_update_at_upper_acceptance
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ) (j : ℕ)
    (H : Set ((Fin 2 × ℕ) → ℝ)) (s : FiniteCouplingState)
    (hreal : ∀ w ∈ H, correctedCouplingStage (Finset.range N) p q r w j = s.toState)
    (hfaith : s.faithful = true) (hrate : p ≤ r s.word ∧ r s.word ≤ q)
    (hA : s.middle.1.carrier.active.Nonempty)
    (w : (Fin 2 × ℕ) → ℝ) (n : ℕ)
    (hn : upperPastPending s.middle.1.carrier.active (Finset.range N) hA p j H w n = true)
    (v : ℕ) (hv : v ∈ s.middle.1.carrier.active)
    (hselected : selectFinite ((upperCarrier (Finset.range N) p w (j + n)).active ∪ s.middle.1.carrier.active)
      (hA.mono Finset.subset_union_right) (w (0, j + n)) = v) :
    let t := correctedCouplingStage (Finset.range N) p q r w (j + n)
    t.emit p q r (w (0, j + n)) = true ∧
      (t.step p q r (w (0, j + n)) (w (1, j + n))).word =
        s.word ++ [recoveryThresholdBirth (r s.word) (w (1, j + n))] ∧
      (t.step p q r (w (0, j + n)) (w (1, j + n))).trees.middle.chronological =
        s.middle.1.chronological.update (couplingLabelRank s.middle.1.carrier.vertices v)
          s.middle.1.carrier.vertices.card (recoveryThresholdBirth (r s.word) (w (1, j + n))) := by
  let roots := Finset.range N
  let A := s.middle.1.carrier.active
  let t := correctedCouplingStage roots p q r w (j + n)
  obtain ⟨hM, hW, hF⟩ := middle_state_while_upper_pending roots p q r j H s
    hreal hfaith hrate hA w n hn
  change t.trees.middle = s.middle.1 at hM
  change t.word = s.word at hW
  change t.faithful = true at hF
  have hinit := faithful_middle_subset_upper_on_event roots p q r j H s hreal hfaith
  have hsub := upperPastPending_subset_active A roots hA p j H hinit w n hn
  have hB : t.trees.upper.carrier.active = (upperCarrier roots p w (j + n)).active :=
    congrArg CouplingCarrier.active (correctedCouplingStage_upper_carrier roots p q r w (j + n))
  have hu : t.trees.upper.carrier.active.Nonempty := by rw [hB]; exact hA.mono hsub
  have hs := upperPastPending_selection_eq_totalSelected A roots hA p q r j H hinit w n hn
  change _ = t.trees.upper.totalSelected _ at hs
  rw [CouplingGenealogy.totalSelected, dite_eq_left hu] at hs
  have hvSelected : t.trees.upper.selectedActive hu (w (0, j + n)) = v := hs.symm.trans hselected
  have hg : t.faithful = true ∧ p ≤ r t.word ∧ r t.word ≤ q :=
    ⟨hF, by simpa only [hW] using hrate⟩
  have hvm : v ∈ t.trees.middle.carrier.active := by rw [hM]; exact hv
  have hemit : t.emit p q r (w (0, j + n)) = true := by
    simp [CorrectedCouplingState.emit, hg, hu, hvSelected, hvm]
  have hstep : (t.step p q r (w (0, j + n)) (w (1, j + n))).trees.middle =
      s.middle.1.update v t.trees.upper.fresh (recoveryThresholdBirth (r s.word) (w (1, j + n))) := by
    simp [CorrectedCouplingState.step, hg, hu, CouplingTriple.step, hvSelected, hM, hW, hrate]
  have ho := correctedCouplingStage_faithful_ordered roots p q r w (j + n) hF
  have hgt : ∀ x ∈ s.middle.1.carrier.vertices, x < t.trees.upper.fresh := by
    intro x hx
    have hxM : x ∈ t.trees.middle.carrier.vertices := by rw [hM]; exact hx
    exact t.trees.upper.mem_lt_fresh (ho.2.1.1 hxM)
  have hparent : ∀ x ∈ s.middle.1.carrier.vertices,
      s.middle.1.parent x ∈ s.middle.1.carrier.vertices := by
    have hp := correctedCouplingStage_middle_parent_mem N hN hpq r w (j + n)
    change ∀ x ∈ t.trees.middle.carrier.vertices,
      t.trees.middle.parent x ∈ t.trees.middle.carrier.vertices at hp
    simpa only [hM] using hp
  refine ⟨hemit, ?_, ?_⟩
  · rw [t.word_step, hemit]
    simp only [hW, ↓reduceIte]
  · rw [hstep]
    exact s.middle.1.chronological_update hv hgt hparent _

theorem FiniteCouplingGenealogy.chronological_sourceUpdate
    (s : FiniteCouplingGenealogy)
    (hparent : ∀ x ∈ s.1.carrier.vertices, s.1.parent x ∈ s.1.carrier.vertices)
    (b : Bool) (u : ℝ) :
    (s.update (s.1.totalSelected u) s.1.fresh b).chronological = s.chronological.sourceStep b u := by
  by_cases hA : s.1.carrier.active.Nonempty
  · have hv : s.1.totalSelected u ∈ s.1.carrier.active := by
      simpa [CouplingGenealogy.totalSelected, hA] using s.1.selectedActive_mem hA u
    have hcan : s.chronological.1.carrier.active.Nonempty :=
      hA.image (couplingLabelRank s.1.carrier.vertices)
    have hsel : couplingLabelRank s.1.carrier.vertices (s.1.totalSelected u) =
        selectFinite s.chronological.1.carrier.active hcan u := by
      rw [CouplingGenealogy.totalSelected, dite_eq_left hA]
      exact couplingLabelRank_selectFinite s.1.carrier.vertices s.1.carrier.active hA
        s.1.carrier.active_sub_vertices u
    apply Subtype.ext
    change (s.1.update (s.1.totalSelected u) s.1.fresh b).chronological = _
    rw [s.1.chronological_update hv (fun x hx ↦ s.1.mem_lt_fresh hx) hparent b]
    simp only [FiniteCouplingGenealogy.sourceStep, dite_eq_left hcan, FiniteCouplingGenealogy.update]
    change s.1.chronological.update _ s.1.carrier.vertices.card b =
      s.1.chronological.update (selectFinite s.chronological.1.carrier.active hcan u)
        (Finset.range s.1.carrier.vertices.card).card b
    rw [Finset.card_range, ← hsel]
  · have he := Finset.not_nonempty_iff_eq_empty.mp hA
    have hcan : s.chronological.1.carrier.active = ∅ := by
      change (s.1.carrier.active.image (couplingLabelRank s.1.carrier.vertices)) = ∅
      simp [he]
    rw [FiniteCouplingGenealogy.sourceStep_of_empty _ hcan]
    apply Subtype.ext
    change (s.1.update (s.1.totalSelected u) s.1.fresh b).chronological = s.1.chronological
    rw [s.1.update_eq_self_of_empty he]

theorem CorrectedCouplingState.step_middle_of_bad
    (s : CorrectedCouplingState) (p q : ℝ) (r : List Bool → ℝ)
    (hbad : ¬(s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q)) (u recovery : ℝ) :
    (s.step p q r u recovery).trees.middle =
      s.trees.middle.update (s.trees.middle.totalSelected u) s.trees.middle.fresh
        (recoveryThresholdBirth (r s.word) recovery) := by
  simp [CorrectedCouplingState.step, hbad, CouplingGenealogy.totalSelected]

theorem FiniteCouplingState.direct_middle_source_update
    (s : FiniteCouplingState) (p q : ℝ) (r : List Bool → ℝ)
    (hbad : ¬(s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q))
    (hparent : ∀ x ∈ s.middle.1.carrier.vertices,
      s.middle.1.parent x ∈ s.middle.1.carrier.vertices) (u recovery : ℝ) :
    (s.step p q r u recovery).middle.chronological =
      s.middle.chronological.sourceStep (recoveryThresholdBirth (r s.word) recovery) u := by
  have hval : (s.step p q r u recovery).middle.1 =
      s.middle.1.update (s.middle.1.totalSelected u) s.middle.1.fresh
        (recoveryThresholdBirth (r s.word) recovery) := by
    have he := congrArg (fun t : CorrectedCouplingState ↦ t.trees.middle)
      (s.toState_step p q r u recovery)
    exact he.trans (s.toState.step_middle_of_bad p q r hbad u recovery)
  have hcode : (s.step p q r u recovery).middle =
      s.middle.update (s.middle.1.totalSelected u) s.middle.1.fresh
        (recoveryThresholdBirth (r s.word) recovery) := Subtype.ext hval
  rw [hcode]
  exact s.middle.chronological_sourceUpdate hparent _ u

theorem correctedCouplingStage_middle_eq_of_empty
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    {i j : ℕ} (hij : i ≤ j)
    (hi : (correctedCouplingStage roots p q r w i).trees.middle.carrier.active = ∅) :
    (correctedCouplingStage roots p q r w j).trees.middle =
      (correctedCouplingStage roots p q r w i).trees.middle := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j _ ih =>
      have hj : (correctedCouplingStage roots p q r w j).trees.middle.carrier.active = ∅ := by
        rw [ih]
        exact hi
      exact (CorrectedCouplingState.step_middle_eq_of_empty _ hj p q r (w (0, j)) (w (1, j))).trans ih

end HeightPaper.CountCoupling
