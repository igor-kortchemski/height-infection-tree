module

public import HeightPaper.Probability.CorrectedCouplingUpperAcceptance

/-!
# The three-genealogy stochastic recursion

At each physical time the upper and lower genealogies share a uniformly
selected upper active vertex and one recovery uniform.  The middle uses that
selection while the coupling condition holds.  Once it fails, the middle
uses a direct uniform selection from its own active set.  The upper
genealogy is unaffected by this switch and agrees pathwise with the
standalone upper process.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

structure CorrectedCouplingState where
  trees : CouplingTriple
  word : List Bool
  faithful : Bool

def CorrectedCouplingState.initial
    (roots : Finset ℕ) : CorrectedCouplingState :=
  { trees := CouplingTriple.initial roots
    word := []
    faithful := true }

/-- One physical update of the corrected coupling construction.  In the
out-of-bounds branch the middle uses the same fresh parent uniform through
its own active-set rank; no independence between the two parent selections
is needed for either marginal law. -/
noncomputable def CorrectedCouplingState.step
    (s : CorrectedCouplingState)
    (p q : ℝ) (r : List Bool → ℝ)
    (parent recovery : ℝ) : CorrectedCouplingState :=
  let rate := r s.word
  let b := recoveryThresholdBirth rate recovery
  if s.faithful = true ∧ p ≤ rate ∧ rate ≤ q then
    if hu : s.trees.upper.carrier.active.Nonempty then
      let v := s.trees.upper.selectedActive hu parent
      { trees := s.trees.step p q rate recovery v
        word := if v ∈ s.trees.middle.carrier.active then
            s.word ++ [b] else s.word
        faithful := true }
    else
      { trees := s.trees
        word := s.word ++ [b]
        faithful := true }
  else
    let upperV := if hu : s.trees.upper.carrier.active.Nonempty then
      s.trees.upper.selectedActive hu parent else 0
    let middleV := if hm : s.trees.middle.carrier.active.Nonempty then
      s.trees.middle.selectedActive hm parent else 0
    { trees :=
        { lower := s.trees.lower.update upperV s.trees.upper.fresh
            (recoveryThresholdBirth q recovery)
          middle := s.trees.middle.update middleV s.trees.middle.fresh b
          upper := s.trees.upper.update upperV s.trees.upper.fresh
            (recoveryThresholdBirth p recovery) }
      word := s.word ++ [b]
      faithful := false }

noncomputable def correctedCouplingStage
    (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) : ℕ → CorrectedCouplingState
  | 0 => CorrectedCouplingState.initial roots
  | k + 1 =>
      (correctedCouplingStage roots p q r w k).step
        p q r (w (0, k)) (w (1, k))

/-- The upper component ignores the middle's time change and the
out-of-bounds switch. -/
theorem CorrectedCouplingState.step_upper
    (s : CorrectedCouplingState)
    (p q : ℝ) (r : List Bool → ℝ)
    (parent recovery : ℝ) :
    (s.step p q r parent recovery).trees.upper =
      if hu : s.trees.upper.carrier.active.Nonempty then
        s.trees.upper.update
          (s.trees.upper.selectedActive hu parent)
          s.trees.upper.fresh
          (recoveryThresholdBirth p recovery)
      else s.trees.upper := by
  unfold CorrectedCouplingState.step
  by_cases hgood : s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q
  · simp only [hgood]
    by_cases hu : s.trees.upper.carrier.active.Nonempty
    · simp [hu, CouplingTriple.step]
    · simp [hu]
  · simp only [hgood]
    by_cases hu : s.trees.upper.carrier.active.Nonempty
    · simp [hu]
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp hu
      simp [hempty, CouplingGenealogy.update,
        CouplingCarrier.update]

theorem correctedCouplingStage_upper_eq_upperStage
    (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) :
    (correctedCouplingStage roots p q r w k).trees.upper =
      upperStage roots p w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [correctedCouplingStage, CorrectedCouplingState.step_upper]
      rw [ih, upperStage_succ]

private theorem lower_upper_common_update
    (s : CorrectedCouplingState)
    (hlowup : s.trees.lower.LE s.trees.upper)
    {p q : ℝ} (hpq : p ≤ q)
    (v : ℕ) (recovery : ℝ) :
    (s.trees.lower.update v s.trees.upper.fresh
      (recoveryThresholdBirth q recovery)).LE
    (s.trees.upper.update v s.trees.upper.fresh
      (recoveryThresholdBirth p recovery)) := by
  exact CouplingGenealogy.update_mono hlowup v
    s.trees.upper.fresh s.trees.upper.fresh_not_mem
    (fun _ ↦ recoveryThresholdBirth_mono_upper hpq)

/-- The lower genealogy is always included in the upper genealogy, even
after the middle coupling condition fails. -/
theorem CorrectedCouplingState.step_lower_upper
    (s : CorrectedCouplingState)
    (hlowup : s.trees.lower.LE s.trees.upper)
    {p q : ℝ} (hpq : p ≤ q)
    (r : List Bool → ℝ)
    (parent recovery : ℝ) :
    (s.step p q r parent recovery).trees.lower.LE
      (s.step p q r parent recovery).trees.upper := by
  unfold CorrectedCouplingState.step
  by_cases hgood : s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q
  · simp only [hgood]
    by_cases hu : s.trees.upper.carrier.active.Nonempty
    · simp only [hu, dite_eq_left, CouplingTriple.step]
      exact lower_upper_common_update s hlowup hpq
        (s.trees.upper.selectedActive hu parent) recovery
    · simp only [hu]
      exact hlowup
  · simp only [hgood]
    exact lower_upper_common_update s hlowup hpq
      (if hu : s.trees.upper.carrier.active.Nonempty then
        s.trees.upper.selectedActive hu parent else 0)
      recovery

theorem correctedCouplingStage_lower_upper
    (roots : Finset ℕ) {p q : ℝ} (hpq : p ≤ q)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (k : ℕ) :
    (correctedCouplingStage roots p q r w k).trees.lower.LE
      (correctedCouplingStage roots p q r w k).trees.upper := by
  induction k with
  | zero =>
      exact (CouplingTriple.initial_ordered roots).1
  | succ k ih =>
      exact CorrectedCouplingState.step_lower_upper
        _ ih hpq r (w (0, k)) (w (1, k))

/-- While the faithful branch is active, its triple remains ordered.
The bound is read from the branch test at the current word. -/
theorem CorrectedCouplingState.step_faithful_ordered
    (s : CorrectedCouplingState)
    (hs : s.faithful = true → s.trees.Ordered)
    (p q : ℝ) (r : List Bool → ℝ)
    (parent recovery : ℝ) :
    (s.step p q r parent recovery).faithful = true →
      (s.step p q r parent recovery).trees.Ordered := by
  by_cases hgood : s.faithful = true ∧
      p ≤ r s.word ∧ r s.word ≤ q
  · have hord := hs hgood.1
    by_cases hu : s.trees.upper.carrier.active.Nonempty
    · intro _
      simpa [CorrectedCouplingState.step, hgood, hu] using
        (s.trees.step_ordered hord hgood.2.1 hgood.2.2
          (s.trees.upper.selectedActive hu parent))
    · intro _
      simpa [CorrectedCouplingState.step, hgood, hu] using hord
  · simp [CorrectedCouplingState.step, hgood]

theorem correctedCouplingStage_faithful_ordered
    (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (k : ℕ) :
    (correctedCouplingStage roots p q r w k).faithful = true →
      (correctedCouplingStage roots p q r w k).trees.Ordered := by
  induction k with
  | zero =>
      intro _
      exact CouplingTriple.initial_ordered roots
  | succ k ih =>
      exact CorrectedCouplingState.step_faithful_ordered
        _ ih p q r (w (0, k)) (w (1, k))

/-- Empty middle activity is absorbing in both branches of the physical
construction. -/
theorem CorrectedCouplingState.step_middle_empty
    (s : CorrectedCouplingState)
    (hm : s.trees.middle.carrier.active = ∅)
    (p q : ℝ) (r : List Bool → ℝ)
    (parent recovery : ℝ) :
    (s.step p q r parent recovery).trees.middle.carrier.active = ∅ := by
  unfold CorrectedCouplingState.step
  by_cases hgood : s.faithful = true ∧
      p ≤ r s.word ∧ r s.word ≤ q
  · simp only [hgood]
    by_cases hu : s.trees.upper.carrier.active.Nonempty
    · simp [hu, CouplingTriple.step,
        CouplingGenealogy.update, CouplingCarrier.update, hm]
    · simp [hu, hm]
  · simp [hgood, CouplingGenealogy.update,
      CouplingCarrier.update, hm]

/-- If the middle forest is active and every physical step encountered
there satisfies the corrected recovery bound, the construction has never
switched to the out-of-bounds branch. -/
theorem correctedCouplingStage_faithful_of_middle_active
    (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hbound : ∀ k,
      (correctedCouplingStage roots p q r w k).trees.middle.carrier.active.Nonempty →
      p ≤ r (correctedCouplingStage roots p q r w k).word ∧
        r (correctedCouplingStage roots p q r w k).word ≤ q)
    (k : ℕ)
    (hm : (correctedCouplingStage roots p q r w k).trees.middle.carrier.active.Nonempty) :
    (correctedCouplingStage roots p q r w k).faithful = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
      let s := correctedCouplingStage roots p q r w k
      have hmPrev : s.trees.middle.carrier.active.Nonempty := by
        by_contra hnot
        have hempty := Finset.not_nonempty_iff_eq_empty.mp hnot
        have hnext := s.step_middle_empty hempty p q r
          (w (0, k)) (w (1, k))
        have hnextEq :
            (correctedCouplingStage roots p q r w (k + 1)).trees.middle.carrier.active = ∅ := by
          simpa only [correctedCouplingStage] using hnext
        exact (Finset.not_nonempty_iff_eq_empty.mpr hnextEq) hm
      have hfaith := ih hmPrev
      have hrate := hbound k hmPrev
      have hgood : s.faithful = true ∧
          p ≤ r s.word ∧ r s.word ≤ q :=
        ⟨hfaith, hrate⟩
      change (s.step p q r (w (0, k)) (w (1, k))).faithful = true
      simp only [CorrectedCouplingState.step, hgood]
      by_cases hu : s.trees.upper.carrier.active.Nonempty <;> simp [hu]

private theorem genealogy_le_updated_upper_of_empty
    {a b : CouplingGenealogy}
    (hab : a.LE b)
    (ha : a.carrier.active = ∅)
    (v fresh : ℕ) (hfresh : fresh ∉ b.carrier.vertices)
    (birth : Bool) :
    a.LE (b.update v fresh birth) := by
  have hmono := CouplingGenealogy.update_mono hab v fresh hfresh
    (birthA := false) (birthB := birth) (by
      intro hv _
      simp [ha] at hv)
  simpa [CouplingGenealogy.update, CouplingCarrier.update, ha]
    using hmono

/-- Once the middle active set is empty, both smaller active sets stay
empty. The upper genealogy may continue but cannot break the forest
sandwich. -/
theorem CorrectedCouplingState.step_ordered_of_middle_empty
    (s : CorrectedCouplingState)
    (hs : s.trees.Ordered)
    (hm : s.trees.middle.carrier.active = ∅)
    (p q : ℝ)
    (r : List Bool → ℝ)
    (parent recovery : ℝ) :
    (s.step p q r parent recovery).trees.Ordered := by
  have hlower : s.trees.lower.carrier.active = ∅ := by
    have hsubset := hs.1.1.2
    rw [hm] at hsubset
    exact Finset.subset_empty.mp hsubset
  by_cases hgood : s.faithful = true ∧
      p ≤ r s.word ∧ r s.word ≤ q
  · by_cases hu : s.trees.upper.carrier.active.Nonempty
    · have hnew := s.trees.step_ordered_of_middle_active
        (p := p) (q := q) (r := r s.word) (u := recovery) hs
        (fun h ↦ False.elim (by simp [hm] at h))
        (s.trees.upper.selectedActive hu parent)
      simpa [CorrectedCouplingState.step, hgood, hu] using hnew
    · simpa [CorrectedCouplingState.step, hgood, hu] using hs
  · let v := if hu : s.trees.upper.carrier.active.Nonempty then
        s.trees.upper.selectedActive hu parent else 0
    have hupper : s.trees.middle.LE
        (s.trees.upper.update v s.trees.upper.fresh
          (recoveryThresholdBirth p recovery)) :=
      genealogy_le_updated_upper_of_empty hs.2 hm v
        s.trees.upper.fresh s.trees.upper.fresh_not_mem
        (recoveryThresholdBirth p recovery)
    have hlowEq : s.trees.lower.update v s.trees.upper.fresh
        (recoveryThresholdBirth q recovery) = s.trees.lower := by
      simp [CouplingGenealogy.update, CouplingCarrier.update, hlower]
    have hmidEq : s.trees.middle.update
        (if hv : s.trees.middle.carrier.active.Nonempty then
          s.trees.middle.selectedActive hv parent else 0)
        s.trees.middle.fresh
        (recoveryThresholdBirth (r s.word) recovery) =
        s.trees.middle := by
      simp [CouplingGenealogy.update, CouplingCarrier.update, hm]
    simpa [CorrectedCouplingState.step, hgood, hlowEq,
      hmidEq, v, CouplingTriple.Ordered] using
      (show s.trees.lower.LE s.trees.middle ∧
        s.trees.middle.LE
          (s.trees.upper.update v s.trees.upper.fresh
            (recoveryThresholdBirth p recovery))
      from ⟨hs.1, hupper⟩)

/-- The actual three-genealogy recursion preserves componentwise tree and
active-set inclusion at every physical time whenever the corrected bounds
hold at each physical step with nonempty middle activity. -/
theorem correctedCouplingStage_ordered_of_active_bounds
    (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hbound : ∀ k,
      (correctedCouplingStage roots p q r w k).trees.middle.carrier.active.Nonempty →
      p ≤ r (correctedCouplingStage roots p q r w k).word ∧
        r (correctedCouplingStage roots p q r w k).word ≤ q)
    (k : ℕ) :
    (correctedCouplingStage roots p q r w k).trees.Ordered := by
  induction k with
  | zero => exact CouplingTriple.initial_ordered roots
  | succ k ih =>
      let s := correctedCouplingStage roots p q r w k
      by_cases hm : s.trees.middle.carrier.active.Nonempty
      · have hfaith :=
          correctedCouplingStage_faithful_of_middle_active
            roots p q r w hbound k hm
        have hrate := hbound k hm
        have hgood : s.faithful = true ∧
            p ≤ r s.word ∧ r s.word ≤ q :=
          ⟨hfaith, hrate⟩
        have hu : s.trees.upper.carrier.active.Nonempty :=
          hm.mono ih.2.1.2
        have hnew := s.trees.step_ordered
          (r := r s.word) (u := w (1, k)) ih
          hrate.1 hrate.2
          (s.trees.upper.selectedActive hu (w (0, k)))
        change (s.step p q r (w (0, k)) (w (1, k))).trees.Ordered
        simpa [CorrectedCouplingState.step, hgood, hu] using hnew
      · have hempty := Finset.not_nonempty_iff_eq_empty.mp hm
        exact s.step_ordered_of_middle_empty ih hempty p q r
          (w (0, k)) (w (1, k))

/-- Each physical update preserves finite rooted-forest validity. -/
theorem CorrectedCouplingState.step_valid
    (s : CorrectedCouplingState)
    {roots : Finset ℕ}
    (hvalid : s.trees.Valid roots)
    (hlowup : s.trees.lower.LE s.trees.upper)
    (hfaith : s.faithful = true → s.trees.Ordered)
    (p q : ℝ) (r : List Bool → ℝ)
    (parent recovery : ℝ) :
    (s.step p q r parent recovery).trees.Valid roots := by
  by_cases hgood : s.faithful = true ∧
      p ≤ r s.word ∧ r s.word ≤ q
  · by_cases hu : s.trees.upper.carrier.active.Nonempty
    · have hnew := s.trees.step_valid
        (hfaith hgood.1) hvalid p q (r s.word) recovery
        (s.trees.upper.selectedActive hu parent)
      simpa [CorrectedCouplingState.step, hgood, hu] using hnew
    · simpa [CorrectedCouplingState.step, hgood, hu] using hvalid
  · let upperV := if hu : s.trees.upper.carrier.active.Nonempty then
        s.trees.upper.selectedActive hu parent else 0
    let middleV := if hm : s.trees.middle.carrier.active.Nonempty then
        s.trees.middle.selectedActive hm parent else 0
    have hgtLower :
        ∀ x ∈ s.trees.lower.carrier.vertices, x < s.trees.upper.fresh := by
      intro x hx
      exact s.trees.upper.mem_lt_fresh (hlowup.1.1 hx)
    have hl := s.trees.lower.valid_update hvalid.1
      upperV s.trees.upper.fresh hgtLower
      (recoveryThresholdBirth q recovery)
    have hm := s.trees.middle.valid_update hvalid.2.1
      middleV s.trees.middle.fresh
      (fun x hx ↦ s.trees.middle.mem_lt_fresh hx)
      (recoveryThresholdBirth (r s.word) recovery)
    have hu := s.trees.upper.valid_update hvalid.2.2
      upperV s.trees.upper.fresh
      (fun x hx ↦ s.trees.upper.mem_lt_fresh hx)
      (recoveryThresholdBirth p recovery)
    simpa [CorrectedCouplingState.step, hgood, upperV, middleV,
      CouplingTriple.Valid]
      using (show
        (s.trees.lower.update upperV s.trees.upper.fresh
          (recoveryThresholdBirth q recovery)).Valid roots ∧
        (s.trees.middle.update middleV s.trees.middle.fresh
          (recoveryThresholdBirth (r s.word) recovery)).Valid roots ∧
        (s.trees.upper.update upperV s.trees.upper.fresh
          (recoveryThresholdBirth p recovery)).Valid roots
        from ⟨hl, hm, hu⟩)

theorem correctedCouplingStage_valid
    (roots : Finset ℕ) {p q : ℝ} (hpq : p ≤ q)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (k : ℕ) :
    (correctedCouplingStage roots p q r w k).trees.Valid roots := by
  induction k with
  | zero => exact CouplingTriple.initial_valid roots
  | succ k ih =>
      exact CorrectedCouplingState.step_valid _ ih
        (correctedCouplingStage_lower_upper roots hpq r w k)
        (correctedCouplingStage_faithful_ordered roots p q r w k)
        p q r (w (0, k)) (w (1, k))

/-- Almost-sure upper extinction transfers unchanged to the full
three-genealogy recursion. -/
theorem correctedCouplingStage_upper_ae_eventually_empty
    (N : ℕ) (hN : 0 < N)
    {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (q : ℝ) (r : List Bool → ℝ) :
    ∀ᵐ w ∂pairedUniformLaw, ∃ k,
      (correctedCouplingStage (Finset.range N) p q r w k).trees.upper.carrier.active = ∅ := by
  filter_upwards [upperStage_ae_eventually_empty N hN hp hp1]
    with w hw
  obtain ⟨k, hk⟩ := hw
  exact ⟨k, by
    rw [correctedCouplingStage_upper_eq_upperStage]
    exact hk⟩

end HeightPaper.CountCoupling
