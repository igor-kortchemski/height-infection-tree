module

public import HeightPaper.Probability.CorrectedCouplingUpperProcess

/-!
# First accepted proposal in the actual upper forest

The upper carrier is a countable state: its finite vertex and active sets
determine the uniform proposal mechanism.  The first proposal to hit a fixed
nonempty subset of the initial active set is uniform there, and the recovery
uniform at that physical time remains independent.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace HeightPaper.CountCoupling

instance : Countable CouplingCarrier := by
  have hinj : Function.Injective
      (fun s : CouplingCarrier ↦ (s.vertices, s.active)) := by
    intro a b h
    cases a with
    | mk av aa ah =>
      cases b with
      | mk bv ba bh =>
        cases h
        rfl
  exact hinj.countable

instance : MeasurableSpace CouplingCarrier := ⊤

noncomputable def upperCarrier (roots : Finset ℕ) (p : ℝ)
    (w : (Fin 2 × ℕ) → ℝ) : ℕ → CouplingCarrier
  | 0 => (CouplingGenealogy.initial roots).carrier
  | k + 1 =>
      let s := upperCarrier roots p w k
      if hs : s.active.Nonempty then
        s.update
          (selectFinite s.active hs (w (0, k)))
          (s.vertices.sup id + 1)
          (recoveryThresholdBirth p (w (1, k)))
      else s

theorem upperStage_carrier_eq_upperCarrier
    (roots : Finset ℕ) (p : ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) :
    (upperStage roots p w k).carrier = upperCarrier roots p w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [upperStage_succ, upperCarrier]
      rw [← ih]
      by_cases hs : (upperStage roots p w k).carrier.active.Nonempty
      · simp only [dite_eq_left hs, CouplingGenealogy.update]
        rfl
      · simp only [dite_eq_right hs]

theorem measurable_upperCarrier (roots : Finset ℕ) (p : ℝ)
    (k : ℕ) :
    Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦ upperCarrier roots p w k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      let step : CouplingCarrier × (ℝ × ℝ) → CouplingCarrier :=
        fun z ↦
          if hs : z.1.active.Nonempty then
            z.1.update
              (selectFinite z.1.active hs z.2.1)
              (z.1.vertices.sup id + 1)
              (recoveryThresholdBirth p z.2.2)
          else z.1
      have hstep : Measurable step := by
        apply measurable_from_prod_countable_right
        intro s
        by_cases hs : s.active.Nonempty
        · have hsel : Measurable
            (fun z : ℝ × ℝ ↦ selectFinite s.active hs z.1) :=
            (measurable_selectFinite s.active hs).comp measurable_fst
          have hbirth : Measurable
            (fun z : ℝ × ℝ ↦ recoveryThresholdBirth p z.2) :=
            (measurable_recoveryThresholdBirth p).comp measurable_snd
          have hcode : Measurable
              (fun z : ℝ × ℝ ↦
                (selectFinite s.active hs z.1,
                  recoveryThresholdBirth p z.2)) :=
            hsel.prodMk hbirth
          simpa only [step, dite_eq_left hs, Function.comp_def] using
            (measurable_of_countable
              (fun z : ℕ × Bool ↦
                s.update z.1 (s.vertices.sup id + 1) z.2)).comp hcode
        · simp only [step, dite_eq_right hs]
          exact measurable_const
      have hpair : Measurable
          (fun w : (Fin 2 × ℕ) → ℝ ↦ (w (0, k), w (1, k))) :=
        (measurable_pi_apply (0, k)).prodMk
          (measurable_pi_apply (1, k))
      exact hstep.comp (ih.prodMk hpair)

theorem upperCarrier_congr_prefix
    (roots : Finset ℕ) (p : ℝ) (k : ℕ)
    {w z : (Fin 2 × ℕ) → ℝ}
    (h : ∀ i, i.2 < k → w i = z i) :
    upperCarrier roots p w k = upperCarrier roots p z k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hprev := ih (fun i hi ↦ h i (by omega))
      simp only [upperCarrier, hprev]
      rw [h (0, k) (by simp), h (1, k) (by simp)]

noncomputable def upperPending
    (A roots : Finset ℕ) (hA : A.Nonempty) (p : ℝ)
    (w : (Fin 2 × ℕ) → ℝ) : ℕ → Bool
  | 0 => true
  | k + 1 =>
      upperPending A roots hA p w k &&
        decide
          (selectFinite ((upperCarrier roots p w k).active ∪ A)
            (hA.mono Finset.subset_union_right)
            (w (0, k)) ∉ A)

theorem upperPending_succ_true_iff
    (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) :
    upperPending A roots hA p w (k + 1) = true ↔
      upperPending A roots hA p w k = true ∧
        selectFinite ((upperCarrier roots p w k).active ∪ A)
          (hA.mono Finset.subset_union_right) (w (0, k)) ∉ A := by
  simp [upperPending]

theorem measurable_upperPending
    (A roots : Finset ℕ) (hA : A.Nonempty) (p : ℝ)
    (k : ℕ) :
    Measurable
      (fun w : (Fin 2 × ℕ) → ℝ ↦
        upperPending A roots hA p w k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      have hsel : Measurable
          (fun z : CouplingCarrier × ℝ ↦
            selectFinite (z.1.active ∪ A)
              (hA.mono Finset.subset_union_right) z.2) :=
        measurable_from_prod_countable_right
          (fun s ↦ measurable_selectFinite (s.active ∪ A)
            (hA.mono Finset.subset_union_right))
      have hchosen : Measurable
          (fun w : (Fin 2 × ℕ) → ℝ ↦
            selectFinite ((upperCarrier roots p w k).active ∪ A)
              (hA.mono Finset.subset_union_right) (w (0, k))) :=
        by
          have harg : Measurable
              (fun w : (Fin 2 × ℕ) → ℝ ↦
                (upperCarrier roots p w k, w (0, k))) :=
            (measurable_upperCarrier roots p k).prodMk
              (measurable_pi_apply (0, k))
          simpa only [Function.comp_def] using hsel.comp harg
      have hmiss : Measurable
          (fun w : (Fin 2 × ℕ) → ℝ ↦
            decide (selectFinite ((upperCarrier roots p w k).active ∪ A)
              (hA.mono Finset.subset_union_right) (w (0, k)) ∉ A)) :=
        (measurable_of_countable (fun v : ℕ ↦ decide (v ∉ A))).comp hchosen
      have hjoin : Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦
          upperPending A roots hA p w k &&
            decide (selectFinite ((upperCarrier roots p w k).active ∪ A)
              (hA.mono Finset.subset_union_right) (w (0, k)) ∉ A)) :=
        (measurable_of_countable (fun z : Bool × Bool ↦ z.1 && z.2)).comp
          (ih.prodMk hmiss)
      simpa only [upperPending] using hjoin

theorem upperPending_congr_prefix
    (A roots : Finset ℕ) (hA : A.Nonempty) (p : ℝ) (k : ℕ)
    {w z : (Fin 2 × ℕ) → ℝ}
    (h : ∀ i, i.2 < k → w i = z i) :
    upperPending A roots hA p w k =
      upperPending A roots hA p z k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hprev := ih (fun i hi ↦ h i (by omega))
      simp only [upperPending, hprev,
        upperCarrier_congr_prefix roots p k
          (fun i hi ↦ h i (by omega))]
      rw [h (0, k) (by simp)]

private theorem selectFinite_congr
    {B C : Finset ℕ} (hBC : B = C)
    (hB : B.Nonempty) (hC : C.Nonempty) (u : ℝ) :
    selectFinite B hB u = selectFinite C hC u := by
  subst C
  rfl

/-- While an acceptance is pending, every vertex in the fixed target set
remains active in the upper forest. Rejected proposals cannot freeze a
vertex of that set. -/
theorem upperPending_subset_active
    (A roots : Finset ℕ) (hA : A.Nonempty)
    (hAroots : A ⊆ roots) (p : ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (k : ℕ)
    (hpending : upperPending A roots hA p w k = true) :
    A ⊆ (upperCarrier roots p w k).active := by
  induction k with
  | zero =>
      change A ⊆ roots
      exact hAroots
  | succ k ih =>
      obtain ⟨hprev, hmiss⟩ :=
        (upperPending_succ_true_iff A roots hA p w k).mp hpending
      have hAk := ih hprev
      let s := upperCarrier roots p w k
      have hs : s.active.Nonempty := hA.mono hAk
      have hsame : s.active ∪ A = s.active :=
        Finset.union_eq_left.mpr hAk
      let v := selectFinite s.active hs (w (0, k))
      have hv : v ∈ s.active := selectFinite_mem s.active hs _
      have hselected :
          selectFinite (s.active ∪ A)
            (hA.mono Finset.subset_union_right) (w (0, k)) = v := by
        exact selectFinite_congr hsame _ hs _
      have hnot : v ∉ A := by
        change selectFinite (s.active ∪ A)
          (hA.mono Finset.subset_union_right) (w (0, k)) ∉ A at hmiss
        exact hselected ▸ hmiss
      change A ⊆
        (if hs' : s.active.Nonempty then
          s.update v (s.vertices.sup id + 1)
            (recoveryThresholdBirth p (w (1, k)))
        else s).active
      simp only [dite_eq_left hs]
      cases hb : recoveryThresholdBirth p (w (1, k))
      · simp [CouplingCarrier.update, hv]
        intro x hx
        exact Finset.mem_erase.mpr
          ⟨by intro he; exact hnot (he ▸ hx), hAk hx⟩
      · simp [CouplingCarrier.update, hv]
        exact hAk.trans (Finset.subset_insert _ _)

/-- On a pending rejection segment, totalization by union with `A` is
invisible: the proposal is exactly the upper forest's uniform active
selection. -/
theorem upperPending_selection_eq_upper
    (A roots : Finset ℕ) (hA : A.Nonempty)
    (hAroots : A ⊆ roots) (p : ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (k : ℕ)
    (hk : upperPending A roots hA p w k = true)
    (u : ℝ) :
    selectFinite ((upperCarrier roots p w k).active ∪ A)
      (hA.mono Finset.subset_union_right) u =
    selectFinite (upperCarrier roots p w k).active
      (hA.mono (upperPending_subset_active A roots
        hA hAroots p w k hk)) u := by
  exact selectFinite_congr
    (Finset.union_eq_left.mpr
      (upperPending_subset_active A roots hA hAroots p w k hk))
    _ _ _

/-- For the genuine evolving upper forest, the first proposal that hits a
fixed nonempty active subset is uniform on that subset. Its recovery draw is
an independent uniform even though the proposal set changes after every
rejected birth or recovery. -/
theorem upperStage_first_accepted_joint_law
    (N : ℕ) (hN : 0 < N)
    {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (A : Finset ℕ) (hA : A.Nonempty)
    (hAroots : A ⊆ Finset.range N)
    {v : ℕ} (hv : v ∈ A) (D : Set ℝ)
    (hD : MeasurableSet D) :
    pairedUniformLaw
      (⋃ k : ℕ, {w | upperPending A (Finset.range N) hA p w k = true ∧
        selectFinite
          ((upperCarrier (Finset.range N) p w k).active ∪ A)
          (hA.mono Finset.subset_union_right) (w (0, k)) = v ∧
        w (1, k) ∈ D}) =
      (A.card : ℝ≥0∞)⁻¹ * unitUniform D := by
  let C : ℕ → ((Fin 2 × ℕ) → ℝ) → Finset ℕ × Bool :=
    fun k w ↦
      ((upperCarrier (Finset.range N) p w k).active,
        upperPending A (Finset.range N) hA p w k)
  have hC (k : ℕ) : Measurable (C k) := by
    have hactive : Measurable
        (fun w : (Fin 2 × ℕ) → ℝ ↦
          (upperCarrier (Finset.range N) p w k).active) :=
      (measurable_of_countable (fun s : CouplingCarrier ↦ s.active)).comp
        (measurable_upperCarrier (Finset.range N) p k)
    exact hactive.prodMk
      (measurable_upperPending A (Finset.range N) hA p k)
  have hcausal (k : ℕ) (w z : (Fin 2 × ℕ) → ℝ)
      (h : ∀ i, i.2 < k → w i = z i) :
      C k w = C k z := by
    apply Prod.ext
    · exact congrArg CouplingCarrier.active
        (upperCarrier_congr_prefix (Finset.range N) p k h)
    · exact upperPending_congr_prefix A (Finset.range N) hA p k h
  have hstart (w : (Fin 2 × ℕ) → ℝ) :
      (C 0 w).2 = true := rfl
  have hstep (k : ℕ) (w : (Fin 2 × ℕ) → ℝ) :
      (C (k + 1) w).2 = true ↔
        (C k w).2 = true ∧
          selectFinite ((C k w).1 ∪ A)
            (hA.mono Finset.subset_union_right)
            (w (0, k)) ∉ A :=
    upperPending_succ_true_iff A (Finset.range N) hA p w k
  have hsubset (k : ℕ) (w : (Fin 2 × ℕ) → ℝ)
      (hk : (C k w).2 = true) :
      A ⊆ (C k w).1 :=
    upperPending_subset_active A (Finset.range N)
      hA hAroots p w k hk
  have hext : ∀ᵐ w ∂pairedUniformLaw,
      ∃ k, (C k w).1 = ∅ := by
    filter_upwards [upperStage_ae_eventually_empty N hN hp hp1]
      with w hw
    obtain ⟨k, hk⟩ := hw
    rw [upperStage_carrier_eq_upperCarrier] at hk
    exact ⟨k, hk⟩
  exact paired_causal_first_accepted_label_recovery_probability
    A hA C hC hcausal hstart hstep hsubset hext hv D hD

end HeightPaper.CountCoupling
