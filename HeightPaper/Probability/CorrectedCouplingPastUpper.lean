module

public import HeightPaper.Probability.CorrectedCouplingPastAcceptance
public import HeightPaper.Probability.CorrectedCouplingConstruction
public import HeightPaper.Probability.CorrectedCouplingFiniteState

/-!
# Upper rejection starting on an arbitrary causal past event

The target active set need not consist of initial roots. It can be fixed by
an arbitrary history at a deterministic physical time; partitioning by that
time and state supplies the random-history application.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace HeightPaper.CountCoupling

theorem coded_first_acceptance_cover_on_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Finset ℕ) (hA : A.Nonempty)
    (C : ℕ → Ω → Finset ℕ × Bool) (U : ℕ → Ω → ℝ) (H : Set Ω)
    (hstart : ∀ ω, (C 0 ω).2 = true ↔ ω ∈ H)
    (hstep : ∀ k ω, (C (k + 1) ω).2 = true ↔
      (C k ω).2 = true ∧ selectFinite ((C k ω).1 ∪ A)
        (hA.mono Finset.subset_union_right) (U k ω) ∉ A)
    (hsubset : ∀ k ω, (C k ω).2 = true → A ⊆ (C k ω).1)
    (hext : ∀ᵐ ω ∂μ, ∃ k, (C k ω).1 = ∅) :
    μ (⋃ k, {ω | (C k ω).2 = true ∧ selectFinite ((C k ω).1 ∪ A)
      (hA.mono Finset.subset_union_right) (U k ω) ∈ A}) = μ H := by
  have hback (k : ℕ) (ω : Ω) : (C k ω).2 = true → (C 0 ω).2 = true := by
    induction k with
    | zero => exact id
    | succ k ih => exact fun h ↦ ih ((hstep k ω).mp h).1
  apply measure_congr
  filter_upwards [hext] with ω hω
  apply propext
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk, _⟩
    exact (hstart ω).mp (hback k ω hk)
  · intro hH
    exact first_acceptance_before_upper_empty A hA (fun k ↦ C k ω) (fun k ↦ U k ω)
      ((hstart ω).mpr hH) (fun k ↦ hstep k ω) (fun k ↦ hsubset k ω) hω

noncomputable def upperPastPending (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (j₀ : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ))
    (w : (Fin 2 × ℕ) → ℝ) : ℕ → Bool
  | 0 => by classical exact decide (w ∈ H)
  | n + 1 => upperPastPending A roots hA p j₀ H w n &&
      decide (selectFinite ((upperCarrier roots p w (j₀ + n)).active ∪ A)
        (hA.mono Finset.subset_union_right) (w (0, j₀ + n)) ∉ A)

theorem upperPastPending_start (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (j₀ : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ)) (w : (Fin 2 × ℕ) → ℝ) :
    upperPastPending A roots hA p j₀ H w 0 = true ↔ w ∈ H := by
  classical
  simp [upperPastPending]

theorem upperPastPending_succ (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (j₀ : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ)) (w : (Fin 2 × ℕ) → ℝ) (n : ℕ) :
    upperPastPending A roots hA p j₀ H w (n + 1) = true ↔
      upperPastPending A roots hA p j₀ H w n = true ∧
        selectFinite ((upperCarrier roots p w (j₀ + n)).active ∪ A)
          (hA.mono Finset.subset_union_right) (w (0, j₀ + n)) ∉ A := by
  simp [upperPastPending]

theorem measurable_upperPastPending (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (j₀ : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ)) (hH : MeasurableSet H) (n : ℕ) :
    Measurable (fun w ↦ upperPastPending A roots hA p j₀ H w n) := by
  classical
  induction n with
  | zero =>
      apply measurable_to_bool
      convert hH using 1
      ext w
      simp [upperPastPending]
  | succ n ih =>
      have hsel : Measurable (fun z : CouplingCarrier × ℝ ↦
          selectFinite (z.1.active ∪ A) (hA.mono Finset.subset_union_right) z.2) :=
        measurable_from_prod_countable_right (fun s ↦
          measurable_selectFinite (s.active ∪ A) (hA.mono Finset.subset_union_right))
      have harg := (measurable_upperCarrier roots p (j₀ + n)).prodMk
        (measurable_pi_apply (0, j₀ + n))
      have hmiss := (measurable_of_countable (fun v : ℕ ↦ decide (v ∉ A))).comp
        (hsel.comp harg)
      exact (measurable_of_countable (fun z : Bool × Bool ↦ z.1 && z.2)).comp
        (ih.prodMk hmiss)

theorem upperPastPending_congr_prefix (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (j₀ : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ))
    (hH : ∀ w z, (∀ i, i.2 < j₀ → w i = z i) → (w ∈ H ↔ z ∈ H))
    (n : ℕ) {w z : (Fin 2 × ℕ) → ℝ}
    (h : ∀ i, i.2 < j₀ + n → w i = z i) :
    upperPastPending A roots hA p j₀ H w n = upperPastPending A roots hA p j₀ H z n := by
  classical
  induction n with
  | zero =>
      simp only [upperPastPending, propext (hH w z (fun i hi ↦ h i (by simpa using hi)))]
  | succ n ih =>
      have hprev := ih (fun i hi ↦ h i (by omega))
      have hcar := upperCarrier_congr_prefix roots p (j₀ + n)
        (fun i hi ↦ h i (by omega))
      simp only [upperPastPending, hprev, hcar]
      rw [h (0, j₀ + n) (by simp)]

theorem upperPastPending_subset_active (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (j₀ : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ))
    (hinit : ∀ w ∈ H, A ⊆ (upperCarrier roots p w j₀).active)
    (w : (Fin 2 × ℕ) → ℝ) (n : ℕ)
    (hn : upperPastPending A roots hA p j₀ H w n = true) :
    A ⊆ (upperCarrier roots p w (j₀ + n)).active := by
  induction n with
  | zero => simpa using hinit w ((upperPastPending_start A roots hA p j₀ H w).mp hn)
  | succ n ih =>
      obtain ⟨hprev, hmiss⟩ := (upperPastPending_succ A roots hA p j₀ H w n).mp hn
      have hAk := ih hprev
      let s := upperCarrier roots p w (j₀ + n)
      have hs : s.active.Nonempty := hA.mono hAk
      have hsame : s.active ∪ A = s.active := Finset.union_eq_left.mpr hAk
      let v := selectFinite s.active hs (w (0, j₀ + n))
      have hv : v ∈ s.active := selectFinite_mem s.active hs _
      have hselected : selectFinite (s.active ∪ A)
          (hA.mono Finset.subset_union_right) (w (0, j₀ + n)) = v := by
        simp only [hsame]
        rfl
      have hnot : v ∉ A := by
        change selectFinite (s.active ∪ A)
          (hA.mono Finset.subset_union_right) (w (0, j₀ + n)) ∉ A at hmiss
        exact hselected ▸ hmiss
      rw [Nat.add_succ, upperCarrier]
      change A ⊆ (if _ : s.active.Nonempty then
        s.update v (s.vertices.sup id + 1) (recoveryThresholdBirth p (w (1, j₀ + n)))
        else s).active
      simp only [dite_eq_left hs]
      cases hb : recoveryThresholdBirth p (w (1, j₀ + n))
      · simp [CouplingCarrier.update, hv]
        intro x hx
        exact Finset.mem_erase.mpr ⟨fun he ↦ hnot (he ▸ hx), hAk hx⟩
      · simp [CouplingCarrier.update, hv]
        exact hAk.trans (Finset.subset_insert _ _)

theorem upperCarrier_empty_of_le (roots : Finset ℕ) (p : ℝ)
    (w : (Fin 2 × ℕ) → ℝ) {i j : ℕ} (hij : i ≤ j)
    (hi : (upperCarrier roots p w i).active = ∅) :
    (upperCarrier roots p w j).active = ∅ := by
  induction j, hij using Nat.le_induction with
  | base => exact hi
  | succ j _ ih => simp [upperCarrier, ih]

theorem upperPastPending_selection_eq_upper (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (j₀ : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ))
    (hinit : ∀ w ∈ H, A ⊆ (upperCarrier roots p w j₀).active)
    (w : (Fin 2 × ℕ) → ℝ) (n : ℕ)
    (hn : upperPastPending A roots hA p j₀ H w n = true) :
    selectFinite ((upperCarrier roots p w (j₀ + n)).active ∪ A)
        (hA.mono Finset.subset_union_right) (w (0, j₀ + n)) =
      selectFinite (upperCarrier roots p w (j₀ + n)).active
        (hA.mono (upperPastPending_subset_active A roots hA p j₀ H hinit w n hn))
        (w (0, j₀ + n)) := by
  have hs := upperPastPending_subset_active A roots hA p j₀ H hinit w n hn
  simp only [Finset.union_eq_left.mpr hs]

/-- Uniform accepted label and independent recovery draw after any measurable
causal past event fixing a nonempty subset of the current upper active set. -/
theorem upperPast_first_accepted_joint_law
    (N : ℕ) (hN : 0 < N) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (j₀ : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ)) (hH : MeasurableSet H)
    (hcausal : ∀ w z, (∀ i, i.2 < j₀ → w i = z i) → (w ∈ H ↔ z ∈ H))
    (A : Finset ℕ) (hA : A.Nonempty)
    (hinit : ∀ w ∈ H, A ⊆ (upperCarrier (Finset.range N) p w j₀).active)
    {v : ℕ} (hv : v ∈ A) (D : Set ℝ) (hD : MeasurableSet D) :
    pairedUniformLaw (⋃ n, {w | upperPastPending A (Finset.range N) hA p j₀ H w n = true ∧
      selectFinite ((upperCarrier (Finset.range N) p w (j₀ + n)).active ∪ A)
        (hA.mono Finset.subset_union_right) (w (0, j₀ + n)) = v ∧ w (1, j₀ + n) ∈ D}) =
      (A.card : ℝ≥0∞)⁻¹ * pairedUniformLaw H * unitUniform D := by
  let roots := Finset.range N
  let C : ℕ → ((Fin 2 × ℕ) → ℝ) → Finset ℕ × Bool := fun n w ↦
    ((upperCarrier roots p w (j₀ + n)).active, upperPastPending A roots hA p j₀ H w n)
  let U : ℕ → ((Fin 2 × ℕ) → ℝ) → ℝ := fun n w ↦ w (0, j₀ + n)
  let R : ℕ → ((Fin 2 × ℕ) → ℝ) → ℝ := fun n w ↦ w (1, j₀ + n)
  have hC (n : ℕ) : Measurable (C n) :=
    ((measurable_of_countable CouplingCarrier.active).comp
      (measurable_upperCarrier roots p (j₀ + n))).prodMk
        (measurable_upperPastPending A roots hA p j₀ H hH n)
  have hprefix (n : ℕ) (w z : (Fin 2 × ℕ) → ℝ)
      (h : ∀ i, i.2 < j₀ + n → w i = z i) : C n w = C n z := by
    dsimp only [C]
    rw [upperCarrier_congr_prefix roots p (j₀ + n) h,
      upperPastPending_congr_prefix A roots hA p j₀ H hcausal n h]
  have hstep (n : ℕ) (w : (Fin 2 × ℕ) → ℝ) :
      (C (n + 1) w).2 = true ↔ (C n w).2 = true ∧
      selectFinite ((C n w).1 ∪ A) (hA.mono Finset.subset_union_right) (U n w) ∉ A :=
    upperPastPending_succ A roots hA p j₀ H w n
  have hsubset (n : ℕ) (w : (Fin 2 × ℕ) → ℝ) :
      (C n w).2 = true → A ⊆ (C n w).1 :=
    upperPastPending_subset_active A roots hA p j₀ H hinit w n
  have hext : ∀ᵐ w ∂pairedUniformLaw, ∃ n, (C n w).1 = ∅ := by
    filter_upwards [upperStage_ae_eventually_empty N hN hp hp1] with w hw
    obtain ⟨i, hi⟩ := hw
    have hic : (upperCarrier roots p w i).active = ∅ := by
      rw [← upperStage_carrier_eq_upperCarrier]
      exact hi
    exact ⟨i, upperCarrier_empty_of_le roots p w (Nat.le_add_left i j₀) hic⟩
  have hcover := coded_first_acceptance_cover_on_event pairedUniformLaw A hA C U H
    (fun w ↦ upperPastPending_start A roots hA p j₀ H w) hstep hsubset hext
  exact coded_first_accepted_joint_probability_of_cover pairedUniformLaw A hA C U R hC
    (fun n ↦ measurable_pi_apply (0, j₀ + n)) (fun n ↦ measurable_pi_apply (1, j₀ + n))
    (fun n ↦ causal_state_indep_parent (j₀ + n) (C n) (hC n) (hprefix n))
    (fun n ↦ causal_state_parent_indep_recovery (j₀ + n) (C n) (hC n) (hprefix n))
    (fun n ↦ pairedUniformLaw_map_eval (0, j₀ + n))
    (fun n ↦ pairedUniformLaw_map_eval (1, j₀ + n))
    (coded_first_acceptance_pairwise A hA C U hstep) H hcover hv D hD

/-- The past-event assumptions are supplied automatically by an atom of the
actual finite coupled state at a fixed physical time. -/
theorem upperPast_first_accepted_on_stage
    (N : ℕ) (hN : 0 < N) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (q : ℝ) (r : List Bool → ℝ) (j₀ : ℕ) (s : FiniteCouplingState)
    (A : Finset ℕ) (hA : A.Nonempty) (hAs : A ⊆ s.upper.1.carrier.active)
    {v : ℕ} (hv : v ∈ A) (D : Set ℝ) (hD : MeasurableSet D) :
    let H := {w | finiteCouplingStage (Finset.range N) p q r w j₀ = s}
    pairedUniformLaw (⋃ n, {w | upperPastPending A (Finset.range N) hA p j₀ H w n = true ∧
      selectFinite ((upperCarrier (Finset.range N) p w (j₀ + n)).active ∪ A)
        (hA.mono Finset.subset_union_right) (w (0, j₀ + n)) = v ∧ w (1, j₀ + n) ∈ D}) =
      (A.card : ℝ≥0∞)⁻¹ * pairedUniformLaw H * unitUniform D := by
  let roots := Finset.range N
  let H := {w | finiteCouplingStage roots p q r w j₀ = s}
  have hH : MeasurableSet H :=
    (measurable_finiteCouplingStage roots p q r j₀) (measurableSet_singleton s)
  have hcausal (w z : (Fin 2 × ℕ) → ℝ)
      (h : ∀ i, i.2 < j₀ → w i = z i) : w ∈ H ↔ z ∈ H := by
    change finiteCouplingStage roots p q r w j₀ = s ↔ finiteCouplingStage roots p q r z j₀ = s
    rw [finiteCouplingStage_congr_prefix roots p q r j₀ h]
  have hinit (w : (Fin 2 × ℕ) → ℝ) (hw : w ∈ H) :
      A ⊆ (upperCarrier roots p w j₀).active := by
    have he : (finiteCouplingStage roots p q r w j₀).upper.1.carrier.active =
        (upperCarrier roots p w j₀).active := by
      calc
        _ = (correctedCouplingStage roots p q r w j₀).trees.upper.carrier.active :=
          congrArg (fun t : CorrectedCouplingState ↦ t.trees.upper.carrier.active)
            (finiteCouplingStage_toState roots p q r w j₀)
        _ = (upperStage roots p w j₀).carrier.active := by
          rw [correctedCouplingStage_upper_eq_upperStage]
        _ = _ := congrArg CouplingCarrier.active (upperStage_carrier_eq_upperCarrier roots p w j₀)
    rw [← he, hw]
    exact hAs
  exact upperPast_first_accepted_joint_law N hN hp hp1 j₀ H hH hcausal A hA hinit hv D hD

end HeightPaper.CountCoupling
