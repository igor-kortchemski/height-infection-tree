module

public import HeightPaper.Probability.CorrectedCouplingLogicalToken

/-!
# The actual middle token after a faithful rejection interval

The accepted-pair law is transported to the measurable logical token, with
all waiting and coverage obligations discharged for the concrete process.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace HeightPaper.CountCoupling

noncomputable def upperPastSelection (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (j n : ℕ) (w : (Fin 2 × ℕ) → ℝ) : ℕ :=
  selectFinite ((upperCarrier roots p w (j + n)).active ∪ A)
    (hA.mono Finset.subset_union_right) (w (0, j + n))

noncomputable def upperPastAccept (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (j : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ)) (n : ℕ) :
    Set ((Fin 2 × ℕ) → ℝ) :=
  {w | upperPastPending A roots hA p j H w n = true ∧
    upperPastSelection A roots hA p j n w ∈ A}

theorem measurable_upperPastSelection (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (j n : ℕ) : Measurable (upperPastSelection A roots hA p j n) := by
  have hsel : Measurable (fun z : CouplingCarrier × ℝ ↦
      selectFinite (z.1.active ∪ A) (hA.mono Finset.subset_union_right) z.2) :=
    measurable_from_prod_countable_right (fun s ↦
      measurable_selectFinite (s.active ∪ A) (hA.mono Finset.subset_union_right))
  have harg : Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦
      (upperCarrier roots p w (j + n), w (0, j + n))) :=
    (measurable_upperCarrier roots p (j + n)).prodMk (measurable_pi_apply (0, j + n))
  change Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦
    selectFinite ((upperCarrier roots p w (j + n)).active ∪ A)
      (hA.mono Finset.subset_union_right) (w (0, j + n)))
  simpa only [Function.comp_def] using hsel.comp harg

theorem measurableSet_upperPastAccept (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (j : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ)) (hH : MeasurableSet H) (n : ℕ) :
    MeasurableSet (upperPastAccept A roots hA p j H n) :=
  ((measurable_upperPastPending A roots hA p j H hH n) (measurableSet_singleton true)).inter
    ((measurable_upperPastSelection A roots hA p j n) A.measurableSet)

theorem upperPastAccept_pairwise (A roots : Finset ℕ) (hA : A.Nonempty)
    (p : ℝ) (j : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ)) :
    Pairwise (Disjoint on upperPastAccept A roots hA p j H) :=
  coded_first_acceptance_pairwise A hA
    (fun n w ↦ ((upperCarrier roots p w (j + n)).active,
      upperPastPending A roots hA p j H w n)) (fun n w ↦ w (0, j + n))
    (fun n w ↦ upperPastPending_succ A roots hA p j H w n)

theorem upperPastAccept_ae_cover
    (N : ℕ) (hN : 0 < N) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (A : Finset ℕ) (hA : A.Nonempty) (j : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ))
    (hinit : ∀ w ∈ H, A ⊆ (upperCarrier (Finset.range N) p w j).active) :
    (⋃ n, upperPastAccept A (Finset.range N) hA p j H n) =ᵐ[pairedUniformLaw] H := by
  filter_upwards [upperStage_ae_eventually_empty N hN hp hp1] with w hw
  apply propext
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨n, hn⟩
    exact upperPastPending_event A (Finset.range N) hA p j H w n hn.1
  · intro hH
    have hext : ∃ n, (upperCarrier (Finset.range N) p w (j + n)).active = ∅ := by
      obtain ⟨i, hi⟩ := hw
      have hi' : (upperCarrier (Finset.range N) p w i).active = ∅ := by
        rw [← upperStage_carrier_eq_upperCarrier]
        exact hi
      exact ⟨i, upperCarrier_empty_of_le _ p w (Nat.le_add_left i j) hi'⟩
    exact first_acceptance_before_upper_empty A hA
      (fun n ↦ ((upperCarrier (Finset.range N) p w (j + n)).active,
        upperPastPending A (Finset.range N) hA p j H w n))
      (fun n ↦ w (0, j + n))
      ((upperPastPending_start A (Finset.range N) hA p j H w).mpr hH)
      (fun n ↦ upperPastPending_succ A (Finset.range N) hA p j H w n)
      (fun n ↦ upperPastPending_subset_active A (Finset.range N) hA p j H hinit w n) hext

theorem correctedCouplingLogicalToken_on_upperPastAccept
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ) (j : ℕ)
    (H : Set ((Fin 2 × ℕ) → ℝ)) (s : FiniteCouplingState)
    (hfix : ∀ w ∈ H, finiteCouplingStage (Finset.range N) p q r w j = s)
    (hfaith : s.faithful = true) (hrate : p ≤ r s.word ∧ r s.word ≤ q)
    (hA : s.middle.1.carrier.active.Nonempty)
    (hparent : ∀ x ∈ s.middle.1.carrier.vertices,
      s.middle.1.parent x ∈ s.middle.1.carrier.vertices)
    (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ k, ∃ i, k < correctedCouplingClock (Finset.range N) p q r w i)
    (n : ℕ) (hn : w ∈ upperPastAccept s.middle.1.carrier.active (Finset.range N) hA p j H n) :
    correctedCouplingLogicalToken N p q r w s.word.length =
      acceptedMiddleToken s.middle (r s.word)
        (upperPastSelection s.middle.1.carrier.active (Finset.range N) hA p j n w,
          w (1, j + n)) := by
  let v := upperPastSelection s.middle.1.carrier.active (Finset.range N) hA p j n w
  have hreal (z : (Fin 2 × ℕ) → ℝ) (hz : z ∈ H) :
      correctedCouplingStage (Finset.range N) p q r z j = s.toState := by
    rw [← finiteCouplingStage_toState, hfix z hz]
  obtain ⟨hM, hW, _⟩ := middle_state_while_upper_pending (Finset.range N) p q r j H s
    hreal hfaith hrate hA w n hn.1
  have he := middle_update_at_upper_acceptance N hN hpq r j H s hreal hfaith hrate hA
    w n hn.1 v hn.2 rfl
  have hforest : (finiteCouplingStage (Finset.range N) p q r w (j + n + 1)).middle.chronological =
      (s.middle.update v s.middle.1.fresh
        (recoveryThresholdBirth (r s.word) (w (1, j + n)))).chronological := by
    apply Subtype.ext
    calc
      _ = (correctedCouplingStage (Finset.range N) p q r w (j + n + 1)).trees.middle.chronological :=
        congrArg (fun t : CorrectedCouplingState ↦ t.trees.middle.chronological)
          (finiteCouplingStage_toState (Finset.range N) p q r w (j + n + 1))
      _ = _ := he.2.2
      _ = _ := (s.middle.1.chronological_update hn.2
        (fun x hx ↦ s.middle.1.mem_lt_fresh hx) hparent _).symm
  have hc : correctedCouplingClock (Finset.range N) p q r w (j + n) = s.word.length :=
    congrArg List.length hW
  rw [← hc, correctedCouplingLogicalToken_at_emission N p q r w hunbounded (j + n) he.1,
    hW, hforest]
  rfl

theorem faithful_middle_logical_kernel_on_event
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hp1 : p ≤ 1)
    (r : List Bool → ℝ) (j : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ)) (hH : MeasurableSet H)
    (hcausal : ∀ w z, (∀ i, i.2 < j → w i = z i) → (w ∈ H ↔ z ∈ H))
    (s : FiniteCouplingState)
    (hfix : ∀ w ∈ H, finiteCouplingStage (Finset.range N) p q r w j = s)
    (hfaith : s.faithful = true) (hrate : p ≤ r s.word ∧ r s.word ≤ q)
    (hA : s.middle.1.carrier.active.Nonempty)
    (hparent : ∀ x ∈ s.middle.1.carrier.vertices,
      s.middle.1.parent x ∈ s.middle.1.carrier.vertices) :
    (pairedUniformLaw.restrict H).map (fun w ↦ correctedCouplingLogicalToken N p q r w s.word.length) =
      pairedUniformLaw H • sourceMiddleTokenLaw s.middle.chronological (r s.word) := by
  let A := s.middle.1.carrier.active
  let roots := Finset.range N
  let V := upperPastSelection A roots hA p j
  let E := upperPastAccept A roots hA p j H
  let R : ℕ → ((Fin 2 × ℕ) → ℝ) → ℝ := fun n w ↦ w (1, j + n)
  let F := acceptedMiddleToken s.middle (r s.word)
  have hF : Measurable F := measurable_acceptedMiddleToken _ _
  have hreal (w : (Fin 2 × ℕ) → ℝ) (hw : w ∈ H) :
      correctedCouplingStage roots p q r w j = s.toState := by
    rw [← finiteCouplingStage_toState, hfix w hw]
  have hinit := faithful_middle_subset_upper_on_event roots p q r j H s hreal hfaith
  have hE (n : ℕ) : MeasurableSet (E n) := measurableSet_upperPastAccept A roots hA p j H hH n
  have hpair (n : ℕ) : Measurable (fun w ↦ (V n w, R n w)) :=
    (measurable_upperPastSelection A roots hA p j n).prodMk (measurable_pi_apply (1, j + n))
  calc
    _ = Measure.sum (fun n ↦ (pairedUniformLaw.restrict (E n)).map
        (fun w ↦ correctedCouplingLogicalToken N p q r w s.word.length)) :=
      map_restrict_eq_sum_of_ae_partition pairedUniformLaw H E hE
        (upperPastAccept_pairwise A roots hA p j H)
        (upperPastAccept_ae_cover N hN hp hp1 A hA j H hinit)
        _ (measurable_correctedCouplingLogicalToken N p q r _)
    _ = Measure.sum (fun n ↦ (pairedUniformLaw.restrict (E n)).map
        (F ∘ fun w ↦ (V n w, R n w))) := by
      congr 1
      funext n
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (hE n),
        ae_restrict_of_ae (correctedCouplingClock_ae_unbounded N hN hp hp1 q r)] with w hw hu
      exact correctedCouplingLogicalToken_on_upperPastAccept N hN hpq r j H s hfix hfaith hrate
        hA hparent w hu n hw
    _ = (acceptedPairMeasure pairedUniformLaw E V R).map F := by
      rw [acceptedPairMeasure, Measure.map_sum hF.aemeasurable]
      congr 1
      funext n
      exact (Measure.map_map hF (hpair n)).symm
    _ = _ := upperPast_accepted_source_kernel N hN hp hp1 j H hH hcausal
      s.middle hA hparent hinit (r s.word)

end HeightPaper.CountCoupling
