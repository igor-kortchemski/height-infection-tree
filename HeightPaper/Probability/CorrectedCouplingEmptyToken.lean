module

public import HeightPaper.Probability.CorrectedCouplingEmissionTransport

/-!
# Logical emissions after middle extinction

The middle genealogy is absorbing, but its source word must continue.
Predictable emissions select a fresh recovery uniform and therefore give
the same full token kernel as the absorbed source forest.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace HeightPaper.CountCoupling

noncomputable def flaggedEmissionSet (p q : ℝ) (r : List Bool → ℝ) (k : ℕ) :
    Set ((FiniteCouplingState × Bool) × ℝ) :=
  {z | z.1.2 = true ∧ z.1.1.word.length = k ∧ z.1.1.toState.emit p q r z.2 = true}

theorem measurableSet_flaggedEmissionSet (p q : ℝ) (r : List Bool → ℝ) (k : ℕ) :
    MeasurableSet (flaggedEmissionSet p q r k) := by
  have he : Measurable (fun z : (FiniteCouplingState × Bool) × ℝ ↦
      z.1.1.toState.emit p q r z.2) :=
    measurable_from_prod_countable_right (fun s ↦ s.1.measurable_emit p q r)
  exact (((measurable_of_countable (fun s : FiniteCouplingState × Bool ↦ s.2)).comp
    measurable_fst) (measurableSet_singleton true)).inter
      ((((measurable_of_countable (fun s : FiniteCouplingState × Bool ↦ s.1.word.length)).comp
        measurable_fst) (measurableSet_singleton k)).inter (he (measurableSet_singleton true)))

theorem empty_middle_logical_kernel_on_event
    (N : ℕ) (hN : 0 < N) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (q : ℝ) (r : List Bool → ℝ) (j : ℕ)
    (H : Set ((Fin 2 × ℕ) → ℝ)) (hH : MeasurableSet H)
    (hcausal : ∀ w z, (∀ i, i.2 < j → w i = z i) → (w ∈ H ↔ z ∈ H))
    (s : FiniteCouplingState)
    (hfix : ∀ w ∈ H, finiteCouplingStage (Finset.range N) p q r w j = s)
    (hempty : s.middle.1.carrier.active = ∅) :
    (pairedUniformLaw.restrict H).map (fun w ↦ correctedCouplingLogicalToken N p q r w s.word.length) =
      pairedUniformLaw H • sourceMiddleTokenLaw s.middle.chronological (r s.word) := by
  classical
  let roots := Finset.range N
  let flag : ((Fin 2 × ℕ) → ℝ) → Bool := fun w ↦ decide (w ∈ H)
  have hflag : Measurable flag := by
    apply measurable_to_bool
    convert hH using 1
    ext w
    simp [flag]
  let C : ℕ → ((Fin 2 × ℕ) → ℝ) → FiniteCouplingState × Bool :=
    fun n w ↦ (finiteCouplingStage roots p q r w (j + n), flag w)
  have hC (n : ℕ) : Measurable (C n) :=
    (measurable_finiteCouplingStage roots p q r (j + n)).prodMk hflag
  have hprefix (n : ℕ) (w z : (Fin 2 × ℕ) → ℝ)
      (h : ∀ i, i.2 < j + n → w i = z i) : C n w = C n z := by
    dsimp only [C]
    rw [finiteCouplingStage_congr_prefix roots p q r (j + n) h]
    have hf : flag w = flag z := by
      simp only [flag, propext (hcausal w z (fun i hi ↦ h i (by omega)))]
    rw [hf]
  let X : ℕ → ((Fin 2 × ℕ) → ℝ) → (FiniteCouplingState × Bool) × ℝ :=
    fun n w ↦ (C n w, w (0, j + n))
  let R : ℕ → ((Fin 2 × ℕ) → ℝ) → ℝ := fun n w ↦ w (1, j + n)
  let D := flaggedEmissionSet p q r s.word.length
  let E := fun n ↦ (X n) ⁻¹' D
  have hE (n : ℕ) : MeasurableSet (E n) :=
    (measurableSet_flaggedEmissionSet p q r s.word.length).preimage
      ((hC n).prodMk (measurable_pi_apply (0, j + n)))
  have hevents (n : ℕ) : E n = {w | w ∈ H ∧ correctedCouplingClock roots p q r w (j + n) =
      s.word.length ∧ (correctedCouplingStage roots p q r w (j + n)).emit p q r (w (0, j + n)) = true} := by
    ext w
    simp only [E, X, C, D, flaggedEmissionSet, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [← finiteCouplingStage_toState roots p q r w (j + n)]
    simp [flag, correctedCouplingClock, ← finiteCouplingStage_toState roots p q r w (j + n),
      FiniteCouplingState.toState]
  have hdisj : Pairwise (Disjoint on E) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro w ha hb
    rw [hevents] at ha hb
    rcases lt_or_gt_of_ne hab with h | h
    · have hc := correctedCouplingClock_lt_after_emission roots p q r w
        (show j + a < j + b by omega) ha.2.2
      rw [ha.2.1, hb.2.1] at hc
      exact (Nat.lt_irrefl _) hc
    · have hc := correctedCouplingClock_lt_after_emission roots p q r w
        (show j + b < j + a by omega) hb.2.2
      rw [ha.2.1, hb.2.1] at hc
      exact (Nat.lt_irrefl _) hc
  have hstart (w : (Fin 2 × ℕ) → ℝ) (hw : w ∈ H) :
      correctedCouplingStage roots p q r w j = s.toState := by
    rw [← finiteCouplingStage_toState, hfix w hw]
  have hcover : (⋃ n, E n) =ᵐ[pairedUniformLaw] H := by
    filter_upwards [correctedCouplingClock_ae_unbounded N hN hp hp1 q r] with w hu
    apply propext
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      rw [hevents] at hn
      exact hn.1
    · intro hw
      obtain ⟨i, hci, hei⟩ := correctedCoupling_emission_exists roots p q r w hu s.word.length
      have hcj : correctedCouplingClock roots p q r w j = s.word.length :=
        congrArg (fun t : CorrectedCouplingState ↦ t.word.length) (hstart w hw)
      have hji : j ≤ i := by
        by_contra hn
        have hc := correctedCouplingClock_lt_after_emission roots p q r w (by omega : i < j) hei
        omega
      refine ⟨i - j, ?_⟩
      rw [hevents, Nat.add_sub_of_le hji]
      exact ⟨hw, hci, hei⟩
  let F : ℝ → Bool × FiniteCouplingGenealogy :=
    fun u ↦ (recoveryThresholdBirth (r s.word) u, s.middle.chronological)
  have hF : Measurable F := (measurable_recoveryThresholdBirth _).prodMk measurable_const
  have hcongr (n : ℕ) :
      (fun w ↦ correctedCouplingLogicalToken N p q r w s.word.length) =ᵐ[pairedUniformLaw.restrict (E n)]
        F ∘ R n := by
    filter_upwards [ae_restrict_mem (hE n),
      ae_restrict_of_ae (correctedCouplingClock_ae_unbounded N hN hp hp1 q r)] with w hw hu
    rw [hevents] at hw
    have hW : (correctedCouplingStage roots p q r w (j + n)).word = s.word := by
      have hlen : correctedCouplingClock roots p q r w j =
          correctedCouplingClock roots p q r w (j + n) :=
        (congrArg (fun t : CorrectedCouplingState ↦ t.word.length) (hstart w hw.1)).trans hw.2.1.symm
      exact (correctedCouplingStage_word_eq_of_clock_eq roots p q r w
        (Nat.le_add_right j n) hlen).symm.trans
          (congrArg CorrectedCouplingState.word (hstart w hw.1))
    have hM : (finiteCouplingStage roots p q r w (j + n + 1)).middle.chronological =
        s.middle.chronological := by
      apply Subtype.ext
      have he := correctedCouplingStage_middle_eq_of_empty roots p q r w
        (show j ≤ j + n + 1 by omega)
        (show (correctedCouplingStage roots p q r w j).trees.middle.carrier.active = ∅ by
          rw [hstart w hw.1]; exact hempty)
      have he' : (correctedCouplingStage roots p q r w (j + n + 1)).trees.middle = s.middle.1 := by
        rw [he, hstart w hw.1]
        rfl
      have hval := congrArg (fun t : CorrectedCouplingState ↦ t.trees.middle)
        (finiteCouplingStage_toState roots p q r w (j + n + 1))
      exact congrArg CouplingGenealogy.chronological (hval.trans he')
    rw [← hw.2.1, correctedCouplingLogicalToken_at_emission N p q r w hu (j + n) hw.2.2, hW, hM]
    rfl
  have hcanempty : s.middle.chronological.1.carrier.active = ∅ := by
    change s.middle.1.carrier.active.image _ = ∅
    simp [hempty]
  rw [sourceMiddleTokenLaw_of_empty _ hcanempty]
  exact emission_mapped_recovery_on_event pairedUniformLaw X R
    (fun n ↦ (hC n).prodMk (measurable_pi_apply (0, j + n)))
    (fun n ↦ measurable_pi_apply (1, j + n))
    (fun n ↦ causal_state_parent_indep_recovery (j + n) (C n) (hC n) (hprefix n))
    (fun n ↦ pairedUniformLaw_map_eval (1, j + n)) (fun _ ↦ D)
    (fun _ ↦ measurableSet_flaggedEmissionSet p q r s.word.length) hdisj H hcover _
    (measurable_correctedCouplingLogicalToken N p q r _) F hF hcongr

end HeightPaper.CountCoupling
