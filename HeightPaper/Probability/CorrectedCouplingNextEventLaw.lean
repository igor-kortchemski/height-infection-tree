module

public import HeightPaper.Probability.CorrectedCouplingAcceptedPairLaw
public import HeightPaper.Probability.CorrectedCouplingMiddleRejection

/-!
# Transporting the accepted pair to the source event kernel

The uniform accepted label and its independent recovery draw give the full
source transition law after chronological renumbering.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HeightPaper.CountCoupling

theorem paired_freshPair_law_on_event
    (j : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ)) (hH : MeasurableSet H)
    (hcausal : ∀ w z, (∀ i, i.2 < j → w i = z i) → (w ∈ H ↔ z ∈ H)) :
    (pairedUniformLaw.restrict H).map (fun w ↦ (w (0, j), w (1, j))) =
      pairedUniformLaw H • unitUniform.prod unitUniform := by
  classical
  let C : ((Fin 2 × ℕ) → ℝ) → Bool := fun w ↦ decide (w ∈ H)
  have hC : Measurable C := by
    apply measurable_to_bool
    convert hH using 1
    ext w
    simp [C]
  have hprefix (w z : (Fin 2 × ℕ) → ℝ)
      (h : ∀ i, i.2 < j → w i = z i) : C w = C z := by
    simp only [C, propext (hcausal w z h)]
  have hCU := causal_state_indep_parent j C hC hprefix
  have hCUR := causal_state_parent_indep_recovery j C hC hprefix
  have hCtrue : C ⁻¹' {true} = H := by ext w; simp [C]
  have hcoord (i : Fin 2) (D : Set ℝ) (hD : MeasurableSet D) :
      pairedUniformLaw ((fun w ↦ w (i, j)) ⁻¹' D) = unitUniform D := by
    rw [← Measure.map_apply (measurable_pi_apply (i, j)) hD, pairedUniformLaw_map_eval]
  apply Measure.ext_prod
  intro D B hD hB
  let T : Set (Bool × ℝ) := {z | z.1 = true ∧ z.2 ∈ D}
  have hT : MeasurableSet T :=
    ((measurableSet_singleton true).preimage measurable_fst).inter (hD.preimage measurable_snd)
  have hbefore : pairedUniformLaw ((fun w ↦ (C w, w (0, j))) ⁻¹' T) =
      pairedUniformLaw H * unitUniform D := by
    change pairedUniformLaw (C ⁻¹' {true} ∩ (fun w ↦ w (0, j)) ⁻¹' D) = _
    rw [hCU.measure_inter_preimage_eq_mul {true} D (measurableSet_singleton true) hD,
      hCtrue, hcoord 0 D hD]
  have hset : (fun w ↦ (w (0, j), w (1, j))) ⁻¹' (D ×ˢ B) ∩ H =
      (fun w ↦ (C w, w (0, j))) ⁻¹' T ∩ (fun w ↦ w (1, j)) ⁻¹' B := by
    ext w
    simp [C, T, and_assoc, and_comm, and_left_comm]
  rw [Measure.map_apply ((measurable_pi_apply (0, j)).prodMk (measurable_pi_apply (1, j)))
      (hD.prod hB),
    Measure.restrict_apply ((hD.prod hB).preimage
      ((measurable_pi_apply (0, j)).prodMk (measurable_pi_apply (1, j)))), hset,
    hCUR.measure_inter_preimage_eq_mul T B hT hB, hbefore, hcoord 1 B hB,
    Measure.smul_apply, smul_eq_mul, Measure.prod_prod]
  ac_rfl

noncomputable def sourceMiddleToken (g : FiniteCouplingGenealogy) (rate : ℝ)
    (z : ℝ × ℝ) : Bool × FiniteCouplingGenealogy :=
  let b := recoveryThresholdBirth rate z.2
  (b, g.sourceStep b z.1)

noncomputable def acceptedMiddleToken (g : FiniteCouplingGenealogy) (rate : ℝ)
    (z : ℕ × ℝ) : Bool × FiniteCouplingGenealogy :=
  let b := recoveryThresholdBirth rate z.2
  (b, (g.update z.1 g.1.fresh b).chronological)

theorem measurable_sourceMiddleToken (g : FiniteCouplingGenealogy) (rate : ℝ) :
    Measurable (sourceMiddleToken g rate) := by
  have hb := (measurable_recoveryThresholdBirth rate).comp
    (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ))
  have harg : Measurable (fun z : ℝ × ℝ ↦ (recoveryThresholdBirth rate z.2, z.1)) :=
    hb.prodMk measurable_fst
  have hs : Measurable (fun z : ℝ × ℝ ↦ g.sourceStep (recoveryThresholdBirth rate z.2) z.1) := by
    simpa only [Function.comp_def] using g.measurable_sourceStep.comp harg
  change Measurable (fun z : ℝ × ℝ ↦
    (recoveryThresholdBirth rate z.2, g.sourceStep (recoveryThresholdBirth rate z.2) z.1))
  exact hb.prodMk hs

theorem measurable_acceptedMiddleToken (g : FiniteCouplingGenealogy) (rate : ℝ) :
    Measurable (acceptedMiddleToken g rate) := by
  have hb := (measurable_recoveryThresholdBirth rate).comp
    (measurable_snd : Measurable (Prod.snd : ℕ × ℝ → ℝ))
  have harg : Measurable (fun z : ℕ × ℝ ↦ (z.1, recoveryThresholdBirth rate z.2)) :=
    measurable_fst.prodMk hb
  have hf : Measurable (fun d : ℕ × Bool ↦
      (d.2, (g.update d.1 g.1.fresh d.2).chronological)) := measurable_of_countable _
  change Measurable (fun z : ℕ × ℝ ↦
    (recoveryThresholdBirth rate z.2,
      (g.update z.1 g.1.fresh (recoveryThresholdBirth rate z.2)).chronological))
  exact hf.comp harg

noncomputable def sourceMiddleTokenLaw (g : FiniteCouplingGenealogy) (rate : ℝ) :
    Measure (Bool × FiniteCouplingGenealogy) :=
  (unitUniform.prod unitUniform).map (sourceMiddleToken g rate)

instance (g : FiniteCouplingGenealogy) (rate : ℝ) :
    IsProbabilityMeasure (sourceMiddleTokenLaw g rate) := by
  unfold sourceMiddleTokenLaw
  infer_instance

theorem sourceMiddleTokenLaw_eq_uniform_labels
    (g : FiniteCouplingGenealogy) (rate : ℝ) (hA : g.1.carrier.active.Nonempty)
    (hparent : ∀ x ∈ g.1.carrier.vertices, g.1.parent x ∈ g.1.carrier.vertices) :
    sourceMiddleTokenLaw g.chronological rate =
      ((Measure.uniformOfFinset g.1.carrier.active).prod unitUniform).map
        (acceptedMiddleToken g rate) := by
  let P : ℝ × ℝ → ℕ × ℝ := Prod.map (selectFinite g.1.carrier.active hA) id
  have hP : Measurable P := (measurable_selectFinite _ hA).prodMap measurable_id
  have hcomp : acceptedMiddleToken g rate ∘ P = sourceMiddleToken g.chronological rate := by
    funext z
    have hsel : g.1.totalSelected z.1 = selectFinite g.1.carrier.active hA z.1 := by
      rw [CouplingGenealogy.totalSelected, dite_eq_left hA]
      rfl
    have hu : (g.update (selectFinite g.1.carrier.active hA z.1) g.1.fresh
        (recoveryThresholdBirth rate z.2)).chronological =
          g.chronological.sourceStep (recoveryThresholdBirth rate z.2) z.1 := by
      rw [← hsel]
      exact g.chronological_sourceUpdate hparent _ _
    exact congrArg (fun t : FiniteCouplingGenealogy ↦
      (recoveryThresholdBirth rate z.2, t)) hu
  calc
    sourceMiddleTokenLaw g.chronological rate =
        (unitUniform.prod unitUniform).map (acceptedMiddleToken g rate ∘ P) := by rw [hcomp]; rfl
    _ = ((unitUniform.prod unitUniform).map P).map (acceptedMiddleToken g rate) :=
      (Measure.map_map (measurable_acceptedMiddleToken g rate) hP).symm
    _ = _ := by
      rw [show P = Prod.map (selectFinite g.1.carrier.active hA) id from rfl,
        ← Measure.map_prod_map unitUniform unitUniform (measurable_selectFinite _ hA) measurable_id,
        selectFinite_law, Measure.map_id]

/-- The first accepted event on a causal history has the complete source
transition law, weighted by the probability of that history. -/
theorem upperPast_accepted_source_kernel
    (N : ℕ) (hN : 0 < N) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (j : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ)) (hH : MeasurableSet H)
    (hcausal : ∀ w z, (∀ i, i.2 < j → w i = z i) → (w ∈ H ↔ z ∈ H))
    (g : FiniteCouplingGenealogy) (hA : g.1.carrier.active.Nonempty)
    (hparent : ∀ x ∈ g.1.carrier.vertices, g.1.parent x ∈ g.1.carrier.vertices)
    (hinit : ∀ w ∈ H, g.1.carrier.active ⊆ (upperCarrier (Finset.range N) p w j).active)
    (rate : ℝ) :
    let A := g.1.carrier.active
    let V : ℕ → ((Fin 2 × ℕ) → ℝ) → ℕ := fun n w ↦
      selectFinite ((upperCarrier (Finset.range N) p w (j + n)).active ∪ A)
        (hA.mono Finset.subset_union_right) (w (0, j + n))
    let E : ℕ → Set ((Fin 2 × ℕ) → ℝ) := fun n ↦
      {w | upperPastPending A (Finset.range N) hA p j H w n = true ∧ V n w ∈ A}
    (acceptedPairMeasure pairedUniformLaw E V (fun n w ↦ w (1, j + n))).map
      (acceptedMiddleToken g rate) = pairedUniformLaw H • sourceMiddleTokenLaw g.chronological rate := by
  dsimp only
  rw [upperPast_acceptedPairMeasure_eq_prod N hN hp hp1 j H hH hcausal
    g.1.carrier.active hA hinit,
    Measure.map_smul _ (measurable_acceptedMiddleToken g rate).aemeasurable,
    ← sourceMiddleTokenLaw_eq_uniform_labels g rate hA hparent]

/-- The direct branch has the full source event kernel after a specified
causal history. The shared upper parent coordinate causes no marginal-law
assumption: the fresh pair law has been proved on the restricted event. -/
theorem direct_middle_source_kernel_on_event
    (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) (j : ℕ)
    (H : Set ((Fin 2 × ℕ) → ℝ)) (hH : MeasurableSet H)
    (hcausal : ∀ w z, (∀ i, i.2 < j → w i = z i) → (w ∈ H ↔ z ∈ H))
    (s : FiniteCouplingState)
    (hfix : ∀ w ∈ H, finiteCouplingStage (Finset.range N) p q r w j = s)
    (hbad : ¬(s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q))
    (hparent : ∀ x ∈ s.middle.1.carrier.vertices,
      s.middle.1.parent x ∈ s.middle.1.carrier.vertices) :
    (pairedUniformLaw.restrict H).map (fun w ↦
      (recoveryThresholdBirth (r s.word) (w (1, j)),
        (finiteCouplingStage (Finset.range N) p q r w (j + 1)).middle.chronological)) =
      pairedUniformLaw H • sourceMiddleTokenLaw s.middle.chronological (r s.word) := by
  let F := sourceMiddleToken s.middle.chronological (r s.word)
  have hF : Measurable F := measurable_sourceMiddleToken _ _
  have hpair : Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦ (w (0, j), w (1, j))) :=
    (measurable_pi_apply (0, j)).prodMk (measurable_pi_apply (1, j))
  have hcongr : (fun w ↦
      (recoveryThresholdBirth (r s.word) (w (1, j)),
        (finiteCouplingStage (Finset.range N) p q r w (j + 1)).middle.chronological)) =ᵐ[pairedUniformLaw.restrict H]
      (F ∘ fun w ↦ (w (0, j), w (1, j))) := by
    filter_upwards [ae_restrict_mem hH] with w hw
    change (recoveryThresholdBirth (r s.word) (w (1, j)),
      (finiteCouplingStage (Finset.range N) p q r w (j + 1)).middle.chronological) =
      (recoveryThresholdBirth (r s.word) (w (1, j)),
        s.middle.chronological.sourceStep (recoveryThresholdBirth (r s.word) (w (1, j))) (w (0, j)))
    apply congrArg (fun t : FiniteCouplingGenealogy ↦
      (recoveryThresholdBirth (r s.word) (w (1, j)), t))
    rw [finiteCouplingStage, hfix w hw]
    exact s.direct_middle_source_update p q r hbad hparent _ _
  calc
    _ = (pairedUniformLaw.restrict H).map (F ∘ fun w ↦ (w (0, j), w (1, j))) :=
      Measure.map_congr hcongr
    _ = ((pairedUniformLaw.restrict H).map (fun w ↦ (w (0, j), w (1, j)))).map F :=
      (Measure.map_map hF hpair).symm
    _ = _ := by
      rw [paired_freshPair_law_on_event j H hH hcausal, Measure.map_smul _ hF.aemeasurable]
      rfl

end HeightPaper.CountCoupling
