module

public import HeightPaper.Probability.CorrectedCouplingJointKernel

/-!
# The reference joint history driven by independent fresh uniforms

This is Algorithm 1 written on the paired-uniform space, before comparison
with the coupled construction. Its history kernel follows directly from
freshness at deterministic event times.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HeightPaper.CountCoupling

noncomputable def referenceHistoryToken (N : ℕ) (r : List Bool → ℝ)
    (h : List CouplingToken) (z : ℝ × ℝ) : CouplingToken :=
  sourceMiddleToken (jointHistoryForest (Finset.range N) h) (r (jointHistoryWord h)) z

noncomputable def referenceJointHistory (N : ℕ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) : ℕ → List CouplingToken
  | 0 => []
  | k + 1 => referenceJointHistory N r w k ++
      [referenceHistoryToken N r (referenceJointHistory N r w k) (w (0, k), w (1, k))]

noncomputable def referenceLogicalToken (N : ℕ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) : CouplingToken :=
  referenceHistoryToken N r (referenceJointHistory N r w k) (w (0, k), w (1, k))

theorem referenceJointHistory_length (N : ℕ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) : (referenceJointHistory N r w k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [referenceJointHistory, List.length_append, List.length_singleton, ih]

theorem measurable_referenceJointHistory (N : ℕ) (r : List Bool → ℝ) (k : ℕ) :
    Measurable (fun w ↦ referenceJointHistory N r w k) := by
  have hstep : Measurable (fun z : List CouplingToken × (ℝ × ℝ) ↦
      z.1 ++ [referenceHistoryToken N r z.1 z.2]) := by
    apply measurable_from_prod_countable_right
    intro h
    change Measurable (fun z : ℝ × ℝ ↦ h ++
      [sourceMiddleToken (jointHistoryForest (Finset.range N) h) (r (jointHistoryWord h)) z])
    exact (measurable_of_countable (fun t : CouplingToken ↦ h ++ [t])).comp
      (measurable_sourceMiddleToken _ _)
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      exact hstep.comp (ih.prodMk
        ((measurable_pi_apply (0, k)).prodMk (measurable_pi_apply (1, k))))

theorem referenceJointHistory_congr_prefix (N : ℕ) (r : List Bool → ℝ) (k : ℕ)
    {w z : (Fin 2 × ℕ) → ℝ} (h : ∀ i, i.2 < k → w i = z i) :
    referenceJointHistory N r w k = referenceJointHistory N r z k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [referenceJointHistory, ih (fun i hi ↦ h i (by omega)),
        h (0, k) (by simp), h (1, k) (by simp)]

theorem measurable_referenceLogicalToken (N : ℕ) (r : List Bool → ℝ) (k : ℕ) :
    Measurable (fun w ↦ referenceLogicalToken N r w k) := by
  have htoken : Measurable (fun z : List CouplingToken × (ℝ × ℝ) ↦
      referenceHistoryToken N r z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro h
    change Measurable (sourceMiddleToken (jointHistoryForest (Finset.range N) h) (r (jointHistoryWord h)))
    exact measurable_sourceMiddleToken _ _
  exact htoken.comp ((measurable_referenceJointHistory N r k).prodMk
    ((measurable_pi_apply (0, k)).prodMk (measurable_pi_apply (1, k))))

theorem referenceJointHistory_eq_tokenPrefix (N : ℕ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) :
    referenceJointHistory N r w k = couplingTokenPrefix (referenceLogicalToken N r w) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [referenceJointHistory, couplingTokenPrefix_succ, ← ih]; rfl

theorem referenceJointHistory_word (N : ℕ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) :
    jointHistoryWord (referenceJointHistory N r w k) = adaptiveCouplingWord r (fun i ↦ w (1, i)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change List.map Prod.fst (_ ++ [_]) = _
      rw [List.map_append, List.map_cons, List.map_nil]
      change jointHistoryWord (referenceJointHistory N r w k) ++
        [recoveryThresholdBirth (r (jointHistoryWord (referenceJointHistory N r w k))) (w (1, k))] = _
      rw [ih, adaptiveCouplingWord_succ]

theorem referenceJointHistory_forest (N : ℕ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) :
    jointHistoryForest (Finset.range N) (referenceJointHistory N r w k) =
      sourceForestTrajectory N (adaptiveCouplingProcess r (fun i ↦ w (1, i))) (fun i ↦ w (0, i)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (List.map Prod.snd (_ ++ [_])).getLastD _ = _
      rw [List.map_append, List.map_cons, List.map_nil, List.getLastD_concat]
      change (jointHistoryForest (Finset.range N) (referenceJointHistory N r w k)).sourceStep
        (recoveryThresholdBirth (r (jointHistoryWord (referenceJointHistory N r w k))) (w (1, k)))
        (w (0, k)) = _
      rw [ih, referenceJointHistory_word]
      rfl

theorem referenceLogicalToken_source (N : ℕ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) :
    referenceLogicalToken N r w k =
      (adaptiveCouplingProcess r (fun i ↦ w (1, i)) k,
        sourceForestTrajectory N (adaptiveCouplingProcess r (fun i ↦ w (1, i))) (fun i ↦ w (0, i)) (k + 1)) := by
  change (_, (jointHistoryForest (Finset.range N) (referenceJointHistory N r w k)).sourceStep _ _) = _
  rw [referenceJointHistory_word, referenceJointHistory_forest]
  rfl

noncomputable def referencePrefixEvent (N : ℕ) (r : List Bool → ℝ)
    (h : List CouplingToken) : Set ((Fin 2 × ℕ) → ℝ) :=
  {w | referenceJointHistory N r w h.length = h}

theorem reference_logical_kernel_on_prefix (N : ℕ) (r : List Bool → ℝ) (h : List CouplingToken) :
    (pairedUniformLaw.restrict (referencePrefixEvent N r h)).map
      (fun w ↦ referenceLogicalToken N r w h.length) =
      pairedUniformLaw (referencePrefixEvent N r h) • jointHistoryKernel N r h := by
  let H := referencePrefixEvent N r h
  have hH : MeasurableSet H :=
    (measurable_referenceJointHistory N r h.length) (measurableSet_singleton h)
  have hcausal (w z : (Fin 2 × ℕ) → ℝ) (hh : ∀ i, i.2 < h.length → w i = z i) : w ∈ H ↔ z ∈ H := by
    change referenceJointHistory N r w h.length = h ↔ referenceJointHistory N r z h.length = h
    rw [referenceJointHistory_congr_prefix N r h.length hh]
  let F := referenceHistoryToken N r h
  have hF : Measurable F := measurable_sourceMiddleToken _ _
  have hp : Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦ (w (0, h.length), w (1, h.length))) :=
    (measurable_pi_apply (0, h.length)).prodMk (measurable_pi_apply (1, h.length))
  have he : (fun w ↦ referenceLogicalToken N r w h.length) =ᵐ[pairedUniformLaw.restrict H]
      F ∘ (fun w ↦ (w (0, h.length), w (1, h.length))) := by
    filter_upwards [ae_restrict_mem hH] with w hw
    change referenceHistoryToken N r (referenceJointHistory N r w h.length) _ = _
    rw [show referenceJointHistory N r w h.length = h from hw]
    rfl
  rw [Measure.map_congr he, ← Measure.map_map hF hp,
    paired_freshPair_law_on_event h.length H hH hcausal, Measure.map_smul _ hF.aemeasurable]
  rfl

theorem reference_joint_cylinder_factor (N : ℕ) (r : List Bool → ℝ)
    (h : List CouplingToken) (t : CouplingToken) :
    pairedUniformLaw (referencePrefixEvent N r (h ++ [t])) =
      pairedUniformLaw (referencePrefixEvent N r h) * jointHistoryKernel N r h {t} := by
  have hk := congrArg (fun ν : Measure CouplingToken ↦ ν {t})
    (reference_logical_kernel_on_prefix N r h)
  rw [Measure.map_apply (measurable_referenceLogicalToken N r h.length) (measurableSet_singleton t),
    Measure.restrict_apply ((measurableSet_singleton t).preimage
      (measurable_referenceLogicalToken N r h.length)), Measure.smul_apply, smul_eq_mul] at hk
  have he : referencePrefixEvent N r (h ++ [t]) =
      (fun w ↦ referenceLogicalToken N r w h.length) ⁻¹' {t} ∩ referencePrefixEvent N r h := by
    ext w
    simp only [referencePrefixEvent, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff, referenceJointHistory_eq_tokenPrefix,
      List.length_append, List.length_singleton, couplingTokenPrefix_append_iff, and_comm]
  rw [he]
  exact hk

end HeightPaper.CountCoupling
