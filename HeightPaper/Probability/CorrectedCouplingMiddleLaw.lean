module

public import HeightPaper.Probability.CorrectedCouplingTokenLaw

/-!
# The complete joint source law of the time-changed middle forest

This closes the stochastic time-change argument for arbitrary root count and
arbitrary binary source law. The emitted word and the whole chronological
forest trajectory are identified jointly, including after extinction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

noncomputable def decodeCouplingTokens (N : ℕ) (x : ℕ → CouplingToken) :
    (ℕ → Bool) × (ℕ → FiniteCouplingGenealogy) :=
  (fun k ↦ (x k).1, fun k ↦ match k with
    | 0 => FiniteCouplingGenealogy.initial (Finset.range N)
    | j + 1 => (x j).2)

theorem measurable_decodeCouplingTokens (N : ℕ) : Measurable (decodeCouplingTokens N) := by
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr (fun k ↦ measurable_fst.comp (measurable_pi_apply k))
  · apply measurable_pi_iff.mpr
    intro k
    cases k with
    | zero => exact measurable_const
    | succ j => exact measurable_snd.comp (measurable_pi_apply j)

theorem decode_correctedCouplingTokens (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) :
    decodeCouplingTokens N (correctedCouplingLogicalToken N p q r w) =
      (correctedCouplingEmittedWord (Finset.range N) p q r w, sampledMiddleForest N p q r w) := by
  apply Prod.ext
  · rfl
  · funext k
    cases k with
    | zero => exact (sampledMiddleForest_initial N p q r w).symm
    | succ j => rfl

theorem decode_referenceCouplingTokens (N : ℕ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) :
    decodeCouplingTokens N (referenceLogicalToken N r w) =
      (adaptiveCouplingProcess r (fun i ↦ w (1, i)),
        sourceForestTrajectory N (adaptiveCouplingProcess r (fun i ↦ w (1, i))) (fun i ↦ w (0, i))) := by
  apply Prod.ext
  · funext k
    exact congrArg Prod.fst (referenceLogicalToken_source N r w k)
  · funext k
    cases k with
    | zero => rfl
    | succ j => exact congrArg Prod.snd (referenceLogicalToken_source N r w j)

theorem pairedUniformLaw_map_recoveryParent :
    pairedUniformLaw.map (fun w ↦ ((fun k ↦ w (1, k)), (fun k ↦ w (0, k)))) = birthParentLaw := by
  change pairedUniformLaw.map (Prod.swap ∘ splitUniforms) = _
  rw [← Measure.map_map measurable_swap measurable_splitUniforms, pairedUniformLaw_map_split,
    birthParentLaw, Measure.prod_swap]

theorem correctedCouplingMiddle_source_joint_law
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hp1 : p ≤ 1)
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (r : List Bool → ℝ) (hr : ∀ a, 0 ≤ r a ∧ r a ≤ 1)
    (hfactor : ∀ (k : ℕ) (a : List Bool) (b : Bool), a.length = k →
      μ {x | sourceCouplingPrefix x (k + 1) = a ++ [b]} =
        μ {x | sourceCouplingPrefix x k = a} * adaptiveStepMass (r a) b) :
    pairedUniformLaw.map (fun w ↦
      (correctedCouplingEmittedWord (Finset.range N) p q r w, sampledMiddleForest N p q r w)) =
      (μ.prod uniformLaw).map (fun z ↦ (z.1, sourceForestTrajectory N z.1 z.2)) := by
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → (ℕ → Bool) × (ℕ → FiniteCouplingGenealogy) :=
    fun z ↦ (adaptiveCouplingProcess r z.1, sourceForestTrajectory N (adaptiveCouplingProcess r z.1) z.2)
  have harg : Measurable (fun z : (ℕ → ℝ) × (ℕ → ℝ) ↦ (adaptiveCouplingProcess r z.1, z.2)) :=
    ((measurable_adaptiveCouplingProcess r).comp measurable_fst).prodMk measurable_snd
  have hF : Measurable F :=
    ((measurable_adaptiveCouplingProcess r).comp measurable_fst).prodMk
      ((measurable_sourceForestTrajectory N).comp harg)
  have hC : Measurable (correctedCouplingLogicalToken N p q r) :=
    measurable_pi_iff.mpr (measurable_correctedCouplingLogicalToken N p q r)
  have hR : Measurable (referenceLogicalToken N r) :=
    measurable_pi_iff.mpr (measurable_referenceLogicalToken N r)
  have hP : Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦ ((fun k ↦ w (1, k)), (fun k ↦ w (0, k)))) :=
    measurable_swap.comp measurable_splitUniforms
  calc
    _ = (pairedUniformLaw.map (correctedCouplingLogicalToken N p q r)).map (decodeCouplingTokens N) := by
      rw [Measure.map_map (measurable_decodeCouplingTokens N) hC]
      congr 1
      funext w
      exact (decode_correctedCouplingTokens N p q r w).symm
    _ = (pairedUniformLaw.map (referenceLogicalToken N r)).map (decodeCouplingTokens N) := by
      rw [correctedCouplingLogicalToken_law N hN hp hpq hp1 r]
    _ = pairedUniformLaw.map (F ∘ fun w ↦ ((fun k ↦ w (1, k)), (fun k ↦ w (0, k)))) := by
      rw [Measure.map_map (measurable_decodeCouplingTokens N) hR]
      congr 1
      funext w
      exact decode_referenceCouplingTokens N r w
    _ = birthParentLaw.map F := by
      rw [← Measure.map_map hF hP, pairedUniformLaw_map_recoveryParent]
    _ = _ := adaptiveSourceForestTrajectory_law μ r hr hfactor N

/-- Every binary source law is covered by its canonical conditional rates. -/
theorem correctedCouplingMiddle_canonical_joint_law
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hp1 : p ≤ 1)
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ] :
    pairedUniformLaw.map (fun w ↦
      (correctedCouplingEmittedWord (Finset.range N) p q (sourceRecoveryRate μ) w,
        sampledMiddleForest N p q (sourceRecoveryRate μ) w)) =
      (μ.prod uniformLaw).map (fun z ↦ (z.1, sourceForestTrajectory N z.1 z.2)) :=
  correctedCouplingMiddle_source_joint_law N hN hp hpq hp1 μ (sourceRecoveryRate μ)
    (sourceRecoveryRate_mem_unit μ) (sourceRecoveryRate_factors μ)

end HeightPaper.CountCoupling
