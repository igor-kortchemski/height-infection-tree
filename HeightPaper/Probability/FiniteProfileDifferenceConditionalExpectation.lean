module

public import HeightPaper.Probability.FiniteWordConditionalExpectation
public import HeightPaper.Probability.FiniteShiftedProfileConditionalExpectation
public import HeightPaper.Probability.FiniteProfileIncrements

/-!
# Conditional moments of two observations of the finite shifted profile

Both observations use one tree history. Their parent-uniform moment is the
prescribed-word moment, and this is conditioning on the full binary event word.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

noncomputable def finiteShiftedProfileTimeMoment (l : ℝ) (n H : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) (j k : ℕ) (z : ℂ) (p : ℝ) : ℝ :=
  ‖finiteShiftedRankProfile l n H q k z -
    finiteShiftedRankProfile l n H q j z‖ ^ p

/-- Integration over the parent uniforms gives the paper's two-time
prescribed-word moment exactly. -/
theorem finiteShiftedProfileTimeMoment_parent_integral
    (l : ℝ) (n H : ℕ) (u : ℕ → ℝ) (j k : ℕ) (hjk : j ≤ k)
    (z : ℂ) (p : ℝ) :
    (∫ v, finiteShiftedProfileTimeMoment l n H (u, v) j k z p ∂uniformLaw) =
      finiteProfileDifferenceMoment l n H u j k z p := by
  unfold finiteProfileDifferenceMoment
  rw [← rankHistory_law (finiteBirth l n u) (initial n) k]
  rw [integral_map (measurable_rankHistory (finiteBirth l n u) (initial n) k).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  unfold finiteShiftedProfileTimeMoment finiteShiftedRankProfile
  simp only [prescribedNormalizedProfile, finiteComplexNormalizer, infectious_initial,
    rankHistory, trajectoryPrefix_last, trajectoryPrefix_eval k _ j hjk]

theorem finiteShiftedProfileTimeMoment_parent_integrable
    (l : ℝ) (n H : ℕ) (u : ℕ → ℝ) (j k : ℕ) (hjk : j ≤ k)
    (z : ℂ) (p : ℝ) :
    Integrable (fun v ↦ finiteShiftedProfileTimeMoment l n H (u, v) j k z p)
      uniformLaw := by
  let g : FinitePath k → ℝ := fun path ↦
    ‖normalizedActiveWeight (Complex.exp z) path.last /
        finiteComplexNormalizer l n H u k z -
      normalizedActiveWeight (Complex.exp z) (path.eval j) /
        finiteComplexNormalizer l n H u j z‖ ^ p
  have hg : Integrable g (kernelPathMeasure
      (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k) :=
    integrable_kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i))
      (fun i s ↦ finite_support_prescribedStep _ s) (initial n) k g
  have hgmap : Integrable g
      (uniformLaw.map (rankHistory (finiteBirth l n u) (initial n) k)) := by
    rw [rankHistory_law]
    exact hg
  have hcomp := hgmap.comp_measurable
    (measurable_rankHistory (finiteBirth l n u) (initial n) k)
  convert hcomp using 1
  ext v
  dsimp only [g, Function.comp_apply]
  simp only [finiteShiftedProfileTimeMoment, finiteShiftedRankProfile,
    prescribedNormalizedProfile, finiteComplexNormalizer, infectious_initial,
    rankHistory, trajectoryPrefix_last, trajectoryPrefix_eval k _ j hjk]

theorem finiteShiftedProfileTimeMoment_integrable
    (l : ℝ) (n H j k : ℕ) (hj : j ≤ H) (hk : k ≤ H) (hjk : j ≤ k)
    (z : ℂ) (p : ℝ) :
    Integrable (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      finiteShiftedProfileTimeMoment l n H q j k z p) birthParentLaw := by
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun q ↦
    finiteShiftedProfileTimeMoment l n H q j k z p
  have hFmeas : Measurable F := by
    dsimp [F, finiteShiftedProfileTimeMoment]
    exact (((measurable_finiteShiftedRankProfile l n H k hk z).sub
      (measurable_finiteShiftedRankProfile l n H j hj z)).norm).pow_const p
  have hFu (u : ℕ → ℝ) : Integrable (fun v ↦ F (u, v)) uniformLaw :=
    finiteShiftedProfileTimeMoment_parent_integrable l n H u j k hjk z p
  let g : (ℕ → ℝ) → ℝ := fun u ↦ ∫ v, ‖F (u, v)‖ ∂uniformLaw
  have hgcongr (u u' : ℕ → ℝ)
      (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n u' i) :
      g u = g u' := by
    have hJ := finiteSafeCutoff_congr_birth_prefix he
    have hstate (v : ℕ → ℝ) (t : ℕ) (ht : t ≤ H) :=
      rankState_congr_events_prefix (initial n) v t
        (fun i hi ↦ he i (hi.trans_le ht))
    have hprof (v : ℕ → ℝ) (t : ℕ) (ht : t ≤ H) :
        finiteShiftedRankProfile l n H (u, v) t z =
          finiteShiftedRankProfile l n H (u', v) t z := by
      have hC := prescribedNormalizerFrom_congr_prefix (Complex.exp z) 1
        (finiteSafeCutoff l n H u') he ht
      simp only [finiteShiftedRankProfile, prescribedNormalizedProfile,
        infectious_initial, hstate v t ht, hJ, hC]
    apply integral_congr_ae
    filter_upwards with v
    simp only [F, finiteShiftedProfileTimeMoment, hprof v j hj, hprof v k hk]
  have hcode : Measurable (fun u : ℕ → ℝ ↦
      fun i : Fin H ↦ finiteBirth l n u i) :=
    Measurable.of_eval (fun i ↦ measurable_finiteBirth l n i)
  have hg : Integrable g uniformLaw :=
    integrable_of_finite_code uniformLaw
      (fun u : ℕ → ℝ ↦ fun i : Fin H ↦ finiteBirth l n u i)
      hcode g (fun u u' he ↦ hgcongr u u' (fun i hi ↦
        congrFun he ⟨i, hi⟩))
  have hprod : Integrable F (uniformLaw.prod uniformLaw) :=
    (integrable_prod_iff hFmeas.aestronglyMeasurable).2
      ⟨ae_of_all _ hFu, hg⟩
  change Integrable F birthParentLaw
  exact hprod

/-- The prescribed-word two-time moment is almost everywhere the conditional
moment given the complete binary event word. -/
theorem finiteProfileDifferenceMoment_condExp_eventWord_eq
    (l : ℝ) (n H j k : ℕ) (hj : j ≤ H) (hk : k ≤ H) (hjk : j ≤ k)
    (z : ℂ) (p : ℝ) :
    (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      finiteProfileDifferenceMoment l n H q.1 j k z p)
      =ᵐ[birthParentLaw]
        birthParentLaw[(fun q ↦ finiteShiftedProfileTimeMoment l n H q j k z p) |
          (inferInstance : MeasurableSpace (ℕ → Bool)).comap
            (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦ finiteBirth l n q.1)] := by
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun q ↦
    finiteShiftedProfileTimeMoment l n H q j k z p
  have hFmeas : Measurable F := by
    dsimp [F, finiteShiftedProfileTimeMoment]
    exact (((measurable_finiteShiftedRankProfile l n H k hk z).sub
      (measurable_finiteShiftedRankProfile l n H j hj z)).norm).pow_const p
  have hFint : Integrable F birthParentLaw :=
    finiteShiftedProfileTimeMoment_integrable l n H j k hj hk hjk z p
  have hprefix (u u' : ℕ → ℝ)
      (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n u' i) :
      (∫ v, F (u, v) ∂uniformLaw) = ∫ v, F (u', v) ∂uniformLaw := by
    rw [finiteShiftedProfileTimeMoment_parent_integral l n H u j k hjk z p,
      finiteShiftedProfileTimeMoment_parent_integral l n H u' j k hjk z p]
    exact finiteProfileDifferenceMoment_congr_birth_prefix he hj hk z p
  have hcond := finiteWord_condExp_eventWord_eq_parent_integral
    l n H F hFmeas hFint hprefix
  convert hcond using 1
  ext q
  exact (finiteShiftedProfileTimeMoment_parent_integral l n H q.1 j k hjk z p).symm

end HeightPaper.CountCoupling
