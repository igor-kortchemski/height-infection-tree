module

public import HeightPaper.Probability.FiniteWordConditionalExpectation
public import HeightPaper.Probability.FiniteShiftedProfileConditionalExpectation

/-!
# Full event-word conditioning for finite shifted profile moments

The prescribed-word moment used in the manuscript's Jensen bound is a
version of conditional expectation given the entire binary event word.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

theorem finiteShiftedRankProfile_parent_moment_integrable
    (l : ℝ) (n H k : ℕ) (u : ℕ → ℝ) (z : ℂ) (p : ℝ) :
    Integrable (fun v ↦ ‖finiteShiftedRankProfile l n H (u, v) k z‖ ^ p)
      uniformLaw := by
  let g : FinitePath k → ℝ := fun path ↦
    ‖normalizedActiveWeight (Complex.exp z) path.last /
      finiteComplexNormalizer l n H u k z‖ ^ p
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
  rfl

theorem finiteShiftedRankProfile_moment_integrable
    (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (z : ℂ) (p : ℝ) :
    Integrable (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦
      ‖finiteShiftedRankProfile l n H r k z‖ ^ p) birthParentLaw := by
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun r ↦
    ‖finiteShiftedRankProfile l n H r k z‖ ^ p
  have hFmeas : Measurable F := by
    dsimp [F]
    exact ((measurable_finiteShiftedRankProfile l n H k hk z).norm).pow_const p
  have hFu (u : ℕ → ℝ) : Integrable (fun v ↦ F (u, v)) uniformLaw :=
    finiteShiftedRankProfile_parent_moment_integrable l n H k u z p
  let g : (ℕ → ℝ) → ℝ := fun u ↦ ∫ v, ‖F (u, v)‖ ∂uniformLaw
  have hgcongr (u u' : ℕ → ℝ)
      (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n u' i) :
      g u = g u' := by
    have hJ := finiteSafeCutoff_congr_birth_prefix he
    have hstate (v : ℕ → ℝ) := rankState_congr_events_prefix (initial n) v k
      (fun i hi ↦ he i (hi.trans_le hk))
    have hprof (v : ℕ → ℝ) :
        finiteShiftedRankProfile l n H (u, v) k z =
          finiteShiftedRankProfile l n H (u', v) k z := by
      have hC := prescribedNormalizerFrom_congr_prefix (Complex.exp z) 1
        (finiteSafeCutoff l n H u') he hk
      simp only [finiteShiftedRankProfile, prescribedNormalizedProfile,
        infectious_initial, hstate, hJ, hC]
    apply integral_congr_ae
    filter_upwards with v
    simp only [F, hprof v]
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

/-- The exact prescribed-word moment is a conditional expectation given the
full epidemic event word on the coupled product probability space. -/
theorem finiteShiftedRankProfile_moment_condExp_eventWord_eq
    (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (z : ℂ) (p : ℝ) :
    (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦
      finiteProfileMoment (Complex.exp z) p l n H r.1 k)
      =ᵐ[birthParentLaw]
        birthParentLaw[(fun r ↦ ‖finiteShiftedRankProfile l n H r k z‖ ^ p) |
          (inferInstance : MeasurableSpace (ℕ → Bool)).comap
            (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦ finiteBirth l n r.1)] := by
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun r ↦
    ‖finiteShiftedRankProfile l n H r k z‖ ^ p
  have hFmeas : Measurable F := by
    dsimp [F]
    exact ((measurable_finiteShiftedRankProfile l n H k hk z).norm).pow_const p
  have hFint : Integrable F birthParentLaw :=
    finiteShiftedRankProfile_moment_integrable l n H k hk z p
  have hprefix (u u' : ℕ → ℝ)
      (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n u' i) :
      (∫ v, F (u, v) ∂uniformLaw) = ∫ v, F (u', v) ∂uniformLaw := by
    change (∫ v, ‖finiteShiftedRankProfile l n H (u, v) k z‖ ^ p
      ∂uniformLaw) = _
    rw [finiteShiftedRankProfile_parent_moment_eq,
      finiteShiftedRankProfile_parent_moment_eq]
    exact finiteProfileMoment_congr_prefix (Complex.exp z) p he hk
  have hcond := finiteWord_condExp_eventWord_eq_parent_integral
    l n H F hFmeas hFint hprefix
  convert hcond using 1
  ext r
  exact (finiteShiftedRankProfile_parent_moment_eq l n H k r.1 z p).symm

end HeightPaper.CountCoupling
