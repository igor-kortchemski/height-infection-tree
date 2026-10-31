module

public import HeightPaper.Probability.FiniteShiftedProfileConditionalMoment
public import HeightPaper.Probability.ConditionalParentExpectation
public import HeightPaper.Model.EpidemicEventConditioning
public import HeightPaper.Probability.FiniteEventWordCoupledLaw

/-!
# Conditional expectation of the finite shifted profile

The explicit parent-uniform integral is a version of conditional expectation
given the full epidemic event-word coordinate on the coupled product space.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

/-- The parent-conditional difference moment only sees the finite birth word
through the observation horizon. -/
theorem finiteShiftedRankProfile_parent_difference_moment_congr_birth_prefix
    (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (u u' : ℕ → ℝ)
    (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n u' i)
    (z w : ℂ) (p : ℝ) :
    (∫ v, ‖finiteShiftedRankProfile l n H (u, v) k z -
      finiteShiftedRankProfile l n H (u, v) k w‖ ^ p ∂uniformLaw) =
    ∫ v, ‖finiteShiftedRankProfile l n H (u', v) k z -
      finiteShiftedRankProfile l n H (u', v) k w‖ ^ p ∂uniformLaw := by
  have hJ := finiteSafeCutoff_congr_birth_prefix he
  have hstate (v : ℕ → ℝ) := rankState_congr_events_prefix (initial n) v k
    (fun i hi ↦ he i (hi.trans_le hk))
  have hprof (v : ℕ → ℝ) (t : ℂ) :
      finiteShiftedRankProfile l n H (u, v) k t =
        finiteShiftedRankProfile l n H (u', v) k t := by
    have hC := prescribedNormalizerFrom_congr_prefix (Complex.exp t) 1
      (finiteSafeCutoff l n H u') he hk
    simp only [finiteShiftedRankProfile, prescribedNormalizedProfile,
      infectious_initial, hstate, hJ, hC]
  apply integral_congr_ae
  filter_upwards with v
  simp only [hprof v z, hprof v w]

/-- The finite shifted two-tilt moment is globally integrable on the
independent birth/parent product space. -/
theorem finiteShiftedRankProfile_difference_moment_integrable
    (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (z w : ℂ) (p : ℝ) :
    Integrable (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦
      ‖finiteShiftedRankProfile l n H r k z -
        finiteShiftedRankProfile l n H r k w‖ ^ p) birthParentLaw := by
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun r ↦
    ‖finiteShiftedRankProfile l n H r k z -
      finiteShiftedRankProfile l n H r k w‖ ^ p
  have hFmeas : Measurable F := by
    dsimp [F]
    exact (((measurable_finiteShiftedRankProfile l n H k hk z).sub
      (measurable_finiteShiftedRankProfile l n H k hk w)).norm).pow_const p
  have hFu (u : ℕ → ℝ) : Integrable (fun v ↦ F (u, v)) uniformLaw :=
    finiteShiftedRankProfile_parent_difference_integrable l n H k u z w p
  let g : (ℕ → ℝ) → ℝ := fun u ↦ ∫ v, ‖F (u, v)‖ ∂uniformLaw
  have hgcongr (u u' : ℕ → ℝ)
      (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n u' i) :
      g u = g u' := by
    have hJ := finiteSafeCutoff_congr_birth_prefix he
    have hstate (v : ℕ → ℝ) := rankState_congr_events_prefix (initial n) v k
      (fun i hi ↦ he i (hi.trans_le hk))
    have hprof (v : ℕ → ℝ) (t : ℂ) :
        finiteShiftedRankProfile l n H (u, v) k t =
          finiteShiftedRankProfile l n H (u', v) k t := by
      have hC := prescribedNormalizerFrom_congr_prefix (Complex.exp t) 1
        (finiteSafeCutoff l n H u') he hk
      simp only [finiteShiftedRankProfile, prescribedNormalizedProfile,
        infectious_initial, hstate, hJ, hC]
    apply integral_congr_ae
    filter_upwards with v
    simp only [F, hprof v z, hprof v w]
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

/-- The parent integral of each fixed finite shifted two-tilt moment is an
almost-everywhere version of conditioning on the full birth-word coordinate. -/
theorem finiteShiftedRankProfile_difference_condExp_eq_parent_integral
    (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (z w : ℂ) (p : ℝ) :
    (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦
      ∫ v, ‖finiteShiftedRankProfile l n H (r.1, v) k z -
        finiteShiftedRankProfile l n H (r.1, v) k w‖ ^ p ∂uniformLaw)
      =ᵐ[birthParentLaw]
        birthParentLaw[(fun r ↦ ‖finiteShiftedRankProfile l n H r k z -
          finiteShiftedRankProfile l n H r k w‖ ^ p) |
          (inferInstance : MeasurableSpace (ℕ → ℝ)).comap Prod.fst] := by
  have hmeas : Measurable (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦
      ‖finiteShiftedRankProfile l n H r k z -
        finiteShiftedRankProfile l n H r k w‖ ^ p) := by
    exact (((measurable_finiteShiftedRankProfile l n H k hk z).sub
      (measurable_finiteShiftedRankProfile l n H k hk w)).norm).pow_const p
  have hint := finiteShiftedRankProfile_difference_moment_integrable
    l n H k hk z w p
  exact Measure.condExp_fst_prod_ae_eq_integral
    uniformLaw uniformLaw _ hmeas hint

/-- The same parent integral is a version of conditional expectation given
the complete binary epidemic event word, rather than the richer birth-uniform
coordinate. -/
theorem finiteShiftedRankProfile_difference_condExp_eventWord_eq_parent_integral
    (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (z w : ℂ) (p : ℝ) :
    (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦
      ∫ v, ‖finiteShiftedRankProfile l n H (r.1, v) k z -
        finiteShiftedRankProfile l n H (r.1, v) k w‖ ^ p ∂uniformLaw)
      =ᵐ[birthParentLaw]
        birthParentLaw[(fun r ↦ ‖finiteShiftedRankProfile l n H r k z -
          finiteShiftedRankProfile l n H r k w‖ ^ p) |
          (inferInstance : MeasurableSpace (ℕ → Bool)).comap
            (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦ finiteBirth l n r.1)] := by
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun r ↦
    ‖finiteShiftedRankProfile l n H r k z -
      finiteShiftedRankProfile l n H r k w‖ ^ p
  let g : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun r ↦
    ∫ v, F (r.1, v) ∂uniformLaw
  let W : ((ℕ → ℝ) × (ℕ → ℝ)) → (ℕ → Bool) := fun r ↦ finiteBirth l n r.1
  let code : ((ℕ → ℝ) × (ℕ → ℝ)) → (Fin H → Bool) :=
    fun r i ↦ W r i
  have hW₀ : Measurable (finiteBirth l n) :=
    measurable_pi_iff.mpr (measurable_finiteBirth l n)
  have hW : Measurable W := hW₀.comp measurable_fst
  let mword : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (MeasurableSpace.pi : MeasurableSpace (ℕ → Bool)).comap W
  let mfst : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (MeasurableSpace.pi : MeasurableSpace (ℕ → ℝ)).comap Prod.fst
  have hwordfst : mword ≤ mfst := by
    have hh : Measurable[mfst] W := hW₀.comp (comap_measurable Prod.fst)
    exact hh.comap_le
  have hword₀ : mword ≤
      (Prod.instMeasurableSpace : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))) := by
    simpa only [mword] using hW.comap_le
  have hprefix : Measurable (fun b : ℕ → Bool ↦ fun i : Fin H ↦ b i) :=
    Measurable.of_eval (fun i ↦ measurable_pi_apply (i : ℕ))
  have hcodeword :
      (inferInstance : MeasurableSpace (Fin H → Bool)).comap code ≤ mword := by
    have hh : Measurable[mword] code := hprefix.comp (comap_measurable W)
    exact hh.comap_le
  have hgcongr (r s : (ℕ → ℝ) × (ℕ → ℝ)) (hc : code r = code s) :
      g r = g s := by
    have he : ∀ i < H, finiteBirth l n r.1 i = finiteBirth l n s.1 i :=
      fun i hi ↦ congrFun hc ⟨i, hi⟩
    have hJ := finiteSafeCutoff_congr_birth_prefix he
    have hstate (v : ℕ → ℝ) := rankState_congr_events_prefix (initial n) v k
      (fun i hi ↦ he i (hi.trans_le hk))
    have hprof (v : ℕ → ℝ) (t : ℂ) :
        finiteShiftedRankProfile l n H (r.1, v) k t =
          finiteShiftedRankProfile l n H (s.1, v) k t := by
      have hC := prescribedNormalizerFrom_congr_prefix (Complex.exp t) 1
        (finiteSafeCutoff l n H s.1) he hk
      simp only [finiteShiftedRankProfile, prescribedNormalizedProfile,
        infectious_initial, hstate, hJ, hC]
    apply integral_congr_ae
    filter_upwards with v
    simp only [F, hprof v z, hprof v w]
  have hgm : StronglyMeasurable[mword] g :=
    (stronglyMeasurable_comap_of_finite_code code g hgcongr).mono hcodeword
  have hFint : Integrable F birthParentLaw :=
    finiteShiftedRankProfile_difference_moment_integrable l n H k hk z w p
  have hgint : Integrable g birthParentLaw := by
    change Integrable (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦
      (fun u ↦ ∫ v, F (u, v) ∂uniformLaw) r.1) birthParentLaw
    exact hFint.integral_prod_left.comp_fst uniformLaw
  have hfst : g =ᵐ[birthParentLaw] birthParentLaw[F | mfst] :=
    finiteShiftedRankProfile_difference_condExp_eq_parent_integral
      l n H k hk z w p
  have hself : birthParentLaw[g | mword] = g :=
    condExp_of_stronglyMeasurable (μ := birthParentLaw) hword₀ hgm hgint
  have htower := condExp_condExp_of_le
    (μ := birthParentLaw) (f := F) hwordfst measurable_fst.comap_le
  have hcongr := condExp_congr_ae (m := mword) hfst.symm
  change g =ᵐ[birthParentLaw] birthParentLaw[F | mword]
  calc
    g =ᵐ[birthParentLaw] birthParentLaw[g | mword] := by rw [hself]
    _ =ᵐ[birthParentLaw] birthParentLaw[birthParentLaw[F | mfst] | mword] := hcongr.symm
    _ =ᵐ[birthParentLaw] birthParentLaw[F | mword] := htower

/-- On a positive finite event word, the conditional law of the original
epidemic history gives exactly the parent-uniform conditional moment of the
shifted profile difference.  The value of the random cutoff and each
normalizer is determined by that event word. -/
theorem finiteShiftedRankProfile_difference_original_eventCylinder_eq_parent_integral
    (l : ℝ≥0) (n H k : ℕ) (hk : k ≤ H) (u : ℕ → ℝ)
    (hpos : ∀ i ≤ H, 0 < prescribedWalk (finiteBirth l n u) 1 i)
    (hsupport : ∃ path ∈ eventCylinder (finiteBirth l n u) 1 H,
      path ∈ (pathLaw (l / n) n H).support)
    (z w : ℂ) (p : ℝ) :
    (∫ path, ‖prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n u)
        (initial n) (finiteSafeCutoff l n H u) k (path.eval k) -
      prescribedNormalizedProfile (Complex.exp w) (finiteBirth l n u)
        (initial n) (finiteSafeCutoff l n H u) k (path.eval k)‖ ^ p
      ∂((pathLaw (l / n) n H).filter
        (eventCylinder (finiteBirth l n u) 1 H) hsupport).toMeasure) =
      ∫ v, ‖finiteShiftedRankProfile l n H (u, v) k z -
        finiteShiftedRankProfile l n H (u, v) k w‖ ^ p ∂uniformLaw := by
  rw [pathLaw_filter_eventCylinder (l / n) n (finiteBirth l n u) H hpos hsupport]
  change (∫ path, ‖prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n u)
      (initial n) (finiteSafeCutoff l n H u) k (path.eval k) -
    prescribedNormalizedProfile (Complex.exp w) (finiteBirth l n u)
      (initial n) (finiteSafeCutoff l n H u) k (path.eval k)‖ ^ p
    ∂kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) H) = _
  rw [finiteShiftedRankProfile_parent_difference_moment_eq]
  rw [← kernelPathMeasure_map_prefixAt
    (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) H k hk]
  rw [integral_map (FinitePath.measurable _).aemeasurable
    (FinitePath.measurable _).aestronglyMeasurable]
  simp only [FinitePath.prefixAt_last]
  rfl

/-- The probability of a bad conditional shifted-profile moment on a
surviving finite word is identical under the coupled birth word and under
the original epidemic path law. The original event uses its observed count
word and any uniform representative realizing that word. -/
theorem finiteShiftedRankProfile_conditional_badMoment_original_probability
    (l : ℝ≥0) (n H k : ℕ) (hk : k ≤ H)
    (K : Set ℂ) (w : ℂ) (p ε : ℝ) :
    uniformLaw.real {u | u ∈ finiteSurvival l n H ∧
      finiteSafeCutoff l n H u ≤ k ∧
      ∃ z ∈ K, ε < ∫ v,
        ‖finiteShiftedRankProfile l n H (u, v) k z -
          finiteShiftedRankProfile l n H (u, v) k w‖ ^ p ∂uniformLaw} =
    (pathMeasure (l / n) n H).real
      {path | path.last.active.Nonempty ∧ ∃ u : ℕ → ℝ,
        (fun i : Fin H ↦ finiteBirth l n u i) = observedEventWord path ∧
        finiteSafeCutoff l n H u ≤ k ∧
        ∃ z ∈ K, ε < ∫ v,
          ‖finiteShiftedRankProfile l n H (u, v) k z -
            finiteShiftedRankProfile l n H (u, v) k w‖ ^ p ∂uniformLaw} := by
  let Bad : (ℕ → ℝ) → Prop := fun u ↦
    finiteSafeCutoff l n H u ≤ k ∧
      ∃ z ∈ K, ε < ∫ v,
        ‖finiteShiftedRankProfile l n H (u, v) k z -
          finiteShiftedRankProfile l n H (u, v) k w‖ ^ p ∂uniformLaw
  have hBad (u u' : ℕ → ℝ)
      (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n u' i) :
      Bad u ↔ Bad u' := by
    have hJ := finiteSafeCutoff_congr_birth_prefix he
    have hm (z : ℂ) :=
      finiteShiftedRankProfile_parent_difference_moment_congr_birth_prefix
        l n H k hk u u' he z w p
    simp only [Bad, hJ, hm]
  exact finiteSurvival_prefixEvent_probability_eq_pathMeasure l n H Bad hBad

end HeightPaper.CountCoupling
