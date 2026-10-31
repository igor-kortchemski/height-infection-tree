module

public import HeightPaper.Probability.CountWordFactors
public import HeightPaper.Probability.FiniteLocalShiftedComplexConditionalMoment
public import HeightPaper.Probability.ConditionalParentExpectation

/-!
# The finite-to-local parent moment depends on the two count words

The finite normalized profile uses the finite birth word through its
observation horizon. The canonical local analytic limit uses the entire local
birth word. Thus its parent-integrated difference is measurable for the pair
of complete birth words.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper.CountCoupling

noncomputable def finiteLocalBirthPair (l : ℝ) (n : ℕ) (u : ℕ → ℝ) :
    (ℕ → Bool) × (ℕ → Bool) :=
  (finiteBirth l n u, localBirth l u)

theorem measurable_finiteLocalBirthPair (l : ℝ) (n : ℕ) :
    Measurable (finiteLocalBirthPair l n) := by
  exact (Measurable.of_eval (measurable_finiteBirth l n)).prodMk
    (Measurable.of_eval (measurable_localBirth l))

theorem localSafeCutoff_congr_birth_word {l : ℝ} {u u' : ℕ → ℝ}
    (he : localBirth l u = localBirth l u') :
    localSafeCutoff l u = localSafeCutoff l u' := by
  have hw : localWalk l u = localWalk l u' := by
    funext k
    simp only [localWalk, he]
  simp only [localSafeCutoff, hw]

theorem finiteLocalShifted_parent_integral_measurable_pairWord
    (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (z w : ℂ) (p : ℝ) :
    Measurable[(inferInstance : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool))).comap
      (finiteLocalBirthPair l n)]
      (fun u : ℕ → ℝ ↦ ∫ v,
        ‖finiteShiftedRankProfile l n H (u, v) k z -
          localRankProfileLimit l 0 (u, v) w‖ ^ p ∂uniformLaw) := by
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun r ↦
    ‖finiteShiftedRankProfile l n H r k z -
      localRankProfileLimit l 0 r w‖ ^ p
  let g : (ℕ → ℝ) → ℝ := fun u ↦ ∫ v, F (u, v) ∂uniformLaw
  have hF : Measurable F :=
    (((measurable_finiteShiftedRankProfile l n H k hk z).sub
      (measurable_localRankProfileLimit l 0 w)).norm).pow_const p
  have hg : Measurable g :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := uniformLaw)).measurable
  have hfactor : g.FactorsThrough (finiteLocalBirthPair l n) := by
    intro u u' he
    have hfin : finiteBirth l n u = finiteBirth l n u' :=
      congrArg Prod.fst he
    have hloc : localBirth l u = localBirth l u' :=
      congrArg Prod.snd he
    have hJfin : finiteSafeCutoff l n H u = finiteSafeCutoff l n H u' :=
      finiteSafeCutoff_congr_birth_prefix (fun i _ ↦ congrFun hfin i)
    have hJloc : localSafeCutoff l u = localSafeCutoff l u' :=
      localSafeCutoff_congr_birth_word hloc
    have hfinProf (v : ℕ → ℝ) :
        finiteShiftedRankProfile l n H (u, v) k z =
          finiteShiftedRankProfile l n H (u', v) k z := by
      simp only [finiteShiftedRankProfile, hfin, hJfin]
    have hlocProf (v : ℕ → ℝ) :
        localRankProfileLimit l 0 (u, v) w =
          localRankProfileLimit l 0 (u', v) w := by
      simp only [localRankProfileLimit, localAnalyticProfileLimit, hloc, hJloc]
    apply integral_congr_ae
    filter_upwards with v
    simp only [F, hfinProf v, hlocProf v]
  exact measurable_comap_of_factorsThrough_standardBorel
    (finiteLocalBirthPair l n) g (measurable_finiteLocalBirthPair l n) hg hfactor

/-- For every integrable observable determined by the two complete birth
words and the parent uniforms, parent integration is a version of conditional
expectation given the pair of birth words. -/
theorem pairBirthWord_condExp_eq_parent_integral
    (l : ℝ) (n : ℕ)
    (F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hF : Measurable F) (hInt : Integrable F birthParentLaw)
    (hcongr : ∀ u u' : ℕ → ℝ,
      finiteLocalBirthPair l n u = finiteLocalBirthPair l n u' →
        ∀ v, F (u, v) = F (u', v)) :
    (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦ ∫ v, F (r.1, v) ∂uniformLaw)
      =ᵐ[birthParentLaw]
        birthParentLaw[F |
          (inferInstance : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool))).comap
            (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦ finiteLocalBirthPair l n r.1)] := by
  let W : ((ℕ → ℝ) × (ℕ → ℝ)) → (ℕ → Bool) × (ℕ → Bool) :=
    fun r ↦ finiteLocalBirthPair l n r.1
  let g : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ :=
    fun r ↦ ∫ v, F (r.1, v) ∂uniformLaw
  have hW : Measurable[(Prod.instMeasurableSpace : MeasurableSpace
      ((ℕ → ℝ) × (ℕ → ℝ)))] W :=
    (measurable_finiteLocalBirthPair l n).comp measurable_fst
  have hg : Measurable[(Prod.instMeasurableSpace : MeasurableSpace
      ((ℕ → ℝ) × (ℕ → ℝ)))] g :=
    ((hF.stronglyMeasurable.integral_prod_right' (ν := uniformLaw)).measurable).comp
      measurable_fst
  have hfactor : g.FactorsThrough W := by
    intro r s he
    apply integral_congr_ae
    filter_upwards with v
    exact hcongr r.1 s.1 he v
  have hgm₀ : StronglyMeasurable[
      (Prod.instMeasurableSpace : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool))).comap W] g :=
    (measurable_comap_of_factorsThrough_standardBorel W g hW hg hfactor).stronglyMeasurable
  let mword : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (Prod.instMeasurableSpace : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool))).comap W
  let mfst : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (inferInstance : MeasurableSpace (ℕ → ℝ)).comap Prod.fst
  have hword₀ : mword ≤
      (Prod.instMeasurableSpace : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))) := hW.comap_le
  have hwordfst : mword ≤ mfst := by
    have hW' : Measurable[mfst] W :=
      (measurable_finiteLocalBirthPair l n).comp (comap_measurable Prod.fst)
    exact hW'.comap_le
  have hgm : StronglyMeasurable[mword] g := hgm₀
  have hgint : Integrable g birthParentLaw := by
    change Integrable (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦
      (fun u ↦ ∫ v, F (u, v) ∂uniformLaw) r.1) birthParentLaw
    exact hInt.integral_prod_left.comp_fst uniformLaw
  have hfst : g =ᵐ[birthParentLaw] birthParentLaw[F | mfst] :=
    Measure.condExp_fst_prod_ae_eq_integral uniformLaw uniformLaw F hF hInt
  have hself : birthParentLaw[g | mword] = g :=
    condExp_of_stronglyMeasurable (μ := birthParentLaw) hword₀ hgm hgint
  have htower := condExp_condExp_of_le
    (μ := birthParentLaw) (f := F) hwordfst measurable_fst.comap_le
  have hcongr' := condExp_congr_ae (m := mword) hfst.symm
  change g =ᵐ[birthParentLaw] birthParentLaw[F | mword]
  calc
    g =ᵐ[birthParentLaw] birthParentLaw[g | mword] := by rw [hself]
    _ =ᵐ[birthParentLaw] birthParentLaw[birthParentLaw[F | mfst] | mword] := hcongr'.symm
    _ =ᵐ[birthParentLaw] birthParentLaw[F | mword] := htower

/-- Every bounded truncation of the finite-to-local moment has the paper's
paired-word conditional expectation as its parent integral. This avoids any
global integrability assumption on the untruncated local limit. -/
theorem finiteLocalShifted_truncated_moment_condExp_pairWord
    (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (z w : ℂ) (p R : ℝ)
    (hR : 0 ≤ R) :
    (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦ ∫ v,
      min R (‖finiteShiftedRankProfile l n H (r.1, v) k z -
        localRankProfileLimit l 0 (r.1, v) w‖ ^ p) ∂uniformLaw)
      =ᵐ[birthParentLaw]
        birthParentLaw[(fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦
          min R (‖finiteShiftedRankProfile l n H r k z -
            localRankProfileLimit l 0 r w‖ ^ p)) |
          (inferInstance : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool))).comap
            (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦ finiteLocalBirthPair l n r.1)] := by
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun r ↦
    min R (‖finiteShiftedRankProfile l n H r k z -
      localRankProfileLimit l 0 r w‖ ^ p)
  have hF : Measurable F :=
    measurable_const.min ((((measurable_finiteShiftedRankProfile l n H k hk z).sub
      (measurable_localRankProfileLimit l 0 w)).norm).pow_const p)
  have hbound (r : (ℕ → ℝ) × (ℕ → ℝ)) : ‖F r‖ ≤ R := by
    have hh : 0 ≤ ‖finiteShiftedRankProfile l n H r k z -
        localRankProfileLimit l 0 r w‖ ^ p :=
      Real.rpow_nonneg (norm_nonneg _) _
    simpa only [F, Real.norm_eq_abs, abs_of_nonneg (le_min hR hh)] using
      (min_le_left R (‖finiteShiftedRankProfile l n H r k z -
        localRankProfileLimit l 0 r w‖ ^ p))
  have hInt : Integrable F birthParentLaw :=
    Integrable.of_bound hF.aestronglyMeasurable R (ae_of_all _ hbound)
  have hcongr (u u' : ℕ → ℝ)
      (he : finiteLocalBirthPair l n u = finiteLocalBirthPair l n u')
      (v : ℕ → ℝ) : F (u, v) = F (u', v) := by
    have hfin : finiteBirth l n u = finiteBirth l n u' := congrArg Prod.fst he
    have hloc : localBirth l u = localBirth l u' := congrArg Prod.snd he
    have hJfin : finiteSafeCutoff l n H u = finiteSafeCutoff l n H u' :=
      finiteSafeCutoff_congr_birth_prefix (fun i _ ↦ congrFun hfin i)
    have hJloc : localSafeCutoff l u = localSafeCutoff l u' :=
      localSafeCutoff_congr_birth_word hloc
    have hfinProf : finiteShiftedRankProfile l n H (u, v) k z =
        finiteShiftedRankProfile l n H (u', v) k z := by
      simp only [finiteShiftedRankProfile, hfin, hJfin]
    have hlocProf : localRankProfileLimit l 0 (u, v) w =
        localRankProfileLimit l 0 (u', v) w := by
      simp only [localRankProfileLimit, localAnalyticProfileLimit, hloc, hJloc]
    simp only [F, hfinProf, hlocProf]
  exact pairBirthWord_condExp_eq_parent_integral l n F hF hInt hcongr

end HeightPaper.CountCoupling
