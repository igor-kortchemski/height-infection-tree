module

public import HeightPaper.Probability.FiniteLocalShiftedWalkConditioning

/-!
# Extended conditional moment on the complete count walks

The source's nonnegative conditional moment can be infinite away from the
survival event. Its canonical extended version is the parent-variable
Lebesgue integral. This value is measurable for the two full signed walks.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set
open scoped ENNReal NNReal

namespace HeightPaper.CountCoupling

noncomputable def finiteLocalShiftedExtendedMoment
    (l : ℝ) (n H k : ℕ) (z w : ℂ) (p : ℝ) (u : ℕ → ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal
    (‖finiteShiftedRankProfile l n H (u, v) k z -
      localRankProfileLimit l 0 (u, v) w‖ ^ p) ∂uniformLaw

theorem finiteLocalShiftedExtendedMoment_measurable_pairWalk
    (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (z w : ℂ) (p : ℝ) :
    Measurable[
      (inferInstance : MeasurableSpace ((ℕ → ℤ) × (ℕ → ℤ))).comap
        (finiteLocalWalkPair l n)]
      (finiteLocalShiftedExtendedMoment l n H k z w p) := by
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ≥0∞ := fun r ↦
    ENNReal.ofReal (‖finiteShiftedRankProfile l n H r k z -
      localRankProfileLimit l 0 r w‖ ^ p)
  let g : (ℕ → ℝ) → ℝ≥0∞ := fun u ↦ ∫⁻ v, F (u, v) ∂uniformLaw
  have hF : Measurable F :=
    ((((measurable_finiteShiftedRankProfile l n H k hk z).sub
      (measurable_localRankProfileLimit l 0 w)).norm).pow_const p).ennreal_ofReal
  have hg : Measurable g := hF.lintegral_prod_right'
  have hfactor : g.FactorsThrough (finiteLocalBirthPair l n) := by
    intro u u' he
    have hfin : finiteBirth l n u = finiteBirth l n u' := congrArg Prod.fst he
    have hloc : localBirth l u = localBirth l u' := congrArg Prod.snd he
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
    apply lintegral_congr_ae
    filter_upwards with v
    simp only [F, hfinProf v, hlocProf v]
  have hbirth : Measurable[
      (inferInstance : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool))).comap
        (finiteLocalBirthPair l n)] g :=
    measurable_comap_of_factorsThrough_standardBorel
      (finiteLocalBirthPair l n) g (measurable_finiteLocalBirthPair l n) hg hfactor
  rw [finiteLocalBirthPair_walkPair_sigma_eq l n] at hbirth
  exact hbirth

/-- The extended parent integral has the defining set-integral identity of
conditional expectation for every event determined by the two full walks. -/
theorem finiteLocalShiftedExtendedMoment_setLIntegral_pairWalk
    (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (z w : ℂ) (p : ℝ)
    (s : Set ((ℕ → ℝ) × (ℕ → ℝ)))
    (hs : MeasurableSet[
      (inferInstance : MeasurableSpace ((ℕ → ℤ) × (ℕ → ℤ))).comap
        (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦ finiteLocalWalkPair l n r.1)] s) :
    (∫⁻ r in s, finiteLocalShiftedExtendedMoment l n H k z w p r.1
      ∂birthParentLaw) =
    ∫⁻ r in s, ENNReal.ofReal
      (‖finiteShiftedRankProfile l n H r k z -
        localRankProfileLimit l 0 r w‖ ^ p) ∂birthParentLaw := by
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ≥0∞ := fun r ↦
    ENNReal.ofReal (‖finiteShiftedRankProfile l n H r k z -
      localRankProfileLimit l 0 r w‖ ^ p)
  let G : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ≥0∞ := fun r ↦
    finiteLocalShiftedExtendedMoment l n H k z w p r.1
  have hF : Measurable F :=
    ((((measurable_finiteShiftedRankProfile l n H k hk z).sub
      (measurable_localRankProfileLimit l 0 w)).norm).pow_const p).ennreal_ofReal
  have hG : Measurable G :=
    (hF.lintegral_prod_right').comp measurable_fst
  let W : ((ℕ → ℝ) × (ℕ → ℝ)) → (ℕ → ℤ) × (ℕ → ℤ) :=
    fun r ↦ finiteLocalWalkPair l n r.1
  let mwalk : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (inferInstance : MeasurableSpace ((ℕ → ℤ) × (ℕ → ℤ))).comap W
  let mfst : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (inferInstance : MeasurableSpace (ℕ → ℝ)).comap Prod.fst
  have hm : mwalk ≤ mfst := by
    have hW : Measurable[mfst] W :=
      (measurable_finiteLocalWalkPair l n).comp (comap_measurable Prod.fst)
    exact hW.comap_le
  obtain ⟨t, ht, hst⟩ := hm s hs
  have hset : s = t ×ˢ (Set.univ : Set (ℕ → ℝ)) := by
    rw [← hst]
    ext r
    simp
  rw [hset]
  change (∫⁻ r in t ×ˢ Set.univ, G r ∂uniformLaw.prod uniformLaw) =
    ∫⁻ r in t ×ˢ Set.univ, F r ∂uniformLaw.prod uniformLaw
  rw [setLIntegral_prod G hG.aemeasurable.restrict,
    setLIntegral_prod F hF.aemeasurable.restrict]
  simp [G, F, finiteLocalShiftedExtendedMoment]

end HeightPaper.CountCoupling
