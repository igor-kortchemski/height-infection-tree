module

public import HeightPaper.Probability.FiniteLocalShiftedPairWord
public import HeightPaper.Model.CoupledPrescribedWalk

/-!
# Conditioning on the two complete walks

The complete finite and local signed walks encode exactly the same information
as their two birth words: the increments recover each birth, and summing the
birth increments recovers each walk. The paired-word conditional-expectation
identity therefore has the literal conditioning sigma algebra of the paper.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set
open scoped NNReal

namespace HeightPaper.CountCoupling

noncomputable def finiteLocalWalkPair (l : ℝ) (n : ℕ) (u : ℕ → ℝ) :
    (ℕ → ℤ) × (ℕ → ℤ) :=
  (finiteWalk l n u, localWalk l u)

theorem measurable_finiteLocalWalkPair (l : ℝ) (n : ℕ) :
    Measurable (finiteLocalWalkPair l n) := by
  exact (Measurable.of_eval (measurable_finiteWalk l n)).prodMk
    (Measurable.of_eval (measurable_localWalk l))

theorem finiteBirth_eq_of_finiteWalk_eq {l : ℝ} {n : ℕ} {u u' : ℕ → ℝ}
    (he : finiteWalk l n u = finiteWalk l n u') :
    finiteBirth l n u = finiteBirth l n u' := by
  funext k
  have hs := congrFun he (k + 1)
  have hk := congrFun he k
  rw [finiteWalk_succ, finiteWalk_succ, hk] at hs
  cases hb : finiteBirth l n u k <;>
    cases hb' : finiteBirth l n u' k <;>
      simp_all

theorem localBirth_eq_of_localWalk_eq {l : ℝ} {u u' : ℕ → ℝ}
    (he : localWalk l u = localWalk l u') :
    localBirth l u = localBirth l u' := by
  funext k
  have hs := congrFun he (k + 1)
  have hk := congrFun he k
  rw [localWalk_succ, localWalk_succ, hk] at hs
  cases hb : localBirth l u k <;>
    cases hb' : localBirth l u' k <;>
      simp_all

theorem finiteLocalBirthPair_factorsThrough_walkPair (l : ℝ) (n : ℕ) :
    (finiteLocalBirthPair l n).FactorsThrough (finiteLocalWalkPair l n) := by
  intro u u' he
  have hfin := finiteBirth_eq_of_finiteWalk_eq (congrArg Prod.fst he)
  have hloc := localBirth_eq_of_localWalk_eq (congrArg Prod.snd he)
  exact Prod.ext hfin hloc

theorem finiteLocalWalkPair_factorsThrough_birthPair (l : ℝ) (n : ℕ) :
    (finiteLocalWalkPair l n).FactorsThrough (finiteLocalBirthPair l n) := by
  intro u u' he
  have hfin : finiteBirth l n u = finiteBirth l n u' := congrArg Prod.fst he
  have hloc : localBirth l u = localBirth l u' := congrArg Prod.snd he
  apply Prod.ext
  · change finiteWalk l n u = finiteWalk l n u'
    funext k
    simp only [finiteWalk, hfin]
  · change localWalk l u = localWalk l u'
    funext k
    simp only [localWalk, hloc]

theorem finiteLocalBirthPair_walkPair_sigma_eq (l : ℝ) (n : ℕ) :
    (inferInstance : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool))).comap
      (finiteLocalBirthPair l n) =
    (inferInstance : MeasurableSpace ((ℕ → ℤ) × (ℕ → ℤ))).comap
      (finiteLocalWalkPair l n) := by
  have hBW : Measurable[
      (inferInstance : MeasurableSpace ((ℕ → ℤ) × (ℕ → ℤ))).comap
        (finiteLocalWalkPair l n)] (finiteLocalBirthPair l n) :=
    measurable_comap_of_factorsThrough_standardBorel
      (finiteLocalWalkPair l n) (finiteLocalBirthPair l n)
      (measurable_finiteLocalWalkPair l n)
      (measurable_finiteLocalBirthPair l n)
      (finiteLocalBirthPair_factorsThrough_walkPair l n)
  have hWB : Measurable[
      (inferInstance : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool))).comap
        (finiteLocalBirthPair l n)] (finiteLocalWalkPair l n) :=
    measurable_comap_of_factorsThrough_standardBorel
      (finiteLocalBirthPair l n) (finiteLocalWalkPair l n)
      (measurable_finiteLocalBirthPair l n)
      (measurable_finiteLocalWalkPair l n)
      (finiteLocalWalkPair_factorsThrough_birthPair l n)
  exact le_antisymm hBW.comap_le hWB.comap_le

theorem finiteLocalBirthPair_walkPair_product_sigma_eq (l : ℝ) (n : ℕ) :
    (inferInstance : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool))).comap
      (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦ finiteLocalBirthPair l n r.1) =
    (inferInstance : MeasurableSpace ((ℕ → ℤ) × (ℕ → ℤ))).comap
      (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦ finiteLocalWalkPair l n r.1) := by
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using
    congrArg (fun m : MeasurableSpace (ℕ → ℝ) ↦ m.comap
      (Prod.fst : ((ℕ → ℝ) × (ℕ → ℝ)) → (ℕ → ℝ)))
      (finiteLocalBirthPair_walkPair_sigma_eq l n)

/-- The bounded finite-to-local conditional moment agrees almost everywhere
with conditional expectation given the two complete signed walks. -/
theorem finiteLocalShifted_truncated_moment_condExp_pairWalk
    (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (z w : ℂ) (p R : ℝ)
    (hR : 0 ≤ R) :
    (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦ ∫ v,
      min R (‖finiteShiftedRankProfile l n H (r.1, v) k z -
        localRankProfileLimit l 0 (r.1, v) w‖ ^ p) ∂uniformLaw)
      =ᵐ[birthParentLaw]
        birthParentLaw[(fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦
          min R (‖finiteShiftedRankProfile l n H r k z -
            localRankProfileLimit l 0 r w‖ ^ p)) |
          (inferInstance : MeasurableSpace ((ℕ → ℤ) × (ℕ → ℤ))).comap
            (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦ finiteLocalWalkPair l n r.1)] := by
  rw [← finiteLocalBirthPair_walkPair_product_sigma_eq l n]
  exact finiteLocalShifted_truncated_moment_condExp_pairWord l n H k hk z w p R hR

end HeightPaper.CountCoupling
