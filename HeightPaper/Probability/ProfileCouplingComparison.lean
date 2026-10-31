module

public import HeightPaper.Probability.TreeUniformCoupling
public import HeightPaper.Model.PrescribedSusceptible
public import HeightPaper.Model.PrescribedPrefix
public import HeightPaper.Model.CoupledPrescribedWalk
public import HeightPaper.Probability.SafeCutoffConvergence

/-!
# Comparison of finite and local profiles on the same parent draws

Agreement of the event prefix and the cutoff gives exact agreement of the
normalized profile at the comparison time. The later finite-to-limit error
then splits into two errors, each on its own prescribed process law.
-/

@[expose] public section

open MeasureTheory Set

namespace HeightPaper.Model

theorem rankProfile_congr_events_prefix (w : ℂ) {e f : ℕ → Bool}
    (n J : ℕ) (v : ℕ → ℝ) {A : ℕ} (he : ∀ i < A, e i = f i) :
    prescribedNormalizedProfile w e (initial n) J A (rankState e (initial n) v A) =
      prescribedNormalizedProfile w f (initial 0) J A (rankState f (initial 0) v A) := by
  rw [rankState_initial_normalizedProfile,
    rankState_congr_events_prefix (initial 0) v A he]
  simp only [prescribedNormalizedProfile, infectious_initial,
    prescribedNormalizerFrom_congr_prefix w 1 J he le_rfl]

/-- The two error terms are functions of the same independent parent draws;
no independence between the two tree processes is assumed. -/
theorem rankProfile_coupling_difference_probability_le {e f : ℕ → Bool}
    (n J H A : ℕ) (vlimit : (ℕ → ℝ) → ℂ → ℂ) (K : Set ℂ)
    (he : ∀ i < A, e i = f i) {ε : ℝ} :
    CountCoupling.uniformLaw.real
      {v | ∃ z ∈ K, ε < ‖prescribedNormalizedProfile (Complex.exp z) e
        (initial n) J H (rankState e (initial n) v H) - vlimit v z‖} ≤
      CountCoupling.uniformLaw.real
        {v | ∃ z ∈ K, ε / 2 < ‖prescribedNormalizedProfile (Complex.exp z) e
          (initial n) J H (rankState e (initial n) v H) -
            prescribedNormalizedProfile (Complex.exp z) e (initial n) J A
              (rankState e (initial n) v A)‖} +
      CountCoupling.uniformLaw.real
        {v | ∃ z ∈ K, ε / 2 < ‖prescribedNormalizedProfile (Complex.exp z) f
          (initial 0) J A (rankState f (initial 0) v A) - vlimit v z‖} := by
  apply le_trans (measureReal_mono (μ := CountCoupling.uniformLaw) ?_) (measureReal_union_le _ _)
  rintro v ⟨z, hz, hb⟩
  by_contra hnot
  simp only [mem_union, mem_ofPred_eq, not_or] at hnot
  have h₁ := le_of_not_gt (fun h => hnot.1 ⟨z, hz, h⟩)
  have h₂ := le_of_not_gt (fun h => hnot.2 ⟨z, hz, h⟩)
  rw [← rankProfile_congr_events_prefix (Complex.exp z) n J v he] at h₂
  have htri := norm_sub_le_norm_sub_add_norm_sub (prescribedNormalizedProfile (Complex.exp z) e
    (initial n) J H (rankState e (initial n) v H))
    (prescribedNormalizedProfile (Complex.exp z) e (initial n) J A
      (rankState e (initial n) v A)) (vlimit v z)
  linarith

end HeightPaper.Model

namespace HeightPaper.CountCoupling

theorem finiteBirth_eq_localBirth_of_walk_prefix {l : ℝ} {n A : ℕ} {u : ℕ → ℝ}
    (hwalk : ∀ k ≤ A, finiteWalk l n u k = localWalk l u k) :
    ∀ i < A, finiteBirth l n u i = localBirth l u i := by
  intro i hi
  have hs := hwalk (i + 1) (by omega)
  rw [finiteWalk_succ, localWalk_succ, hwalk i hi.le] at hs
  cases hf : finiteBirth l n u i <;> cases hl : localBirth l u i <;>
    simp_all

/-- The exact tree-profile identity on the finite/local coupling event. -/
theorem finite_local_rankProfile_eq {l : ℝ} {n H A : ℕ} {u v : ℕ → ℝ}
    (hwalk : ∀ k ≤ A, finiteWalk l n u k = localWalk l u k)
    (hJ : finiteSafeCutoff l n H u = localSafeCutoff l u) (z : ℂ) :
    Model.prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n u) (Model.initial n)
        (finiteSafeCutoff l n H u) A (Model.rankState (finiteBirth l n u) (Model.initial n) v A) =
      Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u) (Model.initial 0)
        (localSafeCutoff l u) A (Model.rankState (localBirth l u) (Model.initial 0) v A) := by
  rw [hJ]
  exact Model.rankProfile_congr_events_prefix _ _ _ _
    (finiteBirth_eq_localBirth_of_walk_prefix hwalk)

end HeightPaper.CountCoupling
