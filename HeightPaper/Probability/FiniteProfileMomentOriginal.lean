module

public import HeightPaper.Probability.FiniteProfileMomentConditionalExpectation
public import HeightPaper.Probability.FiniteEventWordCoupledLaw

/-!
# The finite profile moment bound under the original epidemic law

The random-word Jensen moment bound is transferred exactly from the common
birth-uniform coupling to the observed event word of the epidemic path.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

theorem finiteProfileMomentBad_original_probability_eq
    (l : ℝ≥0) (n H : ℕ) (W R : ℝ) :
    uniformLaw.real (finiteProfileMomentBad W R l n H) =
    (pathMeasure (l / n) n H).real
      {path | path.last.active.Nonempty ∧ ∃ u : ℕ → ℝ,
        (fun i : Fin H ↦ finiteBirth l n u i) = observedEventWord path ∧
        ∃ k ≤ H, finiteSafeCutoff l n H u ≤ k ∧
          ∃ w : ℂ, ‖w‖ ≤ W ∧ ∃ p : ℝ, 1 ≤ p ∧ p ≤ 2 ∧
            finiteProfileMomentRatio w p l n H u k * R <
              finiteProfileMoment w p l n H u k} := by
  let Bad : (ℕ → ℝ) → Prop := fun u ↦
    ∃ k ≤ H, finiteSafeCutoff l n H u ≤ k ∧
      ∃ w : ℂ, ‖w‖ ≤ W ∧ ∃ p : ℝ, 1 ≤ p ∧ p ≤ 2 ∧
        finiteProfileMomentRatio w p l n H u k * R <
          finiteProfileMoment w p l n H u k
  have hBad (u v : ℕ → ℝ)
      (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n v i) :
      Bad u ↔ Bad v := by
    simp only [Bad, finiteSafeCutoff_congr_birth_prefix he]
    apply exists_congr
    intro k
    apply and_congr_right
    intro hk
    apply and_congr_right
    intro _
    apply exists_congr
    intro w
    apply and_congr_right
    intro _
    apply exists_congr
    intro p
    simp only [finiteProfileMoment_congr_prefix w p he hk,
      finiteProfileMomentRatio_congr_prefix w p he hk]
  simpa only [finiteProfileMomentBad, finiteSurvival, mem_ofPred_eq, Bad] using
    finiteSurvival_prefixEvent_probability_eq_pathMeasure l n H Bad hBad

/-- The manuscript's random multiplier can be selected before event time,
complex weight, moment order, population, and rate, under the original path
law. The prescribed-word moment is the full-event-word conditional moment. -/
theorem finiteProfileMoment_uniform_bound_original
    {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {W : ℝ} (hW : 1 ≤ W) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      (pathMeasure (l / n) n ⌊T * n⌋₊).real
        {path | path.last.active.Nonempty ∧ ∃ u : ℕ → ℝ,
          (fun i : Fin ⌊T * n⌋₊ ↦ finiteBirth l n u i) =
            observedEventWord path ∧
          ∃ k ≤ ⌊T * n⌋₊, finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ k ∧
            ∃ w : ℂ, ‖w‖ ≤ W ∧ ∃ p : ℝ, 1 ≤ p ∧ p ≤ 2 ∧
              finiteProfileMomentRatio w p l n ⌊T * n⌋₊ u k * R <
                finiteProfileMoment w p l n ⌊T * n⌋₊ u k} < ε := by
  obtain ⟨R, hR, N, hbound⟩ := finiteProfileMoment_uniform_bound hI hT hparams hW hε
  refine ⟨R, hR, N, ?_⟩
  intro n hn l hl
  rw [← finiteProfileMomentBad_original_probability_eq l n ⌊T * n⌋₊ W R]
  exact hbound n hn l hl

end HeightPaper.CountCoupling
