module

public import HeightPaper.Probability.FiniteProfileDifferenceConditionalExpectation
public import HeightPaper.Probability.FiniteEventWordCoupledLaw

/-!
# Increment moments under the original epidemic path law

The finite-word moment envelope for adjacent shifted profiles transfers
without loss to the active original epidemic path.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace HeightPaper.CountCoupling

open Model

theorem finiteProfileIncrement_badMoment_original_probability_eq
    (l : ℝ≥0) (n H : ℕ) (R : ℝ) :
    uniformLaw.real
      {u | u ∈ finiteSurvival l n H ∧
        ∃ k < H, finiteSafeCutoff l n H u ≤ k ∧
          ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
            ∃ p ∈ Ioc (1 : ℝ) 2,
              Real.exp (complexProfileMomentExponent l z p * Real.log k + R) <
                finiteProfileDifferenceMoment l n H u k (k + 1) z p} =
    (pathMeasure (l / n) n H).real
      {path | path.last.active.Nonempty ∧ ∃ u : ℕ → ℝ,
        (fun i : Fin H ↦ finiteBirth l n u i) = observedEventWord path ∧
        ∃ k < H, finiteSafeCutoff l n H u ≤ k ∧
          ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
            ∃ p ∈ Ioc (1 : ℝ) 2,
              Real.exp (complexProfileMomentExponent l z p * Real.log k + R) <
                finiteProfileDifferenceMoment l n H u k (k + 1) z p} := by
  let Bad : (ℕ → ℝ) → Prop := fun u ↦
    ∃ k < H, finiteSafeCutoff l n H u ≤ k ∧
      ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
        ∃ p ∈ Ioc (1 : ℝ) 2,
          Real.exp (complexProfileMomentExponent l z p * Real.log k + R) <
            finiteProfileDifferenceMoment l n H u k (k + 1) z p
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
    intro z
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    apply exists_congr
    intro p
    simp only [finiteProfileDifferenceMoment_congr_birth_prefix he hk.le
      (by omega : k + 1 ≤ H) z p]
  exact finiteSurvival_prefixEvent_probability_eq_pathMeasure l n H Bad hBad

/-- The corrected source range is `k < ⌊Tn⌋`: the increment uses the state
and active count at `k+1`. The random exponent constant is uniform over all
time indices, tilts, moment orders, populations, and rates. -/
theorem finiteProfileIncrementMoment_uniform_exp_original
    {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      (pathMeasure (l / n) n ⌊T * n⌋₊).real
        {path | path.last.active.Nonempty ∧ ∃ u : ℕ → ℝ,
          (fun i : Fin ⌊T * n⌋₊ ↦ finiteBirth l n u i) =
            observedEventWord path ∧
          ∃ k < ⌊T * n⌋₊,
            finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ k ∧
            ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
              ∃ p ∈ Ioc (1 : ℝ) 2,
                Real.exp (complexProfileMomentExponent l z p * Real.log k + R) <
                  finiteProfileDifferenceMoment l n ⌊T * n⌋₊ u k (k + 1) z p} < ε := by
  obtain ⟨R, hR, N, hbound⟩ := finiteProfileIncrementMoment_uniform_exp hI hT hparams hε
  refine ⟨R, hR, N, ?_⟩
  intro n hn l hl
  rw [← finiteProfileIncrement_badMoment_original_probability_eq l n ⌊T * n⌋₊ R]
  simpa only [finiteSurvival, mem_ofPred_eq] using hbound n hn l hl

end HeightPaper.CountCoupling
