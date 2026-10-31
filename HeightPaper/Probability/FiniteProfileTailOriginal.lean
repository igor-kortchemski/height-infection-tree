module

public import HeightPaper.Probability.FiniteProfileDifferenceConditionalExpectation
public import HeightPaper.Probability.FiniteEventWordCoupledLaw

/-!
# The finite shifted-profile tail under the original epidemic path law

The source's shrinking-tilt two-time moment estimate is transferred from the
birth-uniform coupling to the actual epidemic count word.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped NNReal Topology

namespace HeightPaper.CountCoupling

open Model

theorem finiteProfileDifference_badTail_original_probability_eq
    (l : ℝ≥0) (n H A : ℕ) (hAH : A ≤ H)
    (K : Set ℂ) (p a : ℝ) :
    uniformLaw.real
      {u | u ∈ finiteSurvival l n H ∧
        finiteSafeCutoff l n H u ≤ A ∧
        ∃ z ∈ K, a < finiteProfileDifferenceMoment l n H u A H z p} =
    (pathMeasure (l / n) n H).real
      {path | path.last.active.Nonempty ∧ ∃ u : ℕ → ℝ,
        (fun i : Fin H ↦ finiteBirth l n u i) = observedEventWord path ∧
        finiteSafeCutoff l n H u ≤ A ∧
        ∃ z ∈ K, a < finiteProfileDifferenceMoment l n H u A H z p} := by
  let Bad : (ℕ → ℝ) → Prop := fun u ↦
    finiteSafeCutoff l n H u ≤ A ∧
      ∃ z ∈ K, a < finiteProfileDifferenceMoment l n H u A H z p
  have hBad (u v : ℕ → ℝ)
      (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n v i) :
      Bad u ↔ Bad v := by
    have hJ := finiteSafeCutoff_congr_birth_prefix he
    have hm (z : ℂ) :=
      finiteProfileDifferenceMoment_congr_birth_prefix he hAH le_rfl z p
    simp only [Bad, hJ, hm]
  exact finiteSurvival_prefixEvent_probability_eq_pathMeasure l n H Bad hBad

/-- The source's late-minus-early shifted-profile moment tends to zero in
probability, uniformly over shrinking complex tilt sets and compact rates,
under the original epidemic path law. -/
theorem finiteProfileDifferenceMoment_shrinking_tilts_original
    {I : Set ℝ≥0} (hI : IsCompact I)
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hxroot : ∀ l ∈ I, x < profileRoot l)
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n ≥ 1, A n ≤ ⌊T * n⌋₊)
    (K : ℕ → Set ℂ) (hK : ∀ n ≥ 1, IsCompact (K n))
    (hxK : ∀ n ≥ 1, (x : ℂ) ∈ K n)
    (hKE : ∀ n ≥ 1, ∀ l ∈ I, ∀ z ∈ K n, z.re < profileRoot l)
    (hdiam : Tendsto (fun n ↦ Metric.diam (K n)) atTop (𝓝 0)) :
    ∃ p ∈ Ioo (1 : ℝ) 2, ∀ a > 0, ∀ ε > 0, ∃ N : ℕ,
      ∀ n ≥ N, ∀ l ∈ I,
        (pathMeasure (l / n) n ⌊T * n⌋₊).real
          {path | path.last.active.Nonempty ∧ ∃ u : ℕ → ℝ,
            (fun i : Fin ⌊T * n⌋₊ ↦ finiteBirth l n u i) =
              observedEventWord path ∧
            finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ A n ∧
            ∃ z ∈ K n, a < finiteProfileDifferenceMoment l n ⌊T * n⌋₊
              u (A n) ⌊T * n⌋₊ z p} < ε := by
  obtain ⟨p, hp, hbound⟩ := finiteProfileDifferenceMoment_shrinking_tilts
    hI hT hx hparams hxroot A hA hAH K hK hxK hKE hdiam
  refine ⟨p, hp, ?_⟩
  intro a ha ε hε
  obtain ⟨N, hN⟩ := hbound a ha ε hε
  refine ⟨max N 1, ?_⟩
  intro n hn l hl
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  rw [← finiteProfileDifference_badTail_original_probability_eq
    l n ⌊T * n⌋₊ (A n) (hAH n hn1) (K n) p a]
  simpa only [finiteSurvival, mem_ofPred_eq] using hN n hnN l hl

end HeightPaper.CountCoupling
