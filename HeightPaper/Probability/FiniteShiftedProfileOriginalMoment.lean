module

public import HeightPaper.Probability.FiniteShiftedProfileConditionalExpectation

/-!
# Conditional small-tilt moments under the original epidemic path law

The finite-word probability law transports the coupled uniform-parent estimate
to the paper's actual epidemic history. On a surviving word, the parent moment
also equals the expectation under the original finite count-cylinder law.
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

open Model

/-- One moment order works for every tolerance under the original epidemic
path law, uniformly over compact rate families and shrinking complex tilt
sets. The event records the observed finite birth word of the path. -/
theorem exists_uniform_finiteShiftedProfile_original_conditional_tilt_order
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    (Kset : ℕ → Set ℂ) (hK : ∀ n, IsCompact (Kset n))
    (hxK : ∀ n, (x : ℂ) ∈ Kset n)
    (hdiam : Tendsto (fun n ↦ Metric.diam (Kset n)) atTop (𝓝 0)) :
    ∃ p ∈ Ioc (1 : ℝ) 2, ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
        (pathMeasure (l / n) n ⌊T * n⌋₊).real
          {path | path.last.active.Nonempty ∧ ∃ u : ℕ → ℝ,
            (fun i : Fin ⌊T * n⌋₊ ↦ finiteBirth l n u i) =
              observedEventWord path ∧
            finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ A n ∧
            ∃ z ∈ Kset n, ε < ∫ v,
              ‖finiteShiftedRankProfile l n ⌊T * n⌋₊ (u, v) (A n) z -
                finiteShiftedRankProfile l n ⌊T * n⌋₊ (u, v) (A n) (x : ℂ)‖ ^ p
                ∂uniformLaw} < δ := by
  obtain ⟨p, hp, hbound⟩ :=
    exists_uniform_finiteShiftedProfile_conditional_tilt_order
      hI hl₀ hT hparams hIlower hx A hA hAH Kset hK hxK hdiam
  refine ⟨p, hp, ?_⟩
  intro ε hε δ hδ
  obtain ⟨N, hN⟩ := hbound ε hε δ hδ
  refine ⟨N, ?_⟩
  intro n hn l hl
  rw [← finiteShiftedRankProfile_conditional_badMoment_original_probability
    l n ⌊T * n⌋₊ (A n) (hAH n) (Kset n) (x : ℂ) p ε]
  simpa only [finiteSurvival, mem_ofPred_eq] using hN n hn l hl

end HeightPaper.CountCoupling
