module

public import HeightPaper.Probability.FiniteShiftedProfileOriginalMoment
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Source hypotheses for the shifted-profile small-tilt lemma

Compactness supplies a common lower supercritical parameter. The manuscript's
small-o diameter hypothesis implies the shrinking diameter used by the
conditional-moment proof.
-/

@[expose] public section

open MeasureTheory Filter Set Metric Asymptotics
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

open Model

theorem diameter_tendsto_zero_of_littleO_inverse_log
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (Kset : ℕ → Set ℂ)
    (hsmall : (fun n ↦ Metric.diam (Kset n)) =o[atTop]
      (fun n ↦ (1 : ℝ) / Real.log (A n))) :
    Tendsto (fun n ↦ Metric.diam (Kset n)) atTop (𝓝 0) := by
  have hAreal : Tendsto (fun n ↦ (A n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hA
  have hlog : Tendsto (fun n ↦ Real.log (A n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hAreal
  have hinv : Tendsto (fun n ↦ (1 : ℝ) / Real.log (A n)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hlog
  exact hsmall.tendsto_zero_of_tendsto hinv

/-- The manuscript's pointwise admissibility over a nonempty compact
parameter set gives a single lower rate and one shared moment order.
The conclusion is stated directly under the original epidemic path law. -/
theorem exists_uniform_finiteShiftedProfile_original_source_tilt_order
    {I : Set ℝ≥0} (hI : IsCompact I) (hne : I.Nonempty)
    {T x : ℝ} (hT : 0 < T) (hx0 : 0 < x)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l ∧
      x < profileRoot l)
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    (Kset : ℕ → Set ℂ) (hK : ∀ n, IsCompact (Kset n))
    (hxK : ∀ n, (x : ℂ) ∈ Kset n)
    (hsmall : (fun n ↦ Metric.diam (Kset n)) =o[atTop]
      (fun n ↦ (1 : ℝ) / Real.log (A n))) :
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
  obtain ⟨lmin, hlmin, hmin⟩ := hI.exists_isMinOn hne continuousOn_id
  have hparam : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l :=
    fun l hl ↦ ⟨(hparams l hl).1, (hparams l hl).2.1⟩
  have hIlower : ∀ l ∈ I, (lmin : ℝ) ≤ (l : ℝ) := by
    intro l hl
    exact_mod_cast hmin hl
  have hx : x ∈ Ioo 0 (profileRoot lmin) :=
    ⟨hx0, (hparams lmin hlmin).2.2⟩
  exact exists_uniform_finiteShiftedProfile_original_conditional_tilt_order
    hI (hparams lmin hlmin).1 hT hparam hIlower hx
    A hA hAH Kset hK hxK
    (diameter_tendsto_zero_of_littleO_inverse_log A hA Kset hsmall)

end HeightPaper.CountCoupling
