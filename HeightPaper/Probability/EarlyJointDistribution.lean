module

public import HeightPaper.Probability.EarlyHeightConditionalLaw
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Distributional convergence of the early epidemic coordinates

The setwise joint limit on the countable time/flag/height space is packaged as
weak convergence of the corresponding random elements.  This isolates the
discrete part of the source's larger functional weak-limit statement.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal Classical

namespace HeightPaper.CountCoupling

theorem realThresholdEarlyTriple_tendstoInDistribution
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    TendstoInDistribution
      (fun n ↦ realThresholdEarlyTriple l δ n) atTop
      (localEarlyTriple l)
      (fun n ↦ Model.pathMeasure (rates n) n (2 * n + 1))
      birthParentLaw := by
  let μ : (n : ℕ) → Measure (Model.FinitePath (2 * n + 1)) :=
    fun n ↦ Model.pathMeasure (rates n) n (2 * n + 1)
  let X : (n : ℕ) → Model.FinitePath (2 * n + 1) → ((ℕ × Bool) × ℕ) :=
    fun n ↦ realThresholdEarlyTriple l δ n
  let Z := localEarlyTriple l
  have hX : ∀ n, Measurable (X n) := fun n ↦ Model.FinitePath.measurable _
  have hZ : Measurable Z := by
    have hbit : Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
        decide (q.1 ∈ localSurvival l)) := by
      apply measurable_to_bool
      convert (measurableSet_localSurvival l).preimage measurable_fst using 1
      ext q
      simp
    exact (((measurable_localEarlyExtinctionTime l).comp measurable_fst).prodMk
      hbit).prodMk
        (measurable_localEarlyHeight l)
  have hset (B : Set ((ℕ × Bool) × ℕ)) :
      Tendsto (fun n ↦ ((μ n).map (X n)) B) atTop
        (𝓝 ((birthParentLaw.map Z) B)) := by
    have hB : MeasurableSet B := (Set.to_countable B).measurableSet
    have hreal := realThresholdEarlyTriple_event_probability_tendsto
      rates hl hδ hrates B
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    have hleft (n : ℕ) : ((μ n).map (X n)) B =
        ENNReal.ofReal ((μ n).real (X n ⁻¹' B)) := by
      rw [Measure.map_apply (hX n) hB]
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    have hright : (birthParentLaw.map Z) B =
        ENNReal.ofReal (birthParentLaw.real (Z ⁻¹' B)) := by
      rw [Measure.map_apply hZ hB]
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    simpa only [μ, X, Z, hleft, hright, Function.comp_def] using hh
  refine ⟨fun n ↦ (hX n).aemeasurable, hZ.aemeasurable, ?_⟩
  apply tendsto_of_forall_isOpen_le_liminf'
  intro B _hB
  have hh := (hset B).liminf_eq
  change (birthParentLaw.map Z) B ≤
    liminf (fun n ↦ ((μ n).map (X n)) B) atTop
  rw [hh]

end HeightPaper.CountCoupling
