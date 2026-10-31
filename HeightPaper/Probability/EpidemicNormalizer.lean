module

public import HeightPaper.Model.NormalizerAsymptotics
public import HeightPaper.Probability.ActivePath
public import HeightPaper.Probability.ReciprocalLimit

/-!
# The epidemic normalizer and its precise remaining reciprocal input

The harmonic boundary and quadratic error are proved for the actual epidemic.
The leading reciprocal-count sum is also proved for the actual epidemic, so
the final theorem has no remaining stochastic input.
-/

public section

open Filter MeasureTheory Set
open scoped Topology NNReal BigOperators

namespace HeightPaper.Model

theorem path_observedNormalizer_log_concentration_of_reciprocal
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T r w : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l)) (hw : 1 ≤ w)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    (hreciprocal : ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (pathMeasure (rates n) n (horizon n)).real {p |
        p.last.active.Nonempty ∧ ε ≤ |pathReciprocalSum p.eval (horizon n) / Real.log n - r|})
      atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (pathMeasure (rates n) n (horizon n)).real {p |
        p.last.active.Nonempty ∧ ε ≤ |Real.log (observedNormalizer w p.eval (horizon n)) /
          Real.log n - (w - 1) * ((1 + r) / 2)|}) atTop (𝓝 0) := by
  let μ := fun n ↦ activePathMeasure (rates n) n (horizon n)
  let ℓ := vanishingProbabilityFilter μ
  have hs : Tendsto (fun i : Σ n, FinitePath (horizon n) ↦ Real.log i.1) ℓ atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_index_vanishingProbabilityFilter μ))
  have hsupport : ∀ᶠ i : Σ n, FinitePath (horizon n) in ℓ,
      SupportedPath (rates i.1) i.1 (horizon i.1) i.2.eval ∧
        (i.2.eval (horizon i.1)).active.Nonempty := by
    filter_upwards [eventually_activePath_supported rates horizon] with i hi
    refine ⟨hi.1, ?_⟩
    rw [FinitePath.eval_last]
    exact hi.2
  have hr : Tendsto (fun i : Σ n, FinitePath (horizon n) ↦
      pathReciprocalSum i.2.eval (horizon i.1) / Real.log i.1) ℓ (𝓝 r) := by
    apply (tendsto_vanishingProbabilityFilter_iff μ _ _).mpr
    intro ε hε
    simpa only [μ, activePathMeasure_real_apply, mem_ofPred_eq] using hreciprocal ε hε
  have hq : Tendsto (fun i : Σ n, FinitePath (horizon n) ↦
      pathReciprocalSquareSum i.2.eval (horizon i.1) / Real.log i.1) ℓ (𝓝 0) := by
    apply (tendsto_vanishingProbabilityFilter_iff μ _ _).mpr
    intro ε hε
    have hn (n : ℕ) (p : FinitePath (horizon n)) :
        0 ≤ pathReciprocalSquareSum p.eval (horizon n) / Real.log n := by
      apply div_nonneg _ (Real.log_natCast_nonneg n)
      exact Finset.sum_nonneg fun k _ ↦ div_nonneg zero_le_one (sq_nonneg _)
    have hh := path_reciprocal_square_sum_div_log_tendsto_zero rates horizon hl hT hrates hhorizon hε
    apply hh.congr'
    filter_upwards [] with n
    rw [activePathMeasure_real_apply]
    congr 1
    ext p
    simp only [mem_ofPred_eq, sub_zero]
    rw [FinitePath.eval_last]
    rw [abs_of_nonneg (hn n p)]
    simp only [pathReciprocalSquareSum, one_div]
  have hf := activePath_infectious_log_tendsto rates horizon hl hT hrates hhorizon
  have hh := observedNormalizer_log_ratio_tendsto
    (fun i : Σ n, FinitePath (horizon n) ↦ i.2.eval) (fun i ↦ i.1)
    (fun i ↦ horizon i.1) (fun i ↦ rates i.1) (fun i ↦ Real.log i.1) hs hsupport
    (by
      convert hf using 1
      funext i
      rw [FinitePath.eval_last]) hr hq hw
  have hprob := (tendsto_vanishingProbabilityFilter_iff μ
    (fun i : Σ n, FinitePath (horizon n) ↦
      Real.log (observedNormalizer w i.2.eval (horizon i.1)) / Real.log i.1)
      ((w - 1) * ((1 + r) / 2))).mp hh
  intro ε hε
  simpa only [μ, activePathMeasure_real_apply, mem_ofPred_eq] using hprob ε hε

/-- The actual product normalizer has its predicted logarithmic coefficient. -/
theorem path_observedNormalizer_log_concentration
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T w : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l)) (hw : 1 ≤ w)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (pathMeasure (rates n) n (horizon n)).real {p |
        p.last.active.Nonempty ∧ ε ≤ |Real.log (observedNormalizer w p.eval (horizon n)) /
          Real.log n - growthFactor l * (w - 1)|}) atTop (𝓝 0) := by
  have hrecip : ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (pathMeasure (rates n) n (horizon n)).real {p |
        p.last.active.Nonempty ∧ ε ≤ |pathReciprocalSum p.eval (horizon n) / Real.log n -
          (l + 1) / (l - 1)|}) atTop (𝓝 0) := by
    intro ε hε
    have hh := path_reciprocal_sum_div_log_concentration rates horizon hl hT hrates hhorizon hε
    apply hh.congr'
    filter_upwards [] with n
    congr 1
    ext p
    simp only [mem_ofPred_eq, pathReciprocalSum]
    rw [FinitePath.eval_last]
  have heq : (w - 1) * ((1 + (l + 1) / (l - 1)) / 2) = growthFactor l * (w - 1) := by
    unfold growthFactor
    field_simp
    ring
  simpa only [heq] using path_observedNormalizer_log_concentration_of_reciprocal
    rates horizon hl hT hw hrates hhorizon hrecip

end HeightPaper.Model
