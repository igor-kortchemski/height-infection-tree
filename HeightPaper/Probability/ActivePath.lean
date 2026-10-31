module

public import HeightPaper.Probability.FluidLocation
public import HeightPaper.Probability.ExtinctionTimes
public import HeightPaper.Probability.VanishingFilter
public import HeightPaper.Analysis.LogCounts

/-! # The actual history law restricted to activity at its endpoint -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace HeightPaper.Model

noncomputable def activePathMeasure (rate : ℝ≥0) (n N : ℕ) : Measure (FinitePath N) :=
  (pathMeasure rate n N).restrict {p | p.last.active.Nonempty}

instance (rate : ℝ≥0) (n N : ℕ) : IsFiniteMeasure (activePathMeasure rate n N) := by
  unfold activePathMeasure
  infer_instance

theorem activePathMeasure_real_apply (rate : ℝ≥0) (n N : ℕ) (A : Set (FinitePath N)) :
    (activePathMeasure rate n N).real A =
      (pathMeasure rate n N).real {p | p.last.active.Nonempty ∧ p ∈ A} := by
  rw [measureReal_def, activePathMeasure, Measure.restrict_apply (show MeasurableSet A from trivial)]
  congr 2
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq, and_comm]

theorem ae_activePath_supported (rate : ℝ≥0) (n N : ℕ) :
    ∀ᵐ p ∂activePathMeasure rate n N,
      SupportedPath rate n N p.eval ∧ p.last.active.Nonempty := by
  have hs : ∀ᵐ p ∂activePathMeasure rate n N, SupportedPath rate n N p.eval :=
    (ae_supportedPath rate n N).filter_mono (ae_mono Measure.restrict_le_self)
  have ha : ∀ᵐ p ∂activePathMeasure rate n N, p.last.active.Nonempty :=
    ae_restrict_mem (by trivial)
  exact hs.and ha

theorem eventually_activePath_supported (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) :
    ∀ᶠ i in vanishingProbabilityFilter (fun n ↦ activePathMeasure (rates n) n (horizon n)),
      SupportedPath (rates i.1) i.1 (horizon i.1) i.2.eval ∧ i.2.last.active.Nonempty := by
  rw [eventually_vanishingProbabilityFilter_iff]
  have hz (n : ℕ) : (activePathMeasure (rates n) n (horizon n)).real
      {p | ¬(SupportedPath (rates n) n (horizon n) p.eval ∧ p.last.active.Nonempty)} = 0 := by
    rw [measureReal_eq_zero_iff, measure_eq_zero_iff_ae_notMem]
    exact (ae_activePath_supported (rates n) n (horizon n)).mono fun p hp ↦ by
      simpa only [mem_ofPred_eq, not_not] using hp
  simpa only [hz] using (tendsto_const_nhds (x := (0 : ℝ)) (f := (atTop : Filter ℕ)))

/-- The actual terminal active count has logarithmic exponent one before
fluid extinction, expressed on the same varying history spaces. -/
theorem activePath_infectious_log_tendsto (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ)
    {l T : ℝ} (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    Tendsto (fun i : Σ n, FinitePath (horizon n) ↦
      Real.log (infectious i.2.last) / Real.log i.1)
      (vanishingProbabilityFilter (fun n ↦ activePathMeasure (rates n) n (horizon n))) (𝓝 1) := by
  let μ := fun n ↦ activePathMeasure (rates n) n (horizon n)
  have hI : Tendsto (fun i : Σ n, FinitePath (horizon n) ↦ (infectious i.2.last : ℝ) / i.1)
      (vanishingProbabilityFilter μ) (𝓝 (fluidInfectiousRaw l T)) := by
    apply (tendsto_vanishingProbabilityFilter_iff μ _ _).mpr
    intro ε hε
    have heq (n : ℕ) : (μ n).real {p | ε ≤ |(infectious p.last : ℝ) / n - fluidInfectiousRaw l T|} =
        (evolve (rates n) n (horizon n)).toMeasure.real
          {s | s.active.Nonempty ∧ ε ≤ |(infectious s : ℝ) / n - fluidInfectiousRaw l T|} := by
      rw [activePathMeasure_real_apply]
      simpa only [FinitePath.eval_last, mem_ofPred_eq] using
        pathMeasure_event_at (rates n) n (horizon n) (horizon n) le_rfl
          {s | s.active.Nonempty ∧ ε ≤ |(infectious s : ℝ) / n - fluidInfectiousRaw l T|}
    simp_rw [heq]
    exact evolve_active_infectious_concentration rates horizon hl hrates hhorizon hε
  exact tendsto_log_ratio_one_of_div_pos
    (tendsto_natCast_atTop_atTop.comp (tendsto_index_vanishingProbabilityFilter μ))
    (fluidInfectiousRaw_pos hl hT) hI

end HeightPaper.Model
