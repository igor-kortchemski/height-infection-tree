module

public import HeightPaper.Probability.ActivePath
public import HeightPaper.Model.EpidemicEventConditioning

/-!
# Prefix transfer under endpoint activity

The surviving full-history law assigns no more mass to a prefix event than
the surviving law at that prefix's own endpoint. Consequently every vanishing
exceptional prefix event transfers to the longer surviving history.
-/

public section

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace HeightPaper.Model

theorem pathMeasure_map_prefixAt (rate : ℝ≥0) (n N j : ℕ) (hj : j ≤ N) :
    (pathMeasure rate n N).map (fun p ↦ p.prefixAt j) = pathMeasure rate n j := by
  simpa only [pathMeasure, kernelPathMeasure, ← pathLaw_eq_kernelPathLaw] using
    kernelPathMeasure_map_prefixAt (fun _ ↦ step rate) (initial n) N j hj

theorem activePathMeasure_prefix_le (rate : ℝ≥0) (n N j : ℕ) (hj : j ≤ N)
    (A : Set (FinitePath j)) :
    (activePathMeasure rate n N).real {p | p.prefixAt j ∈ A} ≤
      (activePathMeasure rate n j).real A := by
  rw [activePathMeasure_real_apply, activePathMeasure_real_apply]
  have hmap : (pathMeasure rate n N).real
      {p | (p.prefixAt j).last.active.Nonempty ∧ p.prefixAt j ∈ A} =
      (pathMeasure rate n j).real {p | p.last.active.Nonempty ∧ p ∈ A} := by
    rw [← pathMeasure_map_prefixAt rate n N j hj]
    simp only [measureReal_def]
    rw [
      Measure.map_apply (FinitePath.measurable _)
        (show MeasurableSet {p : FinitePath j | p.last.active.Nonempty ∧ p ∈ A} from trivial)]
    rfl
  rw [← hmap]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ae_supportedPath rate n N] with p hp
  intro hmem
  refine ⟨?_, hmem.2⟩
  apply Finset.card_pos.mp
  change 0 < infectious (p.eval j)
  by_contra hz
  have hzero : infectious (p.eval j) = 0 := by omega
  have hlast := hp.infectious_eq_zero_later hj le_rfl hzero
  rw [FinitePath.eval_last] at hlast
  exact (Nat.ne_of_gt hmem.1.card_pos) hlast

theorem tendsto_prefix_vanishingProbabilityFilter (rates : ℕ → ℝ≥0)
    (horizon cutoff : ℕ → ℕ) (hcutoff : ∀ᶠ n in atTop, cutoff n ≤ horizon n) :
    Tendsto (fun i : Σ n, FinitePath (horizon n) ↦
      (⟨i.1, i.2.prefixAt (cutoff i.1)⟩ : Σ n, FinitePath (cutoff n)))
      (vanishingProbabilityFilter (fun n ↦ activePathMeasure (rates n) n (horizon n)))
      (vanishingProbabilityFilter (fun n ↦ activePathMeasure (rates n) n (cutoff n))) := by
  apply Filter.tendsto_def.mpr
  intro S hS
  change Tendsto (fun n ↦ (activePathMeasure (rates n) n (horizon n)).real
    {p | ¬((⟨n, p.prefixAt (cutoff n)⟩ : Σ n, FinitePath (cutoff n)) ∈ S)}) atTop (𝓝 0)
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hS
  filter_upwards [hcutoff] with n hn
  exact activePathMeasure_prefix_le (rates n) n (horizon n) (cutoff n) hn
    {p | (⟨n, p⟩ : Σ n, FinitePath (cutoff n)) ∉ S}

end HeightPaper.Model
