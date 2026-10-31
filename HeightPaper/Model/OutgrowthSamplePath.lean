module

public import HeightPaper.Model.RandomOutgrowth

/-! # The continuation sample is the actual two-coordinate path marginal -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace HeightPaper.Model

theorem continuationSampleLaw_succ (μ : PMF State) (rate : ℝ≥0) (K : ℕ) :
    continuationSampleLaw μ rate (K + 1) =
      (continuationSampleLaw μ rate K).bind
        (fun x ↦ (step rate x.final).map (fun t ↦ ⟨x.cutoff, t⟩)) := by
  simp only [continuationSampleLaw, continuationLaw_succ, PMF.map_bind, PMF.bind_bind,
    PMF.bind_map, Function.comp_def]

/-- The original epidemic history has exactly the previously constructed
joint cutoff/continuation law as its two-coordinate marginal. -/
theorem pathLaw_map_continuationSample (rate : ℝ≥0) (n j K : ℕ) :
    (pathLaw rate n (j + K)).map (fun p ↦ (⟨p.eval j, p.last⟩ : ContinuationSample)) =
      continuationSampleLaw (evolve rate n j) rate K := by
  induction K with
  | zero =>
      simp only [Nat.add_zero, FinitePath.eval_last, continuationSampleLaw,
        continuationLaw_zero, PMF.pure_map]
      change (pathLaw rate n j).map ((fun s : State ↦ (⟨s, s⟩ : ContinuationSample)) ∘
        FinitePath.last) = (evolve rate n j).map (fun s ↦ (⟨s, s⟩ : ContinuationSample))
      rw [← PMF.map_comp, pathLaw_map_last]
  | succ K ih =>
      rw [Nat.add_succ, pathLaw, PMF.map_bind]
      simp_rw [PMF.map_comp]
      have hf (p : FinitePath (j + K)) :
          (fun q : FinitePath (j + K + 1) ↦ (⟨q.eval j, q.last⟩ : ContinuationSample)) ∘ p.append =
            fun t ↦ (⟨p.eval j, t⟩ : ContinuationSample) := by
        funext t
        simp only [Function.comp_def, FinitePath.append_last,
          FinitePath.append_eval_of_le p t (Nat.le_add_right j K)]
      simp_rw [hf]
      change (pathLaw rate n (j + K)).bind
        ((fun x : ContinuationSample ↦ (step rate x.final).map
          (fun t ↦ (⟨x.cutoff, t⟩ : ContinuationSample))) ∘
          (fun p ↦ (⟨p.eval j, p.last⟩ : ContinuationSample))) = _
      rw [← PMF.bind_map, ih, ← continuationSampleLaw_succ]

theorem pathMeasure_map_continuationSample (rate : ℝ≥0) (n j K : ℕ) :
    (pathMeasure rate n (j + K)).map (fun p ↦ (⟨p.eval j, p.last⟩ : ContinuationSample)) =
      (continuationSampleLaw (evolve rate n j) rate K).toMeasure := by
  rw [pathMeasure, PMF.toMeasure_map _ _ (FinitePath.measurable _), pathLaw_map_continuationSample]

/-- Every supported cutoff/final sample comes from a supported full epidemic
path, so deterministic path geometry applies to it without an extra coupling. -/
theorem continuationSampleLaw_evolve_support_path (rate : ℝ≥0) (n j K : ℕ)
    (x : ContinuationSample)
    (hx : x ∈ (continuationSampleLaw (evolve rate n j) rate K).support) :
    ∃ p : FinitePath (j + K), SupportedPath rate n (j + K) p.eval ∧
      p.eval j = x.cutoff ∧ p.last = x.final := by
  rw [← pathLaw_map_continuationSample] at hx
  obtain ⟨p, hp, hpx⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  exact ⟨p, (mem_support_pathLaw_iff p).mp hp,
    congrArg ContinuationSample.cutoff hpx, congrArg ContinuationSample.final hpx⟩

/-- Event probabilities involving both cutoff and terminal states can be moved
between the actual path space and the joint continuation space. -/
theorem pathMeasure_continuationSample_event (rate : ℝ≥0) (n j K : ℕ)
    (E : Set ContinuationSample) :
    (pathMeasure rate n (j + K)).real {p | (⟨p.eval j, p.last⟩ : ContinuationSample) ∈ E} =
      (continuationSampleLaw (evolve rate n j) rate K).toMeasure.real E := by
  rw [← pathMeasure_map_continuationSample]
  exact (congrArg ENNReal.toReal (Measure.map_apply (FinitePath.measurable _)
    (show MeasurableSet E from trivial))).symm

end HeightPaper.Model
