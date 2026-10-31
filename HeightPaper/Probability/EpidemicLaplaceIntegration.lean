module

public import HeightPaper.Probability.EpidemicProfileUpper
public import HeightPaper.Model.WeakProfile

/-! # Integrating the lower normalized profile with the proved upper and count limits -/

public section

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace HeightPaper.Model

/-- The full active profile follows once the matching normalized lower tail
has been established. The upper tail and logarithmic active count are proved
properties of the actual epidemic, not additional hypotheses. -/
theorem evolve_activeWeight_log_concentration_of_lower
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T x : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l)) (hx : 0 ≤ x)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    (hlower : ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (pathMeasure (rates n) n (horizon n)).real {p |
        p.last.active.Nonempty ∧ ε ≤ growthFactor l * (Real.exp x - 1) -
          Real.log (realNormalizedLaplace x p.last) / Real.log n}) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp x) s) / Real.log n -
          (1 + growthFactor l * (Real.exp x - 1))|}) atTop (𝓝 0) := by
  let μ := fun n ↦ activePathMeasure (rates n) n (horizon n)
  let b := growthFactor l * (Real.exp x - 1)
  have hmean : Tendsto (fun i : Σ n, FinitePath (horizon n) ↦
      Real.log (realNormalizedLaplace x i.2.last) / Real.log i.1)
      (vanishingProbabilityFilter μ) (𝓝 b) := by
    apply (tendsto_vanishingProbabilityFilter_iff μ _ _).mpr
    intro ε hε
    have ht := (path_normalizedLaplace_log_upper rates horizon hl hT hx hrates hhorizon ε hε).add
      (hlower ε hε)
    rw [zero_add] at ht
    apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ ht
    intro n
    rw [activePathMeasure_real_apply]
    apply (measureReal_mono ?_).trans (measureReal_union_le _ _)
    intro p hp
    simp only [mem_ofPred_eq] at hp ⊢
    by_cases hu : ε ≤ Real.log (realNormalizedLaplace x p.last) / Real.log n - b
    · exact Or.inl ⟨hp.1, hu⟩
    · right
      refine ⟨hp.1, ?_⟩
      by_contra hlw
      have hh : |Real.log (realNormalizedLaplace x p.last) / Real.log n - b| < ε := by
        rw [abs_lt]
        constructor <;> linarith [lt_of_not_ge hu, lt_of_not_ge hlw]
      exact not_lt_of_ge hp.2 hh
  have hfull := hmean.add (activePath_infectious_log_tendsto rates horizon hl hT hrates hhorizon)
  have hw : Tendsto (fun i : Σ n, FinitePath (horizon n) ↦
      Real.log (activeWeight (Real.exp x) i.2.last) / Real.log i.1)
      (vanishingProbabilityFilter μ) (𝓝 (1 + b)) := by
    rw [add_comm b 1] at hfull
    apply hfull.congr'
    filter_upwards [eventually_activePath_supported rates horizon] with i hi
    have hI : (0 : ℝ) < infectious i.2.last := by exact_mod_cast hi.2.card_pos
    have hW := activeWeight_exp_pos i.2.last hi.2 x
    dsimp only [realNormalizedLaplace]
    rw [Real.log_div hW.ne' hI.ne']
    ring
  intro ε hε
  have hp := (tendsto_vanishingProbabilityFilter_iff μ _ _).mp hw ε hε
  apply hp.congr
  intro n
  rw [activePathMeasure_real_apply]
  simpa only [FinitePath.eval_last, Set.mem_ofPred_eq, b] using pathMeasure_event_at
    (rates n) n (horizon n) (horizon n) le_rfl
    {s | s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp x) s) / Real.log n -
      (1 + growthFactor l * (Real.exp x - 1))|}

end HeightPaper.Model
