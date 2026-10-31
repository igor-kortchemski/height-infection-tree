module

public import HeightPaper.Probability.Convergence
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Negligibility of the early-extinction height

A sequence converging in law to a finite real random variable is tight. Dividing
it by a deterministic scale tending to infinity makes it negligible. This is the
first reduction in the proof of `thm:main`; the epidemic's unscaled convergence
in law must still be proved separately.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace HeightPaper

variable {Ω : ℕ → Type*} {m : ∀ n, MeasurableSpace (Ω n)}
  {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
  {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {X : (n : ℕ) → Ω n → ℝ} {Z : Ω' → ℝ}

/-- Uniform tail control for a sequence with a finite weak limit. -/
theorem bounded_tails_of_tendstoInDistribution
    (h : TendstoInDistribution X atTop Z μ μ') (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ n, (μ n).real {ω | R < |X n ω|} ≤ ε := by
  let laws : ℕ → ProbabilityMeasure ℝ := fun n ↦
    ⟨(μ n).map (X n), inferInstance⟩
  let limitLaw : ProbabilityMeasure ℝ :=
    ⟨μ'.map Z, inferInstance⟩
  have hcompact : IsCompact (insert limitLaw (Set.range laws)) :=
    h.tendsto.isCompact_insert_range
  have htight : IsTightMeasureSet (Set.range (fun n ↦ (μ n).map (X n))) := by
    apply (isTightMeasureSet_of_isCompact_closure (S := insert limitLaw (Set.range laws))
      (by simpa [hcompact.isClosed.closure_eq] using hcompact)).subset
    rintro ν ⟨n, rfl⟩
    exact ⟨laws n, Set.mem_insert_of_mem _ (Set.mem_range_self n), rfl⟩
  obtain ⟨K, hK, htail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
      (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (f := id) continuousOn_id
  refine ⟨R, fun n ↦ ?_⟩
  have hle : (μ n) {ω | R < |X n ω|} ≤ ENNReal.ofReal ε := by
    calc
      (μ n) {ω | R < |X n ω|} ≤ (μ n) ((X n) ⁻¹' Kᶜ) := by
        apply measure_mono
        intro ω hω hmem
        exact (not_lt_of_ge (hR (X n ω) hmem)) hω
      _ = (μ n).map (X n) Kᶜ :=
        (Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hK.isClosed.measurableSet.compl).symm
      _ ≤ ENNReal.ofReal ε := htail _ (Set.mem_range_self n)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq
    (ENNReal.toReal_ofReal hε.le)

/-- Division by any scale diverging to infinity kills a tight real sequence. -/
theorem negligible_diverging_scale_of_tendstoInDistribution
    (h : TendstoInDistribution X atTop Z μ μ')
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (μ n).real {ω | ε ≤ |X n ω / scale n|}) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨R, hR⟩ := bounded_tails_of_tendstoInDistribution h (δ / 2) (half_pos hδ)
  have hevent : ∀ᶠ n in atTop, max 0 (R / ε) < scale n :=
    hscale.eventually (eventually_gt_atTop _)
  filter_upwards [hevent] with n hn
  have hnpos : 0 < scale n := lt_of_le_of_lt (le_max_left _ _) hn
  have hRn : R < ε * scale n := by
    have hnR : R / ε < scale n := lt_of_le_of_lt (le_max_right _ _) hn
    exact (div_lt_iff₀ hε).mp hnR |>.trans_eq (mul_comm _ _)
  have hle : (μ n).real {ω | ε ≤ |X n ω / scale n|} ≤ δ / 2 := by
    apply (measureReal_mono (μ := μ n) (s₂ := {ω | R < |X n ω|}) ?_).trans (hR n)
    intro ω hω
    change ε ≤ |X n ω / scale n| at hω
    rw [abs_div, abs_of_pos hnpos] at hω
    exact hRn.trans_le ((le_div_iff₀ hnpos).mp hω)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  exact hle.trans_lt (half_lt_self hδ)

/-- In particular, logarithmic normalization kills the early-extinction term. -/
theorem negligible_log_scale_of_tendstoInDistribution
    (h : TendstoInDistribution X atTop Z μ μ') (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (μ n).real {ω | ε ≤ |X n ω / Real.log n|}) atTop (𝓝 0) :=
  negligible_diverging_scale_of_tendstoInDistribution h
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) ε hε

/-- The opening reduction in the proof of `thm:main`, preserving a cutoff
that may be chosen separately for each tolerance. The weak limit of the
unnormalized extinction term may also depend on that cutoff. -/
theorem height_limit_of_cutoff_estimates
    {H : (n : ℕ) → Ω n → ℝ} (κ : ℝ) (p : unitInterval)
    (hH : ∀ n, AEMeasurable (H n) (μ n))
    (hcutoff : ∀ ε > (0 : ℝ), ∃ s : (n : ℕ) → Set (Ω n),
      (∀ n, MeasurableSet (s n)) ∧
      Tendsto (fun n ↦ (μ n).real (s n)) atTop (𝓝 (p : ℝ)) ∧
      Tendsto (fun n ↦ (μ n).real
        {ω | ω ∈ s n ∧ ε ≤ |H n ω / Real.log n - κ|}) atTop (𝓝 0) ∧
      ∃ ν : ProbabilityMeasure ℝ,
        TendstoInDistribution (fun n ↦ (s n)ᶜ.indicator (H n))
          atTop id μ (ν : Measure ℝ)) :
    TendstoInDistribution (fun n ω ↦ H n ω / Real.log n) atTop id μ
      (bernoulliMeasure κ 0 p) := by
  classical
  apply tendstoInDistribution_of_survival_estimates_at_each_scale κ p
    (fun n ↦ (hH n).div_const (Real.log n))
  intro ε hε
  obtain ⟨s, hs, hp, hsurvival, ν, hextinction⟩ := hcutoff ε hε
  refine ⟨s, hs, hp, hsurvival, ?_⟩
  have hzero := negligible_log_scale_of_tendstoInDistribution hextinction ε hε
  convert hzero using 2 with n
  congr 1
  ext ω
  by_cases hω : ω ∈ s n
  · simp [hω, Set.indicator_of_notMem, not_le_of_gt hε]
  · simp [hω, Set.indicator_of_mem]

end HeightPaper
