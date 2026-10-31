module

public import HeightPaper.Probability.EarlyHeightJointDistribution

/-!
# Weak convergence of the logarithmic cutoff height

The two-branch height estimate yields weak convergence of the real-valued
height, including its atoms at zero and at the surviving coefficient.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal Classical

namespace HeightPaper.CountCoupling

theorem realThreshold_heightLog_tendstoInDistribution
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    TendstoInDistribution
      (fun (n : ℕ) p ↦ (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
        Real.log n) atTop
      (fun q ↦ if (localEarlyTriple l q).1.2 then
        growthFactor l * Real.exp (profileRoot l) else 0)
      (fun n ↦ Model.pathMeasure (rates n) n (2 * n + 1))
      birthParentLaw := by
  let a := growthFactor l * Real.exp (profileRoot l)
  let Y : (n : ℕ) → Model.FinitePath (2 * n + 1) → ℝ :=
    fun n p ↦ (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) / Real.log n
  let Z : ((ℕ × Bool) × ℕ) → ℝ := fun z ↦ if z.1.2 then a else 0
  have htriple := realThresholdEarlyTriple_tendstoInDistribution
    rates hl hδ hrates
  have hZ : Continuous Z := continuous_of_discreteTopology
  have hgraph := htriple.continuous_comp hZ
  refine ⟨(fun n ↦ (Model.FinitePath.measurable (Y n)).aemeasurable),
    hgraph.aemeasurable_limit, ?_⟩
  apply tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  have hε0 : ∃ ε : ℝ, 0 < ε ∧ ((0 : ℝ) ∈ G → Metric.ball 0 ε ⊆ G) := by
    by_cases h : (0 : ℝ) ∈ G
    · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hG 0 h
      exact ⟨ε, hε, fun _ ↦ hball⟩
    · exact ⟨1, by norm_num, fun h0 ↦ (h h0).elim⟩
  have hεa : ∃ ε : ℝ, 0 < ε ∧ (a ∈ G → Metric.ball a ε ⊆ G) := by
    by_cases h : a ∈ G
    · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hG a h
      exact ⟨ε, hε, fun _ ↦ hball⟩
    · exact ⟨1, by norm_num, fun ha ↦ (h ha).elim⟩
  obtain ⟨ε0, hε0, hball0⟩ := hε0
  obtain ⟨εa, hεa, hballa⟩ := hεa
  let ε := min ε0 εa
  have hε : 0 < ε := lt_min hε0 hεa
  let B : Set ((ℕ × Bool) × ℕ) := Z ⁻¹' G
  have hB := realThresholdEarlyTriple_event_probability_tendsto
    rates hl hδ hrates B
  have hbad := realThresholdHeightLogBad_probability_tendsto_zero
    rates hl hδ hrates hε
  have hsub (n : ℕ) :
      (fun p ↦ Z (realThresholdEarlyTriple l δ n p)) ⁻¹' G ⊆
        (Y n ⁻¹' G) ∪ realThresholdHeightLogBad l δ ε n := by
    intro p hp
    by_cases hclose : |Y n p - Z (realThresholdEarlyTriple l δ n p)| < ε
    · left
      have hball : Metric.ball (Z (realThresholdEarlyTriple l δ n p)) ε ⊆ G := by
        by_cases hb : (realThresholdEarlyTriple l δ n p).1.2
        · simpa only [Z, ite_eq_left hb] using
            (Set.Subset.trans (Metric.ball_subset_ball (min_le_right _ _)) (hballa (by simpa [Z, hb] using hp)))
        · simpa only [Z, ite_eq_right hb] using
            (Set.Subset.trans (Metric.ball_subset_ball (min_le_left _ _)) (hball0 (by simpa [Z, hb] using hp)))
      exact hball (by simpa only [Metric.mem_ball, Real.dist_eq] using hclose)
    · right
      have hreal : Z (realThresholdEarlyTriple l δ n p) =
          if (1 - δ) * fluidExtinctionTime l * n ≤
              ((2 * p.last.vertices - 1 : ℕ) : ℝ) then a else 0 := by
        simp [Z, realThresholdEarlyTriple, realThresholdEarlyPair]
      change ε ≤ |Y n p - (if (1 - δ) * fluidExtinctionTime l * n ≤
          ((2 * p.last.vertices - 1 : ℕ) : ℝ) then a else 0)|
      rw [← hreal]
      exact le_of_not_gt hclose
  have hbound (n : ℕ) :
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (realThresholdEarlyTriple l δ n ⁻¹' B) -
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (realThresholdHeightLogBad l δ ε n) ≤
      (Model.pathMeasure (rates n) n (2 * n + 1)).real (Y n ⁻¹' G) := by
    let μ := Model.pathMeasure (rates n) n (2 * n + 1)
    have h := (measureReal_mono (μ := μ) (hsub n) (measure_ne_top _ _)).trans
      (measureReal_union_le (μ := μ) _ _)
    change (Model.pathMeasure (rates n) n (2 * n + 1)).real
      (realThresholdEarlyTriple l δ n ⁻¹' B) ≤
      (Model.pathMeasure (rates n) n (2 * n + 1)).real (Y n ⁻¹' G) +
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (realThresholdHeightLogBad l δ ε n) at h
    linarith
  have hsum := hB.sub hbad
  simp only [sub_zero] at hsum
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal
      ((Model.pathMeasure (rates n) n (2 * n + 1)).real
        (realThresholdEarlyTriple l δ n ⁻¹' B) -
       (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (realThresholdHeightLogBad l δ ε n))) atTop
      (𝓝 (birthParentLaw (localEarlyTriple l ⁻¹' B))) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsum
    have htarget : ENNReal.ofReal
        (birthParentLaw.real (localEarlyTriple l ⁻¹' B)) =
        birthParentLaw (localEarlyTriple l ⁻¹' B) :=
      ENNReal.ofReal_toReal (measure_ne_top _ _)
    simpa only [Function.comp_def, htarget] using hh
  have hpoint (n : ℕ) :
      ENNReal.ofReal
        ((Model.pathMeasure (rates n) n (2 * n + 1)).real
          (realThresholdEarlyTriple l δ n ⁻¹' B) -
         (Model.pathMeasure (rates n) n (2 * n + 1)).real
          (realThresholdHeightLogBad l δ ε n)) ≤
        (Model.pathMeasure (rates n) n (2 * n + 1)) (Y n ⁻¹' G) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hliminf := (hlim.liminf_eq).symm.trans_le
    (Filter.liminf_le_liminf (Eventually.of_forall hpoint))
  have hmaplimit : (birthParentLaw.map (Z ∘ localEarlyTriple l)) G =
      birthParentLaw ((Z ∘ localEarlyTriple l) ⁻¹' G) :=
    Measure.map_apply_of_aemeasurable hgraph.aemeasurable_limit hG.measurableSet
  have hmapn (n : ℕ) :
      ((Model.pathMeasure (rates n) n (2 * n + 1)).map (Y n)) G =
      (Model.pathMeasure (rates n) n (2 * n + 1)) (Y n ⁻¹' G) :=
    Measure.map_apply (Model.FinitePath.measurable _ ) hG.measurableSet
  change (birthParentLaw.map (Z ∘ localEarlyTriple l)) G ≤
    liminf (fun n ↦ ((Model.pathMeasure (rates n) n (2 * n + 1)).map (Y n)) G) atTop
  rw [hmaplimit]
  simp_rw [hmapn]
  simpa only [B, preimage_comp] using hliminf

end HeightPaper.CountCoupling
