module

public import HeightPaper.Model.GoodProductWords
public import HeightPaper.Model.UniformProfileLower
public import HeightPaper.Probability.EventWordAveraging
public import HeightPaper.Analysis.LogCounts

/-!
# Averaging uniform lower profiles under the actual epidemic law

The finite prescribed-word bootstrap is averaged over the actual epidemic
using the proved good-count probability control and exact word factorization.
The initial cutoff and all polynomial constants are fixed before the population
limit. A positive linear horizon then has the same logarithmic scale as `n`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper

theorem tendsto_horizon_atTop_of_fraction_pos (horizon : ℕ → ℕ) {T : ℝ} (hT : 0 < T)
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    Tendsto horizon atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have hh := Tendsto.pos_mul_atTop hT hhorizon
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

namespace Model

/-- Uniform prescribed-word lower estimates yield actual epidemic lower
power tails. All probability inputs needed to select good words are proved. -/
theorem path_normalizedLaplace_power_lower_of_uniform
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T lo hi x a : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hlo : 0 < lo) (hloD : lo < (l - 1) / (l + 1)) (hhiD : (l - 1) / (l + 1) < hi)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    (hUniform : ∀ c > (0 : ℝ), ∀ A B : ℝ → ℝ,
      (∀ w ≥ (1 : ℝ), 0 < A w ∧ 0 < B w) → ∀ K : ℕ, 1 ≤ K →
      UniformProfileLower (GoodProductWord ((1 + 1 / hi) / 2) ((1 + 1 / lo) / 2) c A B K) x a) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (pathMeasure (rates n) n (horizon n)).real
      {p | p.last.active.Nonempty ∧
        realNormalizedLaplace x p.last < (horizon n : ℝ) ^ (a - ε)}) atTop (𝓝 0) := by
  have hN := tendsto_horizon_atTop_of_fraction_pos horizon hT.1 hhorizon
  have hhi : 0 < hi := (div_pos (sub_pos.mpr hl) (by linarith)).trans hhiD
  obtain ⟨early, α, c, L, hα, hc, hL, hgood⟩ :=
    exists_goodCountWord_probability_control rates horizon hl hT hlo hloD hhiD hrates hhorizon
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro z hz
    exact Eventually.of_forall fun _ ↦ hz.trans_le measureReal_nonneg
  · intro ζ hζ
    obtain ⟨K, hK, hKe⟩ := hgood (ζ / 2) (half_pos hζ)
    obtain ⟨A, B, hAB, hconvert⟩ := exists_goodProductWord_constants
      (c := c) (L := L) hlo hhi hα K hK
    have htail := hN.eventually (hUniform c hc A B hAB K hK ε hε (ζ / 2) (half_pos hζ))
    filter_upwards [hKe, htail] with n hn htailn
    let G := GoodProductWord ((1 + 1 / hi) / 2) ((1 + 1 / lo) / 2) c A B K (horizon n)
    have hword : (pathMeasure (rates n) n (horizon n)).real
        {p | p.last.active.Nonempty ∧ G (observedBirth p.eval) ∧
          realNormalizedLaplace x p.last < (horizon n : ℝ) ^ (a - ε)} ≤ ζ / 2 := by
      apply pathMeasure_positive_eventWord_bound (rates n) n (horizon n) G
        (fun _ ↦ {p | realNormalizedLaplace x p.last < (horizon n : ℝ) ^ (a - ε)})
        (half_pos hζ).le
      intro events _ hG
      exact htailn n events hG
    have hmain : (pathMeasure (rates n) n (horizon n)).real
        {p | p.last.active.Nonempty ∧ realNormalizedLaplace x p.last < (horizon n : ℝ) ^ (a - ε)} ≤
      (pathMeasure (rates n) n (horizon n)).real
        {p | p.last.active.Nonempty ∧ ¬GoodCountWord lo hi c L K (early n) (horizon n) (observedBirth p.eval)} +
      (pathMeasure (rates n) n (horizon n)).real
        {p | p.last.active.Nonempty ∧ G (observedBirth p.eval) ∧
          realNormalizedLaplace x p.last < (horizon n : ℝ) ^ (a - ε)} := by
      apply le_trans _ (measureReal_union_le _ _)
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply PMF.toMeasure_mono _ (show MeasurableSet {p : FinitePath (horizon n) |
        p.last.active.Nonempty ∧ realNormalizedLaplace x p.last < (horizon n : ℝ) ^ (a - ε)} from trivial)
      intro p hp
      by_cases hg : GoodCountWord lo hi c L K (early n) (horizon n) (observedBirth p.eval)
      · right
        refine ⟨hp.1.1, ?_, hp.1.2⟩
        have hpath := (mem_support_pathLaw_iff p).mp hp.2
        have haN : (p.eval (horizon n)).active.Nonempty := by rw [FinitePath.eval_last]; exact hp.1.1
        exact hconvert _ (early n) (horizon n) hn.1 hn.2.1 hn.2.2.1
          (fun k hk ↦ hpath.observedWalk_pos haN hk) hg
      · exact Or.inl ⟨hp.1.1, hg⟩
    linarith only [hmain, hword, hn.2.2.2]

/-- Conversion to the source logarithmic population scale. The statement is
at the same exponent supplied by the uniform prescribed-word bootstrap. -/
theorem path_normalizedLaplace_log_lower_of_uniform
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T lo hi x a : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l)) (hx : 0 ≤ x)
    (hlo : 0 < lo) (hloD : lo < (l - 1) / (l + 1)) (hhiD : (l - 1) / (l + 1) < hi)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    (hUniform : ∀ c > (0 : ℝ), ∀ A B : ℝ → ℝ,
      (∀ w ≥ (1 : ℝ), 0 < A w ∧ 0 < B w) → ∀ K : ℕ, 1 ≤ K →
      UniformProfileLower (GoodProductWord ((1 + 1 / hi) / 2) ((1 + 1 / lo) / 2) c A B K) x a) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (pathMeasure (rates n) n (horizon n)).real
      {p | p.last.active.Nonempty ∧
        ε ≤ a - Real.log (realNormalizedLaplace x p.last) / Real.log n}) atTop (𝓝 0) := by
  intro ε hε
  have hN := tendsto_horizon_atTop_of_fraction_pos horizon hT.1 hhorizon
  have hlog := tendsto_log_ratio_one_of_div_pos
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop) hT.1 hhorizon
  have hscale := hlog.const_mul (a - ε / 2)
  simp only [mul_one] at hscale
  have htail := path_normalizedLaplace_power_lower_of_uniform rates horizon hl hT hlo hloD hhiD
    hrates hhorizon hUniform (ε / 2) (half_pos hε)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ htail
  filter_upwards [hscale.eventually (Ioi_mem_nhds (show a - ε < a - ε / 2 by linarith)),
    eventually_gt_atTop 1, hN.eventually (eventually_gt_atTop 0)] with n hn hn1 hN0
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hNR : (0 : ℝ) < horizon n := by exact_mod_cast hN0
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro p hp
  refine ⟨hp.1, ?_⟩
  have hF : 0 < realNormalizedLaplace x p.last :=
    zero_lt_one.trans_le (one_le_realNormalizedLaplace hx p.last hp.1)
  have hlogBound : Real.log (realNormalizedLaplace x p.last) / Real.log n ≤ a - ε := by
    linarith only [hp.2]
  have hlogLt : Real.log (realNormalizedLaplace x p.last) < (a - ε / 2) * Real.log (horizon n) := by
    apply (div_lt_div_iff_of_pos_right hlogn).mp
    simpa only [mul_div_assoc] using hlogBound.trans_lt hn
  rw [Real.rpow_def_of_pos hNR]
  have he := Real.exp_lt_exp.mpr hlogLt
  rw [Real.exp_log hF] at he
  simpa only [mul_comm] using he

end Model
end HeightPaper
