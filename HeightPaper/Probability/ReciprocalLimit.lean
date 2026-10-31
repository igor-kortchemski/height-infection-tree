module

public import HeightPaper.Probability.EarlyReciprocal
public import HeightPaper.Analysis.ReciprocalAsymptotics

/-!
# The actual epidemic reciprocal-count logarithmic coefficient

Sharp early count barriers pinch reciprocal sums between harmonic sums. The
initial fixed segment and the macroscopic late interval disappear at
logarithmic scale. All estimates retain the actual finite history law and its
terminal activity event.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

private theorem exists_sharp_reciprocal_parameters {l ε : ℝ} (hl : 1 < l) (hε : 0 < ε) :
    ∃ lo hi Rlo Rhi qlo qhi : ℝ,
      0 < lo ∧ 0 < hi ∧ 0 ≤ Rlo ∧ Rlo < l ∧ 1 ≤ Rhi ∧ l < Rhi ∧
      0 < qlo ∧ qlo ≤ 1 ∧ 1 ≤ qhi ∧
      geometricContraction Rlo qlo < qlo ^ lo ∧ geometricContraction Rhi qhi < qhi ^ hi ∧
      |1 / lo - (l + 1) / (l - 1)| < ε ∧ |1 / hi - (l + 1) / (l - 1)| < ε := by
  let d := (l - 1) / (l + 1)
  have hd : 0 < d := div_pos (sub_pos.mpr hl) (by linarith)
  have hcInv : ContinuousAt (fun x : ℝ ↦ 1 / x) d := continuousAt_const.div continuousAt_id hd.ne'
  have he : ∀ᶠ x : ℝ in 𝓝 d, |1 / x - 1 / d| < ε := by
    simpa only [Real.dist_eq] using hcInv.tendsto.eventually (Metric.ball_mem_nhds (1 / d) hε)
  have helo : ∀ᶠ x : ℝ in 𝓝[<] d, 0 < x ∧ x < d ∧ |1 / x - 1 / d| < ε := by
    filter_upwards [self_mem_nhdsWithin, he.filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds hd).filter_mono nhdsWithin_le_nhds] with x hx he hx0
    exact ⟨hx0, hx, he⟩
  obtain ⟨lo, hlo, hloD, hloClose⟩ := helo.exists
  have hehi : ∀ᶠ x : ℝ in 𝓝[>] d, d < x ∧ |1 / x - 1 / d| < ε := by
    filter_upwards [self_mem_nhdsWithin, he.filter_mono nhdsWithin_le_nhds] with x hx he
    exact ⟨hx, he⟩
  obtain ⟨hi, hhiD, hhiClose⟩ := hehi.exists
  have hhi : 0 < hi := hd.trans hhiD
  have hcDrift : ContinuousAt (fun R : ℝ ↦ (R - 1) / (R + 1)) l :=
    (continuousAt_id.sub continuousAt_const).div (continuousAt_id.add continuousAt_const) (by linarith)
  have hloNear := hcDrift.tendsto.eventually (Ioi_mem_nhds hloD)
  have hRloExists : ∀ᶠ R : ℝ in 𝓝[<] l, 1 < R ∧ R < l ∧ lo < (R - 1) / (R + 1) := by
    filter_upwards [self_mem_nhdsWithin, hloNear.filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds hl).filter_mono nhdsWithin_le_nhds] with R hRl hSlope hR
    exact ⟨hR, hRl, hSlope⟩
  obtain ⟨Rlo, hRlo1, hRloL, hSlopeLo⟩ := hRloExists.exists
  have hhiNear := hcDrift.tendsto.eventually (Iio_mem_nhds hhiD)
  have hRhiExists : ∀ᶠ R : ℝ in 𝓝[>] l, l < R ∧ (R - 1) / (R + 1) < hi := by
    filter_upwards [self_mem_nhdsWithin, hhiNear.filter_mono nhdsWithin_le_nhds] with R hRl hSlope
    exact ⟨hRl, hSlope⟩
  obtain ⟨Rhi, hRhiL, hSlopeHi⟩ := hRhiExists.exists
  have hRlo0 : 0 ≤ Rlo := (zero_lt_one.trans hRlo1).le
  have hRhi1 : 1 ≤ Rhi := (hl.trans hRhiL).le
  obtain ⟨qlo, hqlo, hqlo1, hqloSlope⟩ := exists_lower_count_parameter hRlo0 hSlopeLo
  obtain ⟨qhi, hqhi1, hqhiSlope⟩ := exists_upper_count_parameter (zero_le_one.trans hRhi1) hSlopeHi
  have hinv : 1 / d = (l + 1) / (l - 1) := by dsimp [d]; rw [one_div_div]
  rw [hinv] at hloClose hhiClose
  exact ⟨lo, hi, Rlo, Rhi, qlo, qhi, hlo, hhi, hRlo0, hRloL, hRhi1, hRhiL,
    hqlo, hqlo1.le, hqhi1.le, hqloSlope, hqhiSlope, hloClose, hhiClose⟩

private theorem natural_reciprocal_le_one (k : ℕ) : 1 / (k : ℝ) ≤ 1 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hkR

private theorem geometric_error_tendsto_zero {q ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun K : ℕ ↦ q * ρ ^ (K + 1) / (1 - ρ)) atTop (𝓝 0) := by
  have h := (((tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).comp
    (tendsto_add_atTop_nat 1)).const_mul q).div_const (1 - ρ)
  simpa only [Function.comp_apply, mul_zero, zero_div] using h

/-- The full reciprocal active-count sum has the exact logarithmic coefficient
`(l+1)/(l-1)` on surviving histories. Only the source rate scaling is assumed. -/
theorem path_reciprocal_sum_div_log_concentration
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (horizon n)).real
      {p | (p.eval (horizon n)).active.Nonempty ∧
        ε ≤ |(∑ k ∈ Finset.range (horizon n), 1 / (infectious (p.eval k) : ℝ)) / Real.log n -
          (l + 1) / (l - 1)|}) atTop (𝓝 0) := by
  have hsmall : 0 < ε / 8 := by positivity
  obtain ⟨lo, hi, Rlo, Rhi, qlo, qhi, hlo, hhi, hRlo, hRloL, hRhi, hRhiL,
    hqlo, hqlo1, hqhi, hcLo, hcHi, hloClose, hhiClose⟩ := exists_sharp_reciprocal_parameters hl hsmall
  have hl0 : 0 < l := zero_lt_one.trans hl
  have hfrac : 0 < 1 - Rlo / l := sub_pos.mpr ((div_lt_one hl0).mpr hRloL)
  let a := min T (1 - Rlo / l) / 2
  have ha : 0 < a := half_pos (lt_min hT.1 hfrac)
  have haT : a < T := by
    have hmin := min_le_left T (1 - Rlo / l)
    dsimp [a]
    linarith only [hmin, hT.1]
  have hafrac : a < 1 - Rlo / l := by have := min_le_right T (1 - Rlo / l); dsimp [a]; linarith
  have ha1 : a < 1 := by have := div_nonneg hRlo hl0.le; linarith
  have hPressureLimit : Rlo < l * (1 - a) := by
    have heq : (Rlo / l) * l = Rlo := div_mul_cancel₀ _ hl0.ne'
    nlinarith [mul_lt_mul_of_pos_left hafrac hl0]
  have hPressureLo := (tendsto_early_pressure rates ha.le ha1 hrates).eventually (Ioi_mem_nhds hPressureLimit)
  have hPressureHi := hrates.eventually (Iio_mem_nhds hRhiL)
  let ρlo := geometricContraction Rlo qlo / qlo ^ lo
  let ρhi := geometricContraction Rhi qhi / qhi ^ hi
  have hqhi0 : 0 < qhi := zero_lt_one.trans_le hqhi
  have hρlo : 0 ≤ ρlo := div_nonneg (geometricContraction_pos hRlo hqlo).le (Real.rpow_pos_of_pos hqlo lo).le
  have hρhi : 0 ≤ ρhi := div_nonneg (geometricContraction_pos (zero_le_one.trans hRhi) hqhi0).le (Real.rpow_pos_of_pos hqhi0 hi).le
  have hρlo1 : ρlo < 1 := (div_lt_one (Real.rpow_pos_of_pos hqlo lo)).mpr hcLo
  have hρhi1 : ρhi < 1 := (div_lt_one (Real.rpow_pos_of_pos hqhi0 hi)).mpr hcHi
  have hgeom := (geometric_error_tendsto_zero (q := qlo) hρlo hρlo1).add
    (geometric_error_tendsto_zero (q := qhi) hρhi hρhi1)
  simp only [add_zero] at hgeom
  have hlate := path_late_reciprocal_sum_div_log_tendsto_zero rates horizon hl ha haT hT.2 hrates hhorizon
    (show 0 < ε / 4 by positivity)
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  apply tendsto_order.mpr
  constructor
  · intro x hx
    exact Eventually.of_forall (fun _ ↦ hx.trans_le measureReal_nonneg)
  · intro ζ hζ
    obtain ⟨K, hKgeom⟩ := (hgeom.eventually (Iio_mem_nhds (half_pos hζ))).exists
    let harm : ℕ → ℝ := fun n ↦ ∑ k ∈ Finset.Ico (K + 1) ⌊a * n⌋₊, 1 / (k : ℝ)
    have hHarm : Tendsto (fun n ↦ harm n / Real.log n) atTop (𝓝 1) := by
      simpa only [harm, one_div] using tendsto_reciprocal_Ico_floor_div_log ha (K + 1)
    have hLoBound := (hHarm.div_const hi).eventually (Metric.ball_mem_nhds (1 / hi) hsmall)
    have hHiBound := (hHarm.div_const lo).eventually (Metric.ball_mem_nhds (1 / lo) hsmall)
    have hInitial := (hlog.const_div_atTop ((K + 1 : ℕ) : ℝ)).eventually
      (Iio_mem_nhds (show 0 < ε / 4 by positivity))
    filter_upwards [hPressureLo, hPressureHi, (tendsto_floor_fraction ha.le).eventually_lt hhorizon haT,
      (tendsto_nat_floor_mul_atTop a ha).eventually (eventually_ge_atTop (K + 1)),
      hLoBound, hHiBound, hInitial, hlate.eventually (Iio_mem_nhds (half_pos hζ)),
      eventually_gt_atTop 1] with n hnLo hnHi htime hK hnLow hnHigh hnInitial hnLate hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
    have htimeN : ⌊a * n⌋₊ ≤ horizon n := by exact_mod_cast ((div_lt_div_iff_of_pos_right hnR).mp htime).le
    simp only [Real.dist_eq] at hnLow hnHigh
    dsimp only [Function.comp_apply] at hnInitial
    let bad : Set (FinitePath (horizon n)) := {p | (p.eval (horizon n)).active.Nonempty ∧
      ((∑ k ∈ Finset.Ico (K + 1) ⌊a * n⌋₊, 1 / (infectious (p.eval k) : ℝ)) < harm n / hi ∨
        harm n / lo < ∑ k ∈ Finset.Ico (K + 1) ⌊a * n⌋₊, 1 / (infectious (p.eval k) : ℝ))}
    have hbad : (pathMeasure (rates n) n (horizon n)).real bad ≤
        qlo * ρlo ^ (K + 1) / (1 - ρlo) + qhi * ρhi ^ (K + 1) / (1 - ρhi) :=
      path_early_reciprocal_pinch_le (rates n) n ⌊a * n⌋₊ (horizon n) K htimeN lo hi hlo hhi
        hRlo hRhi hqlo hqlo1 hqhi hcLo hcHi hnLo.le hnHi.le
    have hmain : (pathMeasure (rates n) n (horizon n)).real
        {p | (p.eval (horizon n)).active.Nonempty ∧
          ε ≤ |(∑ k ∈ Finset.range (horizon n), 1 / (infectious (p.eval k) : ℝ)) / Real.log n - (l + 1) / (l - 1)|} ≤
        (pathMeasure (rates n) n (horizon n)).real bad +
          (pathMeasure (rates n) n (horizon n)).real
            {p | (p.eval (horizon n)).active.Nonempty ∧ ε / 4 ≤
              (∑ k ∈ Finset.Ico ⌊a * n⌋₊ (horizon n), 1 / (infectious (p.eval k) : ℝ)) / Real.log n} := by
      apply le_trans _ (measureReal_union_le _ _)
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro p hp
      by_cases hbadp : p ∈ bad
      · exact Or.inl hbadp
      · apply Or.inr
        refine ⟨hp.1, ?_⟩
        by_contra hlatep
        have hpinch : harm n / hi ≤ (∑ k ∈ Finset.Ico (K + 1) ⌊a * n⌋₊, 1 / (infectious (p.eval k) : ℝ)) ∧
            (∑ k ∈ Finset.Ico (K + 1) ⌊a * n⌋₊, 1 / (infectious (p.eval k) : ℝ)) ≤ harm n / lo := by
          constructor
          · exact le_of_not_gt (fun h ↦ hbadp ⟨hp.1, Or.inl h⟩)
          · exact le_of_not_gt (fun h ↦ hbadp ⟨hp.1, Or.inr h⟩)
        have hfirst : (∑ k ∈ Finset.range (K + 1), 1 / (infectious (p.eval k) : ℝ)) ≤ (K + 1 : ℕ) := by
          calc
            _ ≤ ∑ _k ∈ Finset.range (K + 1), (1 : ℝ) :=
              Finset.sum_le_sum (fun k _ ↦ natural_reciprocal_le_one (infectious (p.eval k)))
            _ = _ := by simp
        have hfirstNorm := div_le_div_of_nonneg_right hfirst hlogpos.le
        have hloNorm := div_le_div_of_nonneg_right hpinch.1 hlogpos.le
        have hhiNorm := div_le_div_of_nonneg_right hpinch.2 hlogpos.le
        have hcommHi : (harm n / hi) / Real.log n = (harm n / Real.log n) / hi := by ring
        have hcommLo : (harm n / lo) / Real.log n = (harm n / Real.log n) / lo := by ring
        rw [hcommHi] at hloNorm
        rw [hcommLo] at hhiNorm
        have hnonnegFirst : 0 ≤ (∑ k ∈ Finset.range (K + 1), 1 / (infectious (p.eval k) : ℝ)) / Real.log n := by positivity
        have hnonnegLate : 0 ≤ (∑ k ∈ Finset.Ico ⌊a * n⌋₊ (horizon n), 1 / (infectious (p.eval k) : ℝ)) / Real.log n := by positivity
        have hsplit : (∑ k ∈ Finset.range (horizon n), 1 / (infectious (p.eval k) : ℝ)) / Real.log n =
            (∑ k ∈ Finset.range (K + 1), 1 / (infectious (p.eval k) : ℝ)) / Real.log n +
            (∑ k ∈ Finset.Ico (K + 1) ⌊a * n⌋₊, 1 / (infectious (p.eval k) : ℝ)) / Real.log n +
            (∑ k ∈ Finset.Ico ⌊a * n⌋₊ (horizon n), 1 / (infectious (p.eval k) : ℝ)) / Real.log n := by
          rw [← Finset.sum_range_add_sum_Ico _ htimeN, ← Finset.sum_range_add_sum_Ico _ hK,
            add_div, add_div]
        have hloNear := (abs_lt.mp hhiClose).1
        have hhiNear := (abs_lt.mp hloClose).2
        have hLoErr := (abs_lt.mp hnLow).1
        have hHiErr := (abs_lt.mp hnHigh).2
        have hLateLt := lt_of_not_ge hlatep
        have herr : |(∑ k ∈ Finset.range (horizon n), 1 / (infectious (p.eval k) : ℝ)) / Real.log n -
            (l + 1) / (l - 1)| < ε := by
          apply abs_lt.mpr
          constructor
          · linarith only [hsplit, hnonnegFirst, hnonnegLate, hloNorm, hloNear, hLoErr, hε]
          · linarith only [hsplit, hfirstNorm, hnInitial, hhiNorm, hhiNear, hHiErr, hLateLt, hε]
        exact not_lt_of_ge hp.2 herr
    linarith only [hmain, hbad, hKgeom, hnLate]

end HeightPaper.Model
