module

public import HeightPaper.Probability.UniformReciprocal
public import HeightPaper.Probability.EarlyCountLower
public import HeightPaper.Probability.EarlyExtinctionTightness

/-!
# Whole-history quadratic reciprocal remainders

A fixed short initial interval has uniformly supercritical infection pressure.
The geometric small-count estimate controls its reciprocal-square tail; the
macroscopic estimates control the remaining interval. Their combination makes
the complete quadratic remainder negligible at logarithmic scale.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

/-- An early bad-count event viewed inside a longer actual epidemic history. -/
def earlySmallActiveOnFull (c : ℝ) (K early horizon : ℕ) : Set (FinitePath horizon) :=
  ⋃ k ∈ Finset.Ico K (early + 1), {p | p.eval k ∈ smallActiveCount c k}

theorem pathMeasure_earlySmallActiveOnFull_le (rate : ℝ≥0) (n early horizon K : ℕ)
    (hearly : early ≤ horizon) (c : ℝ) {R q : ℝ} (hR : 0 ≤ R) (hq : 0 < q) (hq1 : q ≤ 1)
    (hc : geometricContraction R q < q ^ c)
    (hpressure : R ≤ (rate : ℝ) * (n - early : ℕ)) :
    (pathMeasure rate n horizon).real (earlySmallActiveOnFull c K early horizon) ≤
      q * (geometricContraction R q / q ^ c) ^ K /
        (1 - geometricContraction R q / q ^ c) := by
  have hρ : 0 ≤ geometricContraction R q / q ^ c :=
    div_nonneg (geometricContraction_pos hR hq).le (Real.rpow_pos_of_pos hq c).le
  have hρ1 : geometricContraction R q / q ^ c < 1 :=
    (div_lt_one (Real.rpow_pos_of_pos hq c)).mpr hc
  calc
    _ ≤ ∑ k ∈ Finset.Ico K (early + 1),
        (pathMeasure rate n horizon).real {p | p.eval k ∈ smallActiveCount c k} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.Ico K (early + 1), q * (geometricContraction R q / q ^ c) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkE : k ≤ early := by have := (Finset.mem_Ico.mp hk).2; omega
      rw [pathMeasure_event_at rate n horizon k (hkE.trans hearly)]
      exact evolve_smallActiveCount_le rate n early k c hR hq hq1 hpressure hkE
    _ = q * ∑ k ∈ Finset.Ico K (early + 1), (geometricContraction R q / q ^ c) ^ k := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (geom_sum_Ico_le_of_lt_one (m := K) (n := early + 1) hρ hρ1) hq.le
      simpa only [mul_div_assoc] using hh

private theorem natural_inv_square_le_one (k : ℕ) : ((k : ℝ) ^ 2)⁻¹ ≤ 1 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have hs : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs

/-- All early quadratic reciprocal terms are bounded off the geometric bad
event, with the constant depending only on the fixed starting-tail index. -/
theorem early_reciprocalSquare_sum_le (c : ℝ) (hc : 0 < c) (K early horizon : ℕ)
    (hK : K ≤ early) (p : FinitePath horizon)
    (hp : p ∉ earlySmallActiveOnFull c (K + 1) early horizon) :
    (∑ k ∈ Finset.range (early + 1), ((infectious (p.eval k) : ℝ) ^ 2)⁻¹) ≤
      (K + 1 : ℕ) + 2 / (c ^ 2 * (K + 1)) := by
  let shortPath : FinitePath early := ⟨fun i ↦ p.eval i.val⟩
  have heval (k : ℕ) (hk : k ≤ early) : shortPath.eval k = p.eval k := by
    change p.eval (min k early) = p.eval k
    rw [Nat.min_eq_left hk]
  have hprefix : shortPath ∉ earlySmallActivePaths c (K + 1) early := by
    intro h
    obtain ⟨k, hk, hm⟩ := mem_iUnion₂.mp h
    have hke : k ≤ early := by have := (Finset.mem_Ico.mp hk).2; omega
    change shortPath.eval k ∈ smallActiveCount c k at hm
    rw [heval k hke] at hm
    apply hp
    exact mem_iUnion₂.mpr ⟨k, hk, hm⟩
  have htail := reciprocalSquare_tail_le_of_no_small c hc K early shortPath hprefix
  have hinterval : Finset.Ioo K (early + 1) = Finset.Ico (K + 1) (early + 1) := by
    ext k
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  rw [hinterval] at htail
  have htail' : (∑ k ∈ Finset.Ico (K + 1) (early + 1), ((infectious (p.eval k) : ℝ) ^ 2)⁻¹) ≤
      2 / (c ^ 2 * (K + 1)) := by
    convert htail using 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [heval k (by have := (Finset.mem_Ico.mp hk).2; omega)]
  have hfirst : (∑ k ∈ Finset.range (K + 1), ((infectious (p.eval k) : ℝ) ^ 2)⁻¹) ≤ (K + 1 : ℕ) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range (K + 1), (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ ↦ natural_inv_square_le_one (infectious (p.eval k)))
      _ = _ := by simp
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : K + 1 ≤ early + 1)]
  exact add_le_add hfirst htail'

/-- Some fixed positive fraction of a surviving macroscopic horizon remains
uniformly supercritical, for every allowed rate sequence. -/
theorem exists_supercritical_early_window (rates : ℕ → ℝ≥0) {l T : ℝ}
    (hl : 1 < l) (hT : 0 < T)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∃ a ∈ Ioo (0 : ℝ) T, ∃ R q c : ℝ,
      0 ≤ R ∧ 0 < q ∧ q < 1 ∧ 0 < c ∧ geometricContraction R q < q ^ c ∧
      ∀ᶠ n : ℕ in atTop, R ≤ (rates n : ℝ) * (n - ⌊a * n⌋₊ : ℕ) := by
  have hl0 : 0 < l := zero_lt_one.trans hl
  obtain ⟨R, hR1, hRl⟩ := exists_between hl
  have hR : 0 < R := zero_lt_one.trans hR1
  have hfrac : 0 < 1 - R / l := sub_pos.mpr ((div_lt_one hl0).mpr hRl)
  let a := min T (1 - R / l) / 2
  have ha : 0 < a := half_pos (lt_min hT hfrac)
  have haT : a < T := by have := min_le_left T (1 - R / l); dsimp [a]; linarith
  have hafrac : a < 1 - R / l := by
    have := min_le_right T (1 - R / l)
    dsimp [a]
    linarith
  have ha1 : a < 1 := by have := div_pos hR hl0; linarith
  have hpressure : R < l * (1 - a) := by
    have hdiv : (R / l) * l = R := div_mul_cancel₀ _ hl0.ne'
    nlinarith [mul_lt_mul_of_pos_left hafrac hl0]
  obtain ⟨q, hqlo, hq1⟩ := exists_between ((div_lt_one hR).mpr hR1)
  have hq : 0 < q := (one_div_pos.mpr hR).trans hqlo
  have hRq : 1 < R * q := by have := (div_lt_iff₀ hR).mp hqlo; nlinarith
  obtain ⟨c, hc, hcg⟩ := exists_positive_count_slope hR.le hq hq1 hRq
  refine ⟨a, ⟨ha, haT⟩, R, q, c, hR.le, hq, hq1, hc, hcg, ?_⟩
  exact ((tendsto_early_pressure rates ha.le ha1 hrates).eventually (Ioi_mem_nhds hpressure)).mono
    (fun _ h ↦ h.le)

/-- The late reciprocal sum is negligible after logarithmic normalization. -/
theorem path_late_reciprocal_sum_div_log_tendsto_zero
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l a T : ℝ} (hl : 1 < l)
    (ha : 0 < a) (haT : a < T) (hT : T < fluidExtinctionTime l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (horizon n)).real
      {p | (p.eval (horizon n)).active.Nonempty ∧
        ε ≤ (∑ k ∈ Finset.Ico ⌊a * n⌋₊ (horizon n), 1 / (infectious (p.eval k) : ℝ)) / Real.log n})
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := path_late_reciprocal_sum_bounded rates horizon hl ha haT hT hrates hhorizon
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hbound
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  filter_upwards [(hlog.const_mul_atTop hε).eventually (eventually_gt_atTop C),
    eventually_gt_atTop 1] with n hn hn1
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro p hp
  exact ⟨hp.1, hn.le.trans ((le_div_iff₀ hlogpos).mp hp.2)⟩

/-- The whole reciprocal-square sum, from the initial infectious individual
through a macroscopic surviving horizon, is negligible at logarithmic scale. -/
theorem path_reciprocal_square_sum_div_log_tendsto_zero
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (horizon n)).real
      {p | (p.eval (horizon n)).active.Nonempty ∧
        ε ≤ (∑ k ∈ Finset.range (horizon n), ((infectious (p.eval k) : ℝ) ^ 2)⁻¹) / Real.log n})
      atTop (𝓝 0) := by
  obtain ⟨a, ha, R, q, c, hR, hq, hq1, hc, hcg, hpressure⟩ :=
    exists_supercritical_early_window rates hl hT.1 hrates
  let ρ := geometricContraction R q / q ^ c
  have hρ : 0 ≤ ρ := div_nonneg (geometricContraction_pos hR hq).le (Real.rpow_pos_of_pos hq c).le
  have hρ1 : ρ < 1 := (div_lt_one (Real.rpow_pos_of_pos hq c)).mpr hcg
  have hgeom : Tendsto (fun K : ℕ ↦ q * ρ ^ (K + 1) / (1 - ρ)) atTop (𝓝 0) := by
    have hh := (((tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).comp (tendsto_add_atTop_nat 1)).const_mul q).div_const (1 - ρ)
    simpa only [Function.comp_apply, mul_zero, zero_div] using hh
  have hlate : Tendsto (fun n ↦ (pathMeasure (rates n) n (horizon n)).real
      {p | (p.eval (horizon n)).active.Nonempty ∧
        1 ≤ ∑ k ∈ Finset.Ico ⌊a * n⌋₊ (horizon n), ((infectious (p.eval k) : ℝ) ^ 2)⁻¹}) atTop (𝓝 0) := by
    simpa only [one_div] using path_late_reciprocal_square_sum_tendsto_zero rates horizon hl ha.1 ha.2 hT.2 hrates hhorizon (by norm_num : (0 : ℝ) < 1)
  apply tendsto_order.mpr
  constructor
  · intro x hx
    exact Eventually.of_forall (fun _ ↦ hx.trans_le measureReal_nonneg)
  · intro ζ hζ
    obtain ⟨K, hKgeom⟩ := (hgeom.eventually (Iio_mem_nhds (half_pos hζ))).exists
    let B := (K + 1 : ℕ) + 2 / (c ^ 2 * (K + 1)) + 1
    have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
    filter_upwards [hpressure, (tendsto_floor_fraction ha.1.le).eventually_lt hhorizon ha.2,
      (tendsto_nat_floor_mul_atTop a ha.1).eventually (eventually_ge_atTop K),
      (hlog.const_mul_atTop hε).eventually (eventually_gt_atTop B),
      hlate.eventually (Iio_mem_nhds (half_pos hζ)), eventually_gt_atTop 1]
      with n hnpressure htime hK hB hnlate hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have htimeN : ⌊a * n⌋₊ ≤ horizon n := by exact_mod_cast ((div_lt_div_iff_of_pos_right hnR).mp htime).le
    have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
    have hbadbound := pathMeasure_earlySmallActiveOnFull_le (rates n) n ⌊a * n⌋₊ (horizon n)
      (K + 1) htimeN c hR hq hq1.le hcg hnpressure
    have hmain : (pathMeasure (rates n) n (horizon n)).real
        {p | (p.eval (horizon n)).active.Nonempty ∧
          ε ≤ (∑ k ∈ Finset.range (horizon n), ((infectious (p.eval k) : ℝ) ^ 2)⁻¹) / Real.log n} ≤
        (pathMeasure (rates n) n (horizon n)).real (earlySmallActiveOnFull c (K + 1) ⌊a * n⌋₊ (horizon n)) +
        (pathMeasure (rates n) n (horizon n)).real
          {p | (p.eval (horizon n)).active.Nonempty ∧
            1 ≤ ∑ k ∈ Finset.Ico ⌊a * n⌋₊ (horizon n), ((infectious (p.eval k) : ℝ) ^ 2)⁻¹} := by
      apply le_trans _ (measureReal_union_le _ _)
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro p hp
      by_cases he : p ∈ earlySmallActiveOnFull c (K + 1) ⌊a * n⌋₊ (horizon n)
      · exact Or.inl he
      · apply Or.inr
        refine ⟨hp.1, ?_⟩
        by_contra hlater
        have hfirst := early_reciprocalSquare_sum_le c hc K ⌊a * n⌋₊ (horizon n) hK p he
        have hprefix : (∑ k ∈ Finset.range ⌊a * n⌋₊, ((infectious (p.eval k) : ℝ) ^ 2)⁻¹) ≤
            (∑ k ∈ Finset.range (⌊a * n⌋₊ + 1), ((infectious (p.eval k) : ℝ) ^ 2)⁻¹) := by
          rw [Finset.sum_range_succ]
          have hh : 0 ≤ ((infectious (p.eval ⌊a * n⌋₊) : ℝ) ^ 2)⁻¹ := by positivity
          linarith
        have hsum := Finset.sum_range_add_sum_Ico
          (fun k ↦ ((infectious (p.eval k) : ℝ) ^ 2)⁻¹) htimeN
        have hpbound := (le_div_iff₀ hlogpos).mp hp.2
        dsimp [B] at hB
        have hlt := lt_of_not_ge hlater
        linarith
    dsimp [ρ] at hKgeom
    linarith

end HeightPaper.Model
