module

public import HeightPaper.Probability.FluidLocation
public import HeightPaper.Probability.EpidemicMoments
public import HeightPaper.Probability.ExtinctionTimes

/-!
# Extinction probability before fluid extinction

The geometric test function identifies the early extinction mass. The exact
clock excludes extinct states whose genuine event count lies in a compact
subinterval before fluid extinction, and so transfers that mass to every
strictly intermediate deterministic event time.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal

namespace HeightPaper

/-- The deterministic infectious curve has a strictly positive lower bound on
every closed interval strictly between its two zeros. -/
theorem fluidInfectiousRaw_uniform_pos {l a b : ℝ} (hl : 1 < l)
    (ha : 0 < a) (hb : b < fluidExtinctionTime l) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc a b, c ≤ fluidInfectiousRaw l t := by
  apply isCompact_Icc.exists_forall_le' (continuous_fluidInfectiousRaw hl).continuousOn
  intro t ht
  exact fluidInfectiousRaw_pos hl ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩

namespace Model

/-- At an extinct state the fluid infectious value at the genuine event count
is controlled by the susceptible clock residual. -/
theorem extinct_fluidInfectiousRaw_le_clock_error {l : ℝ} (hl : 1 < l)
    {n : ℕ} (hn : 0 < n) {s : State} (hpop : s.vertices + s.susceptible = n + 1)
    (hz : infectious s = 0) (hH : 0 < s.susceptible) :
    fluidInfectiousRaw l ((eventCount s : ℝ) / n) ≤
      2 * |fluidClock l ((s.susceptible : ℝ) / n) - (eventCount s : ℝ) / n| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 2 * (s.susceptible : ℝ) + eventCount s = 2 * n + 1 := by
    have hh := count_balance hpop
    rw [hz, zero_add] at hh
    exact_mod_cast hh
  have heq : fluidInfectiousRaw l ((eventCount s : ℝ) / n) =
      2 * ((s.susceptible : ℝ) / n - fluidSusceptible l ((eventCount s : ℝ) / n)) - 1 / n := by
    unfold fluidInfectiousRaw
    field_simp
    nlinarith
  have hinv := abs_sub_fluidSusceptible_le (t := (eventCount s : ℝ) / n) hl
    (show (0 : ℝ) < (s.susceptible : ℝ) / n by positivity)
  rw [heq]
  have hninv : (0 : ℝ) ≤ 1 / n := by positivity
  have hh := le_abs_self ((s.susceptible : ℝ) / n - fluidSusceptible l ((eventCount s : ℝ) / n))
  linarith

/-- Extinction with a nonzero macroscopic genuine event count before the fluid
extinction time has probability tending to zero. -/
theorem evolve_late_extinction_tendsto_zero
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T δ : ℝ} (hl : 1 < l)
    (hδ : 0 < δ) (hT : T < fluidExtinctionTime l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
      {s | infectious s = 0 ∧ δ ≤ (eventCount s : ℝ) / n}) atTop (𝓝 0) := by
  let B := (T + fluidExtinctionTime l) / 2
  have hTB : T < B := by dsimp [B]; linarith
  have hBt : B < fluidExtinctionTime l := by dsimp [B]; linarith
  have hB2 : B < 2 := hBt.trans (fluidExtinctionTime_lt_two hl)
  obtain ⟨c, hc, hlower⟩ := fluidInfectiousRaw_uniform_pos hl hδ hBt
  have hconc := evolve_fluidClock_concentration rates horizon hl hrates hhorizon (half_pos hc)
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hconc
  filter_upwards [hhorizon.eventually (Iio_mem_nhds hTB), eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {s : State |
    infectious s = 0 ∧ δ ≤ (eventCount s : ℝ) / n} from trivial)
  intro s hs
  have he : (eventCount s : ℝ) / n < B :=
    (div_le_div_of_nonneg_right (by exact_mod_cast evolve_eventCount_le hs.2) hnR.le).trans_lt hn
  have hH : 0 < s.susceptible := by
    by_contra hH
    have hH0 : s.susceptible = 0 := Nat.eq_zero_of_not_pos hH
    have hb : (eventCount s : ℝ) = 2 * n + 1 := by
      have hh := count_balance (evolve_population hs.2)
      rw [hs.1.1, hH0] at hh
      simpa using (show (0 : ℝ) + 2 * 0 + eventCount s = 2 * n + 1 by exact_mod_cast hh)
    have he' := (div_lt_iff₀ hnR).mp he
    nlinarith [mul_pos (sub_pos.mpr hB2) hnR]
  have hf := hlower ((eventCount s : ℝ) / n) ⟨hs.1.2, he.le⟩
  have hb := extinct_fluidInfectiousRaw_le_clock_error hl hn0
    (evolve_population hs.2) hs.1.1 hH
  change c / 2 ≤ |fluidClock l ((s.susceptible : ℝ) / n) - (eventCount s : ℝ) / n|
  linarith

/-- Any number strictly below `1/l` is eventually below the actual extinction
probability at a strictly intermediate event time. -/
theorem eventually_lt_extinction_of_lt_reciprocal
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T a : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    (ha : a < 1 / l) :
    ∀ᶠ n : ℕ in atTop, a < (evolve (rates n) n (horizon n)).toMeasure.real
      {s | infectious s = 0} := by
  have hl0 : 0 < l := zero_lt_one.trans hl
  have hi0 : 0 < 1 / l := one_div_pos.mpr hl0
  have hi1 : 1 / l < 1 := (div_lt_one hl0).mpr hl
  obtain ⟨q, hqlo, hqhi⟩ := exists_between (max_lt ha hi0)
  have hq : 0 < q := (le_max_right a 0).trans_lt hqlo
  have haq : a < q := (le_max_left a 0).trans_lt hqlo
  have hq1 : q < 1 := hqhi.trans hi1
  have hp : l * q < 1 := by
    have h := (lt_div_iff₀ hl0).mp hqhi
    simpa only [mul_comm] using h
  have hgap : 0 < (q - a) / 2 := half_pos (sub_pos.mpr haq)
  obtain ⟨M, hM⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).eventually
    (Iio_mem_nhds hgap)).exists
  have hsmall := evolve_small_active_tendsto_zero rates horizon hl hT hrates hhorizon M
  filter_upwards [(hrates.mul_const q).eventually (Iio_mem_nhds hp),
    hsmall.eventually (Iio_mem_nhds hgap)] with n hn hs
  have hb := evolve_extinction_lower_bound (rates n) n (horizon n) M hq hq1.le hn.le
  linarith

/-- A prescribed geometric superharmonic parameter bounds extinction at all
strictly intermediate times, up to an arbitrarily small vanishing error. -/
theorem eventually_extinction_lt_of_reciprocal_lt
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T b : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    (hb : 1 / l < b) :
    ∀ᶠ n : ℕ in atTop, (evolve (rates n) n (horizon n)).toMeasure.real
      {s | infectious s = 0} < b := by
  have hl0 : 0 < l := zero_lt_one.trans hl
  have hi0 : 0 < 1 / l := one_div_pos.mpr hl0
  have hi1 : 1 / l < 1 := (div_lt_one hl0).mpr hl
  obtain ⟨q, hqlo, hqhi⟩ := exists_between (lt_min hb hi1)
  have hq : 0 < q := hi0.trans hqlo
  have hq1 : q < 1 := hqhi.trans_le (min_le_right b 1)
  have hqb : q < b := hqhi.trans_le (min_le_left b 1)
  have hprod : 1 < l * q := by
    have h := (div_lt_iff₀ hl0).mp hqlo
    simpa only [mul_comm] using h
  have hprod0 : 0 < l * q := zero_lt_one.trans hprod
  obtain ⟨c, hclo, hc1⟩ := exists_between ((div_lt_one hprod0).mpr hprod)
  have hc : 0 < c := (one_div_pos.mpr hprod0).trans hclo
  have hpressure : 1 < l * c * q := by
    have h := (div_lt_iff₀ hprod0).mp hclo
    nlinarith
  let δ := min T (1 - c) / 2
  have hmin : 0 < min T (1 - c) := lt_min hT.1 (sub_pos.mpr hc1)
  have hδ : 0 < δ := half_pos hmin
  have hδT : δ < T := by
    have h := min_le_left T (1 - c)
    dsimp [δ]
    linarith
  have hsum : δ + c < 1 := by
    have h := min_le_right T (1 - c)
    dsimp [δ]
    linarith
  have hearly := tendsto_floor_fraction hδ.le
  have hthreshold := tendsto_fluidThreshold_fraction hc.le
  have hlate := evolve_late_extinction_tendsto_zero rates horizon hl hδ hT.2 hrates hhorizon
  have hp := (tendsto_fluidThreshold_pressure rates hc.le hrates).mul_const q
  filter_upwards [(hearly.add hthreshold).eventually (Iio_mem_nhds hsum),
    hearly.eventually_lt hhorizon hδT, hp.eventually (Ioi_mem_nhds hpressure),
    hlate.eventually (Iio_mem_nhds (sub_pos.mpr hqb)), eventually_gt_atTop 0]
    with n hn htime hnpressure hnlate hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsumN : ⌊δ * n⌋₊ + fluidThreshold c n ≤ n := by
    have hsumR : (⌊δ * n⌋₊ : ℝ) + fluidThreshold c n < n := by
      rw [← add_div] at hn
      exact (div_lt_one hnR).mp hn
    exact_mod_cast hsumR.le
  have htimeN : ⌊δ * n⌋₊ ≤ horizon n := by
    have hh := (div_lt_div_iff_of_pos_right hnR).mp htime
    exact_mod_cast hh.le
  have he := evolve_early_extinction_le (rates n) (fluidThreshold c n) n ⌊δ * n⌋₊
    (fluidThreshold_pos c n) hsumN hq hq1.le hnpressure.le
  have hcomp := evolve_extinction_le_earlier_add_late (rates n) n htimeN
  have hlatebound : (evolve (rates n) n (horizon n)).toMeasure.real
      {s | infectious s = 0 ∧ ⌊δ * n⌋₊ < eventCount s} ≤
      (evolve (rates n) n (horizon n)).toMeasure.real
      {s | infectious s = 0 ∧ δ ≤ (eventCount s : ℝ) / n} := by
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro s hs
    refine ⟨hs.1, ?_⟩
    apply (le_div_iff₀ hnR).mpr
    have hh : (⌊δ * n⌋₊ : ℝ) + 1 ≤ eventCount s := by exact_mod_cast hs.2
    exact (Nat.lt_floor_add_one (δ * n)).le.trans hh
  linarith

/-- At every fixed event time strictly between zero and fluid extinction, the
actual finite SIR extinction probability converges to `1/l`. The rate sequence
need only satisfy the paper's scaling assumption. -/
theorem evolve_extinction_tendsto_reciprocal
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
      {s | infectious s = 0}) atTop (𝓝 (1 / l)) := by
  apply tendsto_order.mpr
  exact ⟨fun a ha ↦ eventually_lt_extinction_of_lt_reciprocal rates horizon hl hT hrates hhorizon ha,
    fun b hb ↦ eventually_extinction_lt_of_reciprocal_lt rates horizon hl hT hrates hhorizon hb⟩

end Model
end HeightPaper
