module

public import HeightPaper.Analysis.FluidBarrier

/-!
# Locating active epidemic states on the fluid curve

The exact invariant and the logarithmic clock locate the susceptible and active
counts at any deterministic linear event time, on the event of nonextinction.
No survival-probability or fluid-limit theorem is an input.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology NNReal

namespace HeightPaper

theorem fluidClock_parameter_sub {l r s : ℝ} (hl : l ≠ 0) (hr : r ≠ 0) :
    fluidClock l s - fluidClock r s = Real.log s * (1 / r - 1 / l) := by
  unfold fluidClock
  field_simp
  ring

/-- The inverse clock expands distances by at least one on positive fractions. -/
theorem abs_sub_le_abs_fluidClock_sub {l x y : ℝ} (hl : 0 < l) (hx : 0 < x) (hy : 0 < y) :
    |x - y| ≤ |fluidClock l x - fluidClock l y| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm x y, abs_sub_comm (fluidClock l x) (fluidClock l y)]
    exact this hy hx (le_of_not_ge hxy)
  have hlog := Real.log_le_log hx hxy
  have heq : fluidClock l x - fluidClock l y = y - x + (Real.log y - Real.log x) / l := by
    unfold fluidClock
    field_simp
    ring
  rw [heq, abs_of_nonpos (sub_nonpos.mpr hxy)]
  have hd : 0 ≤ (Real.log y - Real.log x) / l := div_nonneg (sub_nonneg.mpr hlog) hl.le
  exact (show -(x - y) ≤ y - x + (Real.log y - Real.log x) / l by linarith).trans
    (le_abs_self _)

theorem abs_sub_fluidSusceptible_le {l t x : ℝ} (hl : 1 < l) (hx : 0 < x) :
    |x - fluidSusceptible l t| ≤ |fluidClock l x - t| := by
  simpa only [fluidClock_fluidSusceptible hl] using
    abs_sub_le_abs_fluidClock_sub (zero_lt_one.trans hl) hx (fluidSusceptible_pos hl)

namespace Model

/-- Uniform deterministic error control outside the low-susceptible event. -/
theorem eventually_fluidClock_error_bound (rates : ℕ → ℝ≥0) {l c : ℝ}
    (hl : 1 < l) (hc : 0 < c) (hc1 : c < 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ s : State, s.vertices + s.susceptible = n + 1 →
      fluidThreshold c n ≤ s.susceptible →
      |fluidClock l ((s.susceptible : ℝ) / n) - (eventCount s : ℝ) / n| <
        |(finalSizeInvariant (rates n) s - finalSizeInvariant (rates n) (initial n)) / n| + ε := by
  have hl0 : 0 < l := zero_lt_one.trans hl
  obtain ⟨N, hN, hclock⟩ := finalSizeInvariant_clock_uniform (half_pos hε) (half_pos hl0)
  have hparam : Tendsto (fun n ↦ |Real.log c| * |1 / ((rates n : ℝ) * n) - 1 / l|)
      atTop (𝓝 (0 : ℝ)) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).div hrates hl0.ne').sub
      (tendsto_const_nhds (x := 1 / l))).abs.const_mul |Real.log c|
    simpa only [sub_self, abs_zero, mul_zero, Pi.div_apply] using h
  filter_upwards [eventually_ge_atTop N,
    (tendsto_nat_floor_mul_atTop c hc).eventually (eventually_ge_atTop N),
    hrates.eventually (Ioi_mem_nhds (show l / 2 < l by linarith)),
    hparam.eventually (Iio_mem_nhds (half_pos hε))] with n hn hfloor hrn hpar
  intro s hpop hH
  have hn0 : 0 < n := hN.trans_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hHn : N ≤ s.susceptible := by dsimp [fluidThreshold] at hH; omega
  have hlarge := hclock n (rates n) s hn hHn hpop hrn.le
  have hrnpos : 0 < (rates n : ℝ) * n := (half_pos hl0).trans hrn
  have hcH : c < (s.susceptible : ℝ) / n := by
    apply (lt_div_iff₀ hnR).mpr
    have hh : (⌊c * n⌋₊ : ℝ) + 1 ≤ s.susceptible := by
      exact_mod_cast hH
    exact (Nat.lt_floor_add_one (c * n)).trans_le hh
  have hHone : (s.susceptible : ℝ) / n ≤ 1 := by
    apply (div_le_one hnR).mpr
    have hv := s.tree.size_pos
    have hHle : s.susceptible ≤ n := by change 0 < s.vertices at hv; omega
    exact_mod_cast hHle
  have hlog : |Real.log ((s.susceptible : ℝ) / n)| ≤ |Real.log c| := by
    rw [abs_of_nonpos (Real.log_nonpos (hc.trans hcH).le hHone),
      abs_of_nonpos (Real.log_nonpos hc.le hc1.le)]
    exact neg_le_neg (Real.log_le_log hc hcH.le)
  have hdiff : |fluidClock l ((s.susceptible : ℝ) / n) -
      fluidClock ((rates n : ℝ) * n) ((s.susceptible : ℝ) / n)| < ε / 2 := by
    rw [fluidClock_parameter_sub hl0.ne' hrnpos.ne', abs_mul]
    exact (mul_le_mul_of_nonneg_right hlog (abs_nonneg _)).trans_lt hpar
  have hsum := abs_add_le
    (fluidClock l ((s.susceptible : ℝ) / n) -
      fluidClock ((rates n : ℝ) * n) ((s.susceptible : ℝ) / n))
    (fluidClock ((rates n : ℝ) * n) ((s.susceptible : ℝ) / n) -
      (eventCount s : ℝ) / n -
      (finalSizeInvariant (rates n) s - finalSizeInvariant (rates n) (initial n)) / n)
  have htri := abs_add_le
    (fluidClock l ((s.susceptible : ℝ) / n) - (eventCount s : ℝ) / n -
      (finalSizeInvariant (rates n) s - finalSizeInvariant (rates n) (initial n)) / n)
    ((finalSizeInvariant (rates n) s - finalSizeInvariant (rates n) (initial n)) / n)
  have heq : fluidClock l ((s.susceptible : ℝ) / n) -
      fluidClock ((rates n : ℝ) * n) ((s.susceptible : ℝ) / n) +
      (fluidClock ((rates n : ℝ) * n) ((s.susceptible : ℝ) / n) -
      (eventCount s : ℝ) / n -
      (finalSizeInvariant (rates n) s - finalSizeInvariant (rates n) (initial n)) / n) =
      fluidClock l ((s.susceptible : ℝ) / n) - (eventCount s : ℝ) / n -
      (finalSizeInvariant (rates n) s - finalSizeInvariant (rates n) (initial n)) / n := by ring
  rw [heq] at hsum
  rw [sub_add_cancel] at htri
  linarith

/-- The original epidemic's susceptible count approximately solves the fluid
clock equation at its actual number of genuine events, also after absorption. -/
theorem evolve_fluidClock_concentration
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} (hl : 1 < l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
      {s | ε ≤ |fluidClock l ((s.susceptible : ℝ) / n) - (eventCount s : ℝ) / n|})
      atTop (𝓝 0) := by
  let c := finalSusceptibleFraction l / 2
  have hc : 0 < c := half_pos (finalSusceptibleFraction_pos hl)
  have hcf : c < finalSusceptibleFraction l := half_lt_self (finalSusceptibleFraction_pos hl)
  have hF := evolve_finalSizeInvariant_normalized_concentration rates horizon hl hrates hhorizon (half_pos hε)
  have hB := evolve_below_fluidThreshold_tendsto_zero rates horizon hl hc hcf hrates hhorizon
  have hlim := hF.add hB
  simp only [add_zero] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hlim
  filter_upwards [eventually_fluidClock_error_bound rates hl hc
    (hcf.trans (finalSusceptibleFraction_lt_one hl)) hrates (half_pos hε)] with n hn
  apply le_trans _ (measureReal_union_le _ _)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {s : State |
    ε ≤ |fluidClock l ((s.susceptible : ℝ) / n) - (eventCount s : ℝ) / n|} from trivial)
  intro s hs
  by_cases hlow : s.susceptible < fluidThreshold c n
  · exact Or.inr hlow
  · apply Or.inl
    have hb := hn s (evolve_population hs.2) (Nat.le_of_not_gt hlow)
    change ε / 2 ≤ |(finalSizeInvariant (rates n) s - finalSizeInvariant (rates n) (initial n)) / n|
    have hsbound : ε ≤ |fluidClock l ((s.susceptible : ℝ) / n) - (eventCount s : ℝ) / n| := hs.1
    linarith

/-- At a deterministic linear time, active susceptible counts converge in
probability to the fluid susceptible curve, with no conditioning denominator. -/
theorem evolve_active_susceptible_concentration
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} (hl : 1 < l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
      {s | s.active.Nonempty ∧ ε ≤ |(s.susceptible : ℝ) / n - fluidSusceptible l T|})
      atTop (𝓝 0) := by
  let c := finalSusceptibleFraction l / 2
  have hc : 0 < c := half_pos (finalSusceptibleFraction_pos hl)
  have hcf : c < finalSusceptibleFraction l := half_lt_self (finalSusceptibleFraction_pos hl)
  have hC := evolve_fluidClock_concentration rates horizon hl hrates hhorizon (half_pos hε)
  have hB := evolve_below_fluidThreshold_tendsto_zero rates horizon hl hc hcf hrates hhorizon
  have hlim := hC.add hB
  simp only [add_zero] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hlim
  filter_upwards [hhorizon.eventually (Metric.ball_mem_nhds T (half_pos hε)),
    eventually_gt_atTop 0] with n hn hn0
  simp only [Real.dist_eq] at hn
  apply le_trans _ (measureReal_union_le _ _)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {s : State |
    s.active.Nonempty ∧ ε ≤ |(s.susceptible : ℝ) / n - fluidSusceptible l T|} from trivial)
  intro s hs
  by_cases hlow : s.susceptible < fluidThreshold c n
  · exact Or.inr hlow
  · apply Or.inl
    have hH : 0 < s.susceptible := (fluidThreshold_pos c n).trans_le (Nat.le_of_not_gt hlow)
    have hx : (0 : ℝ) < (s.susceptible : ℝ) / n := by positivity
    have he := evolve_eventCount_eq_of_active hs.2 hs.1.1
    have hinv := abs_sub_fluidSusceptible_le (t := T) hl hx
    have htri := abs_add_le (fluidClock l ((s.susceptible : ℝ) / n) - (horizon n : ℝ) / n)
      ((horizon n : ℝ) / n - T)
    rw [sub_add_sub_cancel] at htri
    change ε / 2 ≤ |fluidClock l ((s.susceptible : ℝ) / n) - (eventCount s : ℝ) / n|
    rw [he]
    have hsbound : ε ≤ |(s.susceptible : ℝ) / n - fluidSusceptible l T| := hs.1.2
    linarith


/-- Active infectious counts lie on the corresponding fluid curve. -/
theorem evolve_active_infectious_concentration
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} (hl : 1 < l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
      {s | s.active.Nonempty ∧ ε ≤ |(infectious s : ℝ) / n - fluidInfectiousRaw l T|})
      atTop (𝓝 0) := by
  have hsmall : 0 < ε / 4 := by positivity
  have hH := evolve_active_susceptible_concentration rates horizon hl hrates hhorizon hsmall
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hH
  filter_upwards [hhorizon.eventually (Metric.ball_mem_nhds T hsmall),
    (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0)).eventually
      (Iio_mem_nhds hsmall), eventually_gt_atTop 0] with n hn ht hn0
  simp only [Real.dist_eq] at hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {s : State | s.active.Nonempty ∧
    ε ≤ |(infectious s : ℝ) / n - fluidInfectiousRaw l T|} from trivial)
  intro s hs
  refine ⟨hs.1.1, ?_⟩
  have he := evolve_eventCount_eq_of_active hs.2 hs.1.1
  have hbal : (infectious s : ℝ) + 2 * s.susceptible + horizon n = 2 * n + 1 := by
    exact_mod_cast (he ▸ count_balance (evolve_population hs.2))
  have heq : (infectious s : ℝ) / n - fluidInfectiousRaw l T =
      (-2 * ((s.susceptible : ℝ) / n - fluidSusceptible l T) - ((horizon n : ℝ) / n - T)) + 1 / n := by
    unfold fluidInfectiousRaw
    field_simp
    nlinarith
  have hb : |(infectious s : ℝ) / n - fluidInfectiousRaw l T| ≤
      2 * |(s.susceptible : ℝ) / n - fluidSusceptible l T| + |(horizon n : ℝ) / n - T| + 1 / n := by
    rw [heq]
    have h1 := abs_add_le
      (-2 * ((s.susceptible : ℝ) / n - fluidSusceptible l T) - ((horizon n : ℝ) / n - T))
      ((1 : ℝ) / n)
    have h2 := abs_sub (-2 * ((s.susceptible : ℝ) / n - fluidSusceptible l T))
      ((horizon n : ℝ) / n - T)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / n)] at h1
    rw [abs_mul] at h2
    norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
    linarith
  have hsbound : ε ≤ |(infectious s : ℝ) / n - fluidInfectiousRaw l T| := hs.1.2
  change ε / 4 ≤ |(s.susceptible : ℝ) / n - fluidSusceptible l T|
  linarith

/-- Before deterministic fluid extinction, the probability of a positive but
bounded infectious population tends to zero. -/
theorem evolve_small_active_tendsto_zero
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) (M : ℕ) :
    Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
      {s | 0 < infectious s ∧ infectious s < M}) atTop (𝓝 0) := by
  have hi := fluidInfectiousRaw_pos hl hT
  have hconc := evolve_active_infectious_concentration rates horizon hl hrates hhorizon (half_pos hi)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hconc
  filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat (M : ℝ)).eventually
    (Iio_mem_nhds (half_pos hi)), eventually_gt_atTop 0] with n hM hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro s hs
  refine ⟨Finset.card_pos.mp hs.1, ?_⟩
  have him : (infectious s : ℝ) / n < (M : ℝ) / n :=
    (div_lt_div_iff_of_pos_right hnR).mpr (by exact_mod_cast hs.2)
  have hh := neg_le_abs ((infectious s : ℝ) / n - fluidInfectiousRaw l T)
  change fluidInfectiousRaw l T / 2 ≤ |(infectious s : ℝ) / n - fluidInfectiousRaw l T|
  linarith

end Model
end HeightPaper
