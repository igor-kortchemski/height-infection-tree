module

public import HeightPaper.Probability.SourceSurvival

/-!
# Terminal epidemic size on survival

The terminal clock equation and the uniqueness of the positive fluid
extinction time locate the terminal event and susceptible counts on the
source survival event.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper

/-- A compact subset away from the unique positive fluid extinction time has
a uniformly nonzero infectious-curve residual. -/
theorem fluidInfectiousRaw_abs_away_extinction {l a ε : ℝ} (hl : 1 < l)
    (ha : 0 < a) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc a 3, ε ≤ |t - fluidExtinctionTime l| →
      c ≤ |fluidInfectiousRaw l t| := by
  have hcompact : IsCompact (Icc a 3 ∩ {t : ℝ | ε ≤ |t - fluidExtinctionTime l|}) :=
    isCompact_Icc.inter_right (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  obtain ⟨c, hc, hbound⟩ := hcompact.exists_forall_le'
    (continuous_fluidInfectiousRaw hl).abs.continuousOn (a := (0 : ℝ)) (by
      intro t ht
      apply abs_pos.mpr
      intro hz
      have heq := fluidExtinctionTime_unique hl (ha.trans_le ht.1.1) hz
      have hgap : ε ≤ |t - fluidExtinctionTime l| := ht.2
      rw [heq, sub_self, abs_zero] at hgap
      linarith)
  exact ⟨c, hc, fun t ht hgap ↦ hbound t ⟨ht, hgap⟩⟩

namespace Model

/-- Absolute fluid residual at an extinct state, including the exact finite
population correction. -/
theorem extinct_fluidInfectiousRaw_abs_le_clock_error {l : ℝ} (hl : 1 < l)
    {n : ℕ} (hn : 0 < n) {s : State} (hpop : s.vertices + s.susceptible = n + 1)
    (hz : infectious s = 0) (hH : 0 < s.susceptible) :
    |fluidInfectiousRaw l ((eventCount s : ℝ) / n)| ≤
      2 * |fluidClock l ((s.susceptible : ℝ) / n) - (eventCount s : ℝ) / n| + 1 / n := by
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
  have hh := abs_sub (2 * ((s.susceptible : ℝ) / n - fluidSusceptible l ((eventCount s : ℝ) / n))) ((1 : ℝ) / n)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / n)] at hh
  linarith

theorem tendsto_terminal_horizon_fraction :
    Tendsto (fun n : ℕ ↦ ((2 * n + 1 : ℕ) : ℝ) / n) atTop (𝓝 (2 : ℝ)) := by
  have h := (tendsto_const_nhds (x := (2 : ℝ))).add
    (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp

/-- On the actual source survival event, the total number of genuine events
concentrates at the positive fluid extinction time. -/
theorem sourceSurvival_eventCount_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (terminalStateMeasure (rates n) n).real
      {s | s ∈ sourceSurvivalEvent l δ n ∧ ε ≤ |(eventCount s : ℝ) / n - fluidExtinctionTime l|})
      atTop (𝓝 0) := by
  let T := (1 - δ) * fluidExtinctionTime l
  have hT : 0 < T := mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
  obtain ⟨b, hb, hbound⟩ := fluidInfectiousRaw_abs_away_extinction hl (half_pos hT) hε
  let c := finalSusceptibleFraction l / 2
  have hc : 0 < c := half_pos (finalSusceptibleFraction_pos hl)
  have hcf : c < finalSusceptibleFraction l := half_lt_self (finalSusceptibleFraction_pos hl)
  have hC := evolve_fluidClock_concentration rates (fun n ↦ 2 * n + 1) hl hrates
    tendsto_terminal_horizon_fraction (show 0 < b / 4 by positivity)
  have hB := evolve_below_fluidThreshold_tendsto_zero rates (fun n ↦ 2 * n + 1)
    hl hc hcf hrates tendsto_terminal_horizon_fraction
  have hlim := hC.add hB
  simp only [add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hlim
  have hfloor : Tendsto (fun n : ℕ ↦ (sourceCutoff l δ n : ℝ) / n) atTop (𝓝 T) :=
    tendsto_floor_fraction hT.le
  filter_upwards [hfloor.eventually (Ioi_mem_nhds (half_lt_self hT)),
    (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0)).eventually
      (Iio_mem_nhds (half_pos hb)), eventually_gt_atTop 0] with n hn hsmall hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  apply le_trans _ (measureReal_union_le _ _)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {s : State |
    s ∈ sourceSurvivalEvent l δ n ∧ ε ≤ |(eventCount s : ℝ) / n - fluidExtinctionTime l|} from trivial)
  intro s hs
  by_cases hlow : s.susceptible < fluidThreshold c n
  · exact Or.inr hlow
  · apply Or.inl
    have hpop := evolve_population hs.2
    have habs := evolve_absorbed (by omega : 2 * n + 1 ≤ 2 * n + 1) hs.2
    have hz : infectious s = 0 := Finset.card_eq_zero.mpr habs
    have he : sourceCutoff l δ n ≤ eventCount s := by
      rw [eventCount_absorbed habs]
      exact hs.1.1
    have hlowtime : T / 2 ≤ (eventCount s : ℝ) / n := hn.le.trans
      (div_le_div_of_nonneg_right (by exact_mod_cast he) hnR.le)
    have hevent : (eventCount s : ℝ) ≤ 2 * n + 1 := by exact_mod_cast evolve_eventCount_le hs.2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have huptime : (eventCount s : ℝ) / n ≤ 3 := (div_le_iff₀ hnR).mpr (by nlinarith)
    have hgap := hbound ((eventCount s : ℝ) / n) ⟨hlowtime, huptime⟩ hs.1.2
    have hH := (fluidThreshold_pos c n).trans_le (Nat.le_of_not_gt hlow)
    have hres := extinct_fluidInfectiousRaw_abs_le_clock_error hl hn0 hpop hz hH
    change b / 4 ≤ |fluidClock l ((s.susceptible : ℝ) / n) - (eventCount s : ℝ) / n|
    linarith

/-- The terminal susceptible fraction concentrates at `m_l/l` on the source
survival event. -/
theorem sourceSurvival_finalSusceptible_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (terminalStateMeasure (rates n) n).real
      {s | s ∈ sourceSurvivalEvent l δ n ∧ ε ≤ |(s.susceptible : ℝ) / n - finalSusceptibleFraction l|})
      atTop (𝓝 0) := by
  have hE := sourceSurvival_eventCount_concentration rates hl hδ hrates hε
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hE
  filter_upwards [(tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0)).eventually
    (Iio_mem_nhds hε), eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {s : State | s ∈ sourceSurvivalEvent l δ n ∧
    ε ≤ |(s.susceptible : ℝ) / n - finalSusceptibleFraction l|} from trivial)
  intro s hs
  refine ⟨hs.1.1, ?_⟩
  have habs := evolve_absorbed (by omega : 2 * n + 1 ≤ 2 * n + 1) hs.2
  have hz : infectious s = 0 := Finset.card_eq_zero.mpr habs
  have hb : 2 * (s.susceptible : ℝ) + eventCount s = 2 * n + 1 := by
    have hh := count_balance (evolve_population hs.2)
    rw [hz, zero_add] at hh
    exact_mod_cast hh
  have heq : (s.susceptible : ℝ) / n - finalSusceptibleFraction l =
      -((eventCount s : ℝ) / n - fluidExtinctionTime l) / 2 + 1 / (2 * n) := by
    unfold fluidExtinctionTime
    field_simp
    nlinarith
  have hh := abs_add_le (-((eventCount s : ℝ) / n - fluidExtinctionTime l) / 2) (1 / (2 * n))
  rw [← heq, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * n))] at hh
  have hinv : (1 : ℝ) / (2 * n) = (1 / n) / 2 := by ring
  rw [hinv] at hh
  have hsbound : ε ≤ |(s.susceptible : ℝ) / n - finalSusceptibleFraction l| := hs.1.2
  change ε ≤ |(eventCount s : ℝ) / n - fluidExtinctionTime l|
  linarith

end Model
end HeightPaper
