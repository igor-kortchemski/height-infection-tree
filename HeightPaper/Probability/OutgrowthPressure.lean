module

public import HeightPaper.Probability.LatePressure
public import HeightPaper.Probability.LatePressureThreshold
public import HeightPaper.Model.HeightPotentialBounds

/-!
# Actual epidemic pressure inputs for geometric outgrowth comparisons

These wrappers accept the geometric offspring parameter used by the height
bounds. The upper comparison works at every sufficiently late fixed cutoff;
the lower comparison uses a deterministic integer barrier below the final
fluid susceptible fraction.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

private theorem reciprocal_geometricMean {p : unitInterval} (hp : 0 < (p : ℝ)) :
    1 / (1 + Branching.geometricMean p) = (p : ℝ) := by
  rw [Branching.geometricMean_eq_inv_sub_one hp]
  have heq : 1 + (1 / (p : ℝ) - 1) = 1 / (p : ℝ) := by ring
  rw [heq, one_div_one_div]

/-- A comparison mean strictly above the fluid pressure bounds the actual
recovery probability from below, outside an event of vanishing probability. -/
theorem evolve_active_recovery_lower_concentration
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} {p : unitInterval}
    (hl : 1 < l) (hp : 0 < (p : ℝ))
    (hpressure : l * fluidSusceptible l T < Branching.geometricMean p)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
      {s | s.active.Nonempty ∧
        1 - (infectionProbability (rates n) s.susceptible : ℝ) < (p : ℝ)}) atTop (𝓝 0) := by
  let ε := (Branching.geometricMean p - l * fluidSusceptible l T) / 2
  have hε : 0 < ε := half_pos (sub_pos.mpr hpressure)
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _
    (evolve_active_pressure_concentration rates horizon hl hrates hhorizon hε)
  intro n
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro s hs
  refine ⟨hs.1, ?_⟩
  by_contra hbad
  have hdiff := (abs_lt.mp (lt_of_not_ge hbad)).2
  have hbound : (rates n : ℝ) * s.susceptible ≤ Branching.geometricMean p := by
    dsimp [ε] at hdiff
    linarith only [hdiff, hpressure]
  have hrec : (p : ℝ) ≤ 1 / (1 + (rates n : ℝ) * s.susceptible) := by
    rw [← reciprocal_geometricMean hp]
    apply one_div_le_one_div_of_le (by positivity)
    linarith only [hbound]
  have hsrec := hs.2
  rw [recoveryProbability_real] at hsrec
  exact not_lt_of_ge hrec hsrec

/-- Every sufficiently small fixed cutoff parameter supplies the upper
outgrowth comparison pressure, for any comparison mean above the final mean. -/
theorem eventually_cutoff_recovery_lower_concentration
    (rates : ℕ → ℝ≥0) {l : ℝ} {p : unitInterval}
    (hl : 1 < l) (hp : 0 < (p : ℝ))
    (hmean : offspringMean l < Branching.geometricMean p)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      Tendsto (fun n ↦ (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
        {s | s.active.Nonempty ∧
          1 - (infectionProbability (rates n) s.susceptible : ℝ) < (p : ℝ)}) atTop (𝓝 0) := by
  have he := (tendsto_fluidPressure_at_cutoff hl).eventually (Iio_mem_nhds hmean)
  obtain ⟨d, hd, hbound⟩ := Metric.eventually_nhds_iff.mp he
  let δ₀ := min (d / 2) (1 / 4)
  have hδ₀ : 0 < δ₀ := lt_min (half_pos hd) (by norm_num)
  have hδ₀half : δ₀ < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨δ₀, ⟨hδ₀, hδ₀half⟩, ?_⟩
  intro δ hδ
  have hδ1 : δ < 1 := hδ.2.trans (hδ₀half.trans (by norm_num))
  have hnear : l * fluidSusceptible l ((1 - δ) * fluidExtinctionTime l) <
      Branching.geometricMean p := by
    apply hbound
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ.1]
    have hδd : δ < d / 2 := hδ.2.trans_le (min_le_left _ _)
    linarith only [hδd, hd]
  exact evolve_active_recovery_lower_concentration rates (fun n ↦ sourceCutoff l δ n)
    hl hp hnear hrates (tendsto_floor_fraction
      (mul_pos (sub_pos.mpr hδ1) (fluidExtinctionTime_pos hl)).le)

/-- Any geometric mean strictly below the final epidemic mean admits an
integer susceptible barrier with negligible failure probability. -/
theorem exists_outgrowth_lower_pressure_threshold
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} {p : unitInterval}
    (hl : 1 < l) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hmean : Branching.geometricMean p < offspringMean l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    ∃ L : ℕ → ℕ, (∀ n, 0 < L n) ∧
      (∀ᶠ n in atTop, L n ≤ n ∧
        1 - (infectionProbability (rates n) (L n) : ℝ) ≤ (p : ℝ)) ∧
      Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
        {s | s.susceptible < L n}) atTop (𝓝 0) := by
  let η := offspringMean l - Branching.geometricMean p
  have hη : 0 < η := sub_pos.mpr hmean
  have hηm : η < offspringMean l := by
    have hpos := Branching.geometricMean_pos hp hp1
    dsimp [η]
    linarith only [hpos]
  refine ⟨latePressureThreshold l η, latePressureThreshold_pos l η, ?_,
    evolve_below_latePressureThreshold_tendsto_zero rates horizon hl hη hηm hrates hhorizon⟩
  filter_upwards [eventually_latePressureThreshold_bounds rates hl hη hηm hrates] with n hn
  refine ⟨hn.1, ?_⟩
  rw [recoveryProbability_real]
  have heq : 1 + offspringMean l - η = 1 + Branching.geometricMean p := by dsimp [η]; ring
  rw [heq, reciprocal_geometricMean hp] at hn
  exact hn.2.2

/-- Terminal-time specialization of the lower comparison barrier. -/
theorem exists_terminal_outgrowth_lower_pressure_threshold
    (rates : ℕ → ℝ≥0) {l : ℝ} {p : unitInterval}
    (hl : 1 < l) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hmean : Branching.geometricMean p < offspringMean l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∃ L : ℕ → ℕ, (∀ n, 0 < L n) ∧
      (∀ᶠ n in atTop, L n ≤ n ∧
        1 - (infectionProbability (rates n) (L n) : ℝ) ≤ (p : ℝ)) ∧
      Tendsto (fun n ↦ (evolve (rates n) n (2 * n + 1)).toMeasure.real
        {s | s.susceptible < L n}) atTop (𝓝 0) :=
  exists_outgrowth_lower_pressure_threshold rates (fun n ↦ 2 * n + 1)
    hl hp hp1 hmean hrates tendsto_terminal_horizon_fraction

end HeightPaper.Model
