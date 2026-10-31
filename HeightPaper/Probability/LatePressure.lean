module

public import HeightPaper.Probability.TerminalFluid
public import HeightPaper.Analysis.LatePhase

/-!
# Uniform pressure control after a late cutoff

Monotonicity of the susceptible count reduces all post-cutoff pressures to
its two endpoint values. Their actual probability estimates follow from the
fixed-time and terminal fluid location theorems. The eventual cutoff statement
retains every sufficiently small positive cutoff parameter.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

/-- Changing the scaled rate and susceptible fraction controls the unscaled
infection-pressure error. -/
theorem pressure_error_le {n H : ℕ} (hn : 0 < n) (hH : H ≤ n)
    {l : ℝ} (hl : 0 ≤ l) (rate : ℝ≥0) (x : ℝ) :
    |(rate : ℝ) * H - l * x| ≤ |(rate : ℝ) * n - l| + l * |(H : ℝ) / n - x| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfrac0 : (0 : ℝ) ≤ (H : ℝ) / n := by positivity
  have hfrac1 : (H : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hH)
  have heq : (rate : ℝ) * H - l * x =
      ((rate : ℝ) * n - l) * ((H : ℝ) / n) + l * ((H : ℝ) / n - x) := by
    field_simp
    ring
  have hh := abs_add_le (((rate : ℝ) * n - l) * ((H : ℝ) / n)) (l * ((H : ℝ) / n - x))
  rw [← heq, abs_mul, abs_mul, abs_of_nonneg hfrac0, abs_of_nonneg hl] at hh
  have hm := mul_le_mul_of_nonneg_left hfrac1 (abs_nonneg ((rate : ℝ) * n - l))
  simp only [mul_one] at hm
  linarith

/-- At a fixed linear time, pressure of the active epidemic concentrates at
the deterministic fluid pressure. -/
theorem evolve_active_pressure_concentration
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} (hl : 1 < l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
      {s | s.active.Nonempty ∧ ε ≤ |(rates n : ℝ) * s.susceptible - l * fluidSusceptible l T|})
      atTop (𝓝 0) := by
  have hl0 : 0 < l := zero_lt_one.trans hl
  have htol : 0 < ε / (2 * l) := by positivity
  have hH := evolve_active_susceptible_concentration rates horizon hl hrates hhorizon htol
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hH
  filter_upwards [hrates.eventually (Metric.ball_mem_nhds l (half_pos hε)),
    eventually_gt_atTop 0] with n hn hn0
  simp only [Real.dist_eq] at hn
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {s : State | s.active.Nonempty ∧
    ε ≤ |(rates n : ℝ) * s.susceptible - l * fluidSusceptible l T|} from trivial)
  intro s hs
  refine ⟨hs.1.1, ?_⟩
  have hb := pressure_error_le hn0 (evolve_susceptible_le hs.2) hl0.le (rates n) (fluidSusceptible l T)
  have hsbound : ε ≤ |(rates n : ℝ) * s.susceptible - l * fluidSusceptible l T| := hs.1.2
  change ε / (2 * l) ≤ |(s.susceptible : ℝ) / n - fluidSusceptible l T|
  apply (div_le_iff₀ (by positivity : 0 < 2 * l)).mpr
  nlinarith

/-- Terminal pressure is close to the subcritical mean on actual survival. -/
theorem sourceSurvival_finalPressure_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (terminalStateMeasure (rates n) n).real
      {s | s ∈ sourceSurvivalEvent l δ n ∧ ε ≤ |(rates n : ℝ) * s.susceptible - offspringMean l|})
      atTop (𝓝 0) := by
  have hl0 : 0 < l := zero_lt_one.trans hl
  have htol : 0 < ε / (2 * l) := by positivity
  have hH := sourceSurvival_finalSusceptible_concentration rates hl hδ hrates htol
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hH
  filter_upwards [hrates.eventually (Metric.ball_mem_nhds l (half_pos hε)),
    eventually_gt_atTop 0] with n hn hn0
  simp only [Real.dist_eq] at hn
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {s : State | s ∈ sourceSurvivalEvent l δ n ∧
    ε ≤ |(rates n : ℝ) * s.susceptible - offspringMean l|} from trivial)
  intro s hs
  refine ⟨hs.1.1, ?_⟩
  have hb := pressure_error_le hn0 (evolve_susceptible_le hs.2) hl0.le (rates n) (finalSusceptibleFraction l)
  have hmean : l * finalSusceptibleFraction l = offspringMean l := by
    unfold finalSusceptibleFraction
    field_simp
  rw [hmean] at hb
  have hsbound : ε ≤ |(rates n : ℝ) * s.susceptible - offspringMean l| := hs.1.2
  change ε / (2 * l) ≤ |(s.susceptible : ℝ) / n - finalSusceptibleFraction l|
  apply (div_le_iff₀ (by positivity : 0 < 2 * l)).mpr
  nlinarith

namespace SupportedPath

/-- Susceptibles never increase along an actual supported epidemic history. -/
theorem susceptible_antitone {rate : ℝ≥0} {n steps : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n steps path) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps) :
    (path j).susceptible ≤ (path i).susceptible := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (susceptible_step_le (hp.2 j (by omega))).trans (ih (by omega))

end SupportedPath

/-- Every pressure from the source cutoff through deterministic terminal time
lies inside the specified interval. This includes absorbing self-loops. -/
def latePressureEvent (rate : ℝ≥0) (l δ η : ℝ) (n : ℕ) : Set (FinitePath (2 * n + 1)) :=
  {p | ∀ k, sourceCutoff l δ n ≤ k → k ≤ 2 * n + 1 →
    offspringMean l - η ≤ (rate : ℝ) * (p.eval k).susceptible ∧
      (rate : ℝ) * (p.eval k).susceptible ≤ offspringMean l + η}

theorem sourceCutoff_pred_fraction_tendsto {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ ↦ ((sourceCutoff l δ n - 1 : ℕ) : ℝ) / n)
      atTop (𝓝 ((1 - δ) * fluidExtinctionTime l)) := by
  have hT : 0 < (1 - δ) * fluidExtinctionTime l :=
    mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
  have hfloor : Tendsto (fun n : ℕ ↦ (sourceCutoff l δ n : ℝ) / n)
      atTop (𝓝 ((1 - δ) * fluidExtinctionTime l)) := tendsto_floor_fraction hT.le
  have hh := hfloor.sub (tendsto_one_div_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [sourceCutoff_pos_eventually hl hδ] with n hn
  rw [Nat.cast_sub (by omega : 1 ≤ sourceCutoff l δ n), Nat.cast_one, sub_div]

/-- Fixed sufficiently late cutoffs give uniform pressure control throughout
the remaining epidemic, under its actual joint history law. -/
theorem sourceSurvival_latePressure_failure_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ η : ℝ} (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η)
    (hnear : l * fluidSusceptible l ((1 - δ) * fluidExtinctionTime l) < offspringMean l + η / 2)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {p | p.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        p ∉ latePressureEvent (rates n) l δ η n}) atTop (𝓝 0) := by
  have hA := evolve_active_pressure_concentration rates (fun n ↦ sourceCutoff l δ n - 1)
    hl hrates (sourceCutoff_pred_fraction_tendsto hl hδ) (half_pos hη)
  have hB := sourceSurvival_finalPressure_concentration rates hl hδ hrates (half_pos hη)
  have hlim := hB.add hA
  simp only [add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hlim
  filter_upwards [sourceCutoff_pos_eventually hl hδ] with n hcut
  have hk : sourceCutoff l δ n - 1 ≤ 2 * n + 1 := by
    have := sourceCutoff_le_steps hl hδ n
    omega
  change (pathMeasure (rates n) n (2 * n + 1)).real _ ≤
    (evolve (rates n) n (2 * n + 1)).toMeasure.real
      {s | s ∈ sourceSurvivalEvent l δ n ∧ η / 2 ≤ |(rates n : ℝ) * s.susceptible - offspringMean l|} + _
  rw [← pathMeasure_event_at (rates n) n (2 * n + 1) (2 * n + 1) le_rfl,
    ← pathMeasure_event_at (rates n) n (2 * n + 1) (sourceCutoff l δ n - 1) hk]
  apply le_trans _ (measureReal_union_le _ _)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {p : FinitePath (2 * n + 1) |
    p.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
      p ∉ latePressureEvent (rates n) l δ η n} from trivial)
  intro p hp
  have hpath := (mem_support_pathLaw_iff p).mp hp.2
  by_cases hb : η / 2 ≤ |(rates n : ℝ) * (p.eval (2 * n + 1)).susceptible - offspringMean l|
  · exact Or.inl ⟨hp.1.1, hb⟩
  · apply Or.inr
    refine ⟨(sourceSurvivalEvent_iff_active hl hδ hpath hcut).mp hp.1.1, ?_⟩
    by_contra ha
    have hb' := (abs_lt.mp (lt_of_not_ge hb)).1
    have ha' := (abs_lt.mp (lt_of_not_ge ha)).2
    apply hp.1.2
    intro k hcutk hkend
    have hlow := mul_le_mul_of_nonneg_left
      (show ((p.eval (2 * n + 1)).susceptible : ℝ) ≤ (p.eval k).susceptible by
        exact_mod_cast hpath.susceptible_antitone hkend le_rfl) (rates n).coe_nonneg
    have hhigh := mul_le_mul_of_nonneg_left
      (show ((p.eval k).susceptible : ℝ) ≤ (p.eval (sourceCutoff l δ n - 1)).susceptible by
        exact_mod_cast hpath.susceptible_antitone (by omega : sourceCutoff l δ n - 1 ≤ k) hkend) (rates n).coe_nonneg
    constructor <;> linarith

/-- For every tolerance, every sufficiently small positive cutoff fraction
has the actual uniform post-cutoff pressure estimate. -/
theorem eventually_sourceSurvival_latePressure
    (rates : ℕ → ℝ≥0) {l η : ℝ} (hl : 1 < l) (hη : 0 < η)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
        {p | p.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
          p ∉ latePressureEvent (rates n) l δ η n}) atTop (𝓝 0) := by
  have hh := (tendsto_fluidPressure_at_cutoff hl).eventually
    (Iio_mem_nhds (show offspringMean l < offspringMean l + η / 2 by linarith))
  obtain ⟨d, hd, hbound⟩ := Metric.eventually_nhds_iff.mp hh
  let δ₀ := min (d / 2) (1 / 4)
  have hδ₀ : 0 < δ₀ := lt_min (half_pos hd) (by norm_num)
  have hδ₀half : δ₀ < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨δ₀, ⟨hδ₀, hδ₀half⟩, ?_⟩
  intro δ hδ
  have hδ1 : δ < 1 := hδ.2.trans (hδ₀half.trans (by norm_num))
  apply sourceSurvival_latePressure_failure_tendsto_zero rates hl ⟨hδ.1, hδ1⟩ hη _ hrates
  apply hbound
  rw [Real.dist_eq, sub_zero, abs_of_pos hδ.1]
  have hδd : δ < d / 2 := hδ.2.trans_le (min_le_left _ _)
  linarith

/-- The corrected subcritical recovery event from `lem:eventE`, expressed on
actual finite epidemic histories. -/
def lateRecoveryEvent (rate : ℝ≥0) (l δ η : ℝ) (n : ℕ) : Set (FinitePath (2 * n + 1)) :=
  {p | ∀ k, sourceCutoff l δ n ≤ k → k ≤ 2 * n + 1 →
    1 / (1 + offspringMean l + η) ≤ 1 / (1 + (rate : ℝ) * (p.eval k).susceptible) ∧
      1 / (1 + (rate : ℝ) * (p.eval k).susceptible) ≤ 1 / (1 + offspringMean l - η)}

/-- Small positive perturbations retain both comparison recovery parameters
in the subcritical geometric-tree regime. -/
theorem latePressureEvent_subset_lateRecoveryEvent (rate : ℝ≥0) (l δ η : ℝ) (n : ℕ)
    (hη : 0 < η) (hηm : η < offspringMean l) (hη1 : η < 1 - offspringMean l) :
    latePressureEvent rate l δ η n ⊆ lateRecoveryEvent rate l δ η n := by
  intro p hp k hk hj
  have h := hp k hk hj
  have hh := subcritical_recovery_bounds hη hηm hη1 h.1 h.2
  exact ⟨hh.2.1, hh.2.2.1⟩

/-- Actual probability form of the corrected recovery-control event: each
sufficiently late fixed cutoff works, with all rate sequences retained. -/
theorem eventually_sourceSurvival_lateRecovery
    (rates : ℕ → ℝ≥0) {l η : ℝ} (hl : 1 < l)
    (hη : 0 < η) (hηm : η < offspringMean l) (hη1 : η < 1 - offspringMean l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
        {p | p.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
          p ∉ lateRecoveryEvent (rates n) l δ η n}) atTop (𝓝 0) := by
  obtain ⟨δ₀, hδ₀, hlim⟩ := eventually_sourceSurvival_latePressure rates hl hη hrates
  refine ⟨δ₀, hδ₀, fun δ hδ ↦ ?_⟩
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ (hlim δ hδ)
  intro n
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro p hp
  exact ⟨hp.1, fun h ↦ hp.2 (latePressureEvent_subset_lateRecoveryEvent (rates n) l δ η n hη hηm hη1 h)⟩

end HeightPaper.Model
