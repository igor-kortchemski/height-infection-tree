module

public import HeightPaper.Analysis.HarmonicClock
public import HeightPaper.Probability.StoppedComparison

/-!
# Removing the susceptible stopping barrier

For a threshold strictly below the positive final susceptible fraction, the
harmonic invariant would have to change by a positive multiple of population
size to cross it. The exact variance bound therefore makes such a crossing
vanish in probability on linear event horizons.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology NNReal

namespace HeightPaper

/-- Limiting invariant cost of reaching susceptible fraction `c`. -/
noncomputable def fluidBarrier (l c : ℝ) : ℝ := c - 1 - Real.log c / l

theorem fluidBarrier_pos {l c : ℝ} (hl : 1 < l) (hc : 0 < c)
    (hcf : c < finalSusceptibleFraction l) : 0 < fluidBarrier l c := by
  have hl0 : 0 < l := zero_lt_one.trans hl
  have hcm : l * c < offspringMean l := by
    unfold finalSusceptibleFraction at hcf
    exact (mul_comm l c).symm ▸ (lt_div_iff₀ hl0).mp hcf
  have hprod := mul_pos hl0 hc
  have hmean := meanEquation_strictMonoOn
    (show l * c ∈ Icc (0 : ℝ) 1 from ⟨hprod.le, hcm.le.trans (offspringMean_lt_one hl).le⟩)
    ⟨(offspringMean_pos hl).le, (offspringMean_lt_one hl).le⟩ hcm
  rw [(offspringMean_spec hl).2] at hmean
  have hlog := Real.log_lt_log (show 0 < meanEquation (l * c) by
    exact mul_pos hprod (Real.exp_pos _)) hmean
  simp only [meanEquation, Real.log_mul hprod.ne' (Real.exp_ne_zero _),
    Real.log_mul hl0.ne' (Real.exp_ne_zero _), Real.log_exp,
    Real.log_mul hl0.ne' hc.ne'] at hlog
  unfold fluidBarrier
  have hdiv : Real.log c / l < c - 1 := (div_lt_iff₀ hl0).mpr (by nlinarith)
  linarith

/-- A strictly positive integer threshold whose crossing value is exactly
`floor (c*n)`. -/
noncomputable def fluidThreshold (c : ℝ) (n : ℕ) : ℕ := ⌊c * n⌋₊ + 1

@[simp] theorem fluidThreshold_pos (c : ℝ) (n : ℕ) : 0 < fluidThreshold c n := by
  unfold fluidThreshold
  omega

@[simp] theorem fluidThreshold_sub_one (c : ℝ) (n : ℕ) :
    fluidThreshold c n - 1 = ⌊c * n⌋₊ := by simp [fluidThreshold]

theorem tendsto_floor_fraction {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ ↦ (⌊c * n⌋₊ : ℝ) / n) atTop (𝓝 c) :=
  (tendsto_nat_floor_mul_div_atTop hc).comp tendsto_natCast_atTop_atTop

theorem tendsto_fluidThreshold_fraction {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ ↦ (fluidThreshold c n : ℝ) / n) atTop (𝓝 c) := by
  have h := (tendsto_floor_fraction hc).add
    (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
  simpa only [fluidThreshold, Nat.cast_add, Nat.cast_one, add_div, add_zero] using h

theorem eventually_fluidThreshold_le {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) :
    ∀ᶠ n : ℕ in atTop, fluidThreshold c n ≤ n := by
  filter_upwards [(tendsto_fluidThreshold_fraction hc).eventually (Iio_mem_nhds hc1),
    eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have h : (fluidThreshold c n : ℝ) < n := (div_lt_one hnR).mp hn
  exact_mod_cast h.le

/-- Harmonic differences at a fixed positive susceptible fraction converge to
the logarithm of that fraction. -/
theorem tendsto_harmonic_floor_sub {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (harmonic ⌊c * n⌋₊ : ℝ) - harmonic n) atTop (𝓝 (Real.log c)) := by
  have hf := tendsto_nat_floor_mul_atTop c hc
  have he := ((Real.tendsto_harmonic_sub_log.comp hf).sub Real.tendsto_harmonic_sub_log).add
    ((tendsto_floor_fraction hc.le).log hc.ne')
  simp only [sub_self, zero_add] at he
  apply he.congr'
  filter_upwards [hf.eventually (eventually_gt_atTop 0), eventually_gt_atTop 0] with n hfn hn
  have hf0 : (⌊c * n⌋₊ : ℝ) ≠ 0 := by exact_mod_cast hfn.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Function.comp_apply]
  rw [Real.log_div hf0 hn0]
  ring

namespace Model

/-- The explicit finite-population barrier has the expected positive-scale
limit, with rounding retained in its exact definition. -/
theorem tendsto_stoppingBarrier_fraction (rates : ℕ → ℝ≥0) {l c : ℝ}
    (hl : l ≠ 0) (hc : 0 < c)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ stoppingBarrier (rates n) n (fluidThreshold c n) / n)
      atTop (𝓝 (fluidBarrier l c)) := by
  have hsucc : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 (1 : ℝ)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add
      (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    push_cast
    field_simp
  have ht := ((tendsto_floor_fraction hc.le).sub hsucc).sub
    ((tendsto_harmonic_floor_sub hc).div hrates hl)
  unfold fluidBarrier
  convert ht using 1
  funext n
  simp only [stoppingBarrier, fluidThreshold_sub_one, Pi.div_apply]
  ring

/-- Infection pressure at the deterministic threshold converges to `l*c`. -/
theorem tendsto_fluidThreshold_pressure (rates : ℕ → ℝ≥0) {l c : ℝ}
    (hc : 0 ≤ c) (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ (rates n : ℝ) * fluidThreshold c n) atTop (𝓝 (l * c)) := by
  apply (hrates.mul (tendsto_fluidThreshold_fraction hc)).congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp


/-- The original finite epidemic reaches any fixed fraction below its
nontrivial final susceptible fraction with vanishing probability. -/
theorem evolve_below_fluidThreshold_tendsto_zero
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l c T : ℝ}
    (hl : 1 < l) (hc : 0 < c) (hcf : c < finalSusceptibleFraction l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
      {s | s.susceptible < fluidThreshold c n}) atTop (𝓝 0) := by
  have hl0 : 0 < l := zero_lt_one.trans hl
  have hlc : 0 < l * c := mul_pos hl0 hc
  have hb := fluidBarrier_pos hl hc hcf
  have hpressure := tendsto_fluidThreshold_pressure rates hc.le hrates
  have hbarrier := tendsto_stoppingBarrier_fraction rates hl0.ne' hc hrates
  let bound : ℕ → ℝ := fun n ↦ (horizon n : ℝ) /
    ((rates n : ℝ) * fluidThreshold c n * (stoppingBarrier (rates n) n (fluidThreshold c n)) ^ 2)
  have hevent : ∀ᶠ n : ℕ in atTop, 0 < n ∧
      0 < (rates n : ℝ) * fluidThreshold c n ∧
      0 < stoppingBarrier (rates n) n (fluidThreshold c n) := by
    filter_upwards [eventually_gt_atTop 0,
      hpressure.eventually (Ioi_mem_nhds hlc), hbarrier.eventually (Ioi_mem_nhds hb)]
      with n hn hp hb'
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact ⟨hn, hp, (div_pos_iff.mp hb').resolve_right (by intro h; linarith) |>.1⟩
  have hbound : Tendsto bound atTop (𝓝 0) := by
    have ht := (hhorizon.div (hpressure.mul (hbarrier.pow 2))
      (mul_ne_zero hlc.ne' (pow_ne_zero _ hb.ne'))).mul
      (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hevent] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.1.ne'
    dsimp [bound]
    field_simp
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hbound
  filter_upwards [hevent,
    eventually_fluidThreshold_le hc.le (hcf.trans (finalSusceptibleFraction_lt_one hl))]
    with n hn ha
  have hr : 0 < rates n := by
    have hh := hn.2.1
    have ht : (0 : ℝ) ≤ fluidThreshold c n := Nat.cast_nonneg _
    have hrR : 0 < (rates n : ℝ) := by nlinarith
    exact_mod_cast hrR
  exact evolve_below_threshold_le (rates n) (fluidThreshold c n) n (horizon n)
    hr (fluidThreshold_pos _ _) ha hn.2.2

/-- The exact harmonic invariant of the original, unstopped SIR epidemic
concentrates on every linear event horizon. No fluid-limit input is assumed. -/
theorem evolve_finalSizeInvariant_normalized_concentration
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} (hl : 1 < l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
      {s | ε ≤ |(finalSizeInvariant (rates n) s - finalSizeInvariant (rates n) (initial n)) / n|})
      atTop (𝓝 0) := by
  let c := finalSusceptibleFraction l / 2
  have hc : 0 < c := half_pos (finalSusceptibleFraction_pos hl)
  have hcf : c < finalSusceptibleFraction l := half_lt_self (finalSusceptibleFraction_pos hl)
  have hs := stoppedCountLaw_normalized_concentration rates (fluidThreshold c) horizon initial
    (mul_pos (zero_lt_one.trans hl) hc) (tendsto_fluidThreshold_pressure rates hc.le hrates)
    hhorizon hε
  have hb := evolve_below_fluidThreshold_tendsto_zero rates horizon hl hc hcf hrates hhorizon
  have ht := hs.add hb
  simp only [add_zero] at ht
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ ht
  intro n
  exact evolve_measureReal_le_stopped (rates n) (fluidThreshold c n) n (horizon n)
    (fluidThreshold_pos _ _) _

end Model
end HeightPaper
