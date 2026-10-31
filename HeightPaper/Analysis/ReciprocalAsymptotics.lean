module

public import HeightPaper.Analysis.FluidBarrier

/-!
# Logarithmic harmonic sums on fixed fractional horizons

These deterministic limits retain the integer cutoffs used by the epidemic
reciprocal bounds. Finite initial segments disappear after division by `log n`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace HeightPaper

theorem harmonic_real_eq_sum_range (n : ℕ) :
    (harmonic n : ℝ) = ∑ k ∈ Finset.range (n + 1), (k : ℝ)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, ih]
    exact (Finset.sum_range_succ (fun k : ℕ ↦ (k : ℝ)⁻¹) (n + 1)).symm

theorem tendsto_harmonic_div_log :
    Tendsto (fun n : ℕ ↦ (harmonic n : ℝ) / Real.log n) atTop (𝓝 1) := by
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  have hh := (Real.tendsto_harmonic_sub_log.div_atTop hlog).add (tendsto_const_nhds (x := (1 : ℝ)))
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hlogne : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  dsimp only [Function.comp_apply]
  field_simp
  ring

theorem tendsto_harmonic_floor_div_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ (harmonic ⌊a * n⌋₊ : ℝ) / Real.log n) atTop (𝓝 1) := by
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  have hh := ((tendsto_harmonic_floor_sub ha).div_atTop hlog).add tendsto_harmonic_div_log
  simp only [zero_add] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun n ↦ by dsimp; ring)

theorem tendsto_reciprocal_range_floor_div_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.range ⌊a * n⌋₊, (k : ℝ)⁻¹) / Real.log n)
      atTop (𝓝 1) := by
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  have hinv : Tendsto (fun n : ℕ ↦ (⌊a * n⌋₊ : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_nat_floor_mul_atTop a ha)
  have hh := (tendsto_harmonic_floor_div_log ha).sub (hinv.div_atTop hlog)
  simp only [sub_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  dsimp only [Function.comp_apply]
  rw [harmonic_real_eq_sum_range, Finset.sum_range_succ, add_div]
  ring

/-- The fixed finite initial cutoff does not affect the logarithmic harmonic
coefficient, including when the lower cutoff is zero. -/
theorem tendsto_reciprocal_Ico_floor_div_log {a : ℝ} (ha : 0 < a) (K : ℕ) :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Ico K ⌊a * n⌋₊, (k : ℝ)⁻¹) / Real.log n)
      atTop (𝓝 1) := by
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  have hh := (tendsto_reciprocal_range_floor_div_log ha).sub
    (hlog.const_div_atTop (∑ k ∈ Finset.range K, (k : ℝ)⁻¹))
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [(tendsto_nat_floor_mul_atTop a ha).eventually (eventually_ge_atTop K)] with n hn
  dsimp only [Function.comp_apply]
  rw [← Finset.sum_range_add_sum_Ico _ hn, add_div]
  ring

end HeightPaper
