module

public import HeightPaper.Analysis.GeometricScale
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Polynomial root-count bounds on geometric height scales -/

public section

open Filter
open scoped Topology

namespace HeightPaper

private theorem eventually_power_geometric_exp (H : ℕ → ℕ) (g : ℝ) {m : ℝ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ g * m ^ H n =
      Real.exp (g * Real.log n + (H n : ℝ) * Real.log m) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hm, Real.rpow_def_of_pos hn', mul_comm g]

theorem tendsto_power_geometric_scale_zero (H : ℕ → ℕ) {g a m : ℝ} (hm : 0 < m)
    (hH : Tendsto (fun n ↦ (H n : ℝ) / Real.log n) atTop (𝓝 a))
    (hgap : g + a * Real.log m < 0) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ g * m ^ H n) atTop (𝓝 0) := by
  have hratio : Tendsto (fun n : ℕ ↦ g + (H n : ℝ) / Real.log n * Real.log m)
      atTop (𝓝 (g + a * Real.log m)) := tendsto_const_nhds.add (hH.mul_const _)
  have hprod := tendsto_log_nat_atTop.atTop_mul_neg hgap hratio
  have he : Tendsto (fun n : ℕ ↦ g * Real.log n + (H n : ℝ) * Real.log m) atTop atBot := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hl : Real.log n ≠ 0 := (Real.log_pos hn').ne'
    field_simp
  apply (Real.tendsto_exp_atBot.comp he).congr'
  exact (eventually_power_geometric_exp H g hm).mono fun _ hn ↦ hn.symm

theorem tendsto_power_geometric_scale_atTop (H : ℕ → ℕ) {g a m : ℝ} (hm : 0 < m)
    (hH : Tendsto (fun n ↦ (H n : ℝ) / Real.log n) atTop (𝓝 a))
    (hgap : 0 < g + a * Real.log m) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ g * m ^ H n) atTop atTop := by
  have hratio : Tendsto (fun n : ℕ ↦ g + (H n : ℝ) / Real.log n * Real.log m)
      atTop (𝓝 (g + a * Real.log m)) := tendsto_const_nhds.add (hH.mul_const _)
  have hprod := tendsto_log_nat_atTop.atTop_mul_pos hgap hratio
  have he : Tendsto (fun n : ℕ ↦ g * Real.log n + (H n : ℝ) * Real.log m) atTop atTop := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hl : Real.log n ≠ 0 := (Real.log_pos hn').ne'
    field_simp
  apply (Real.tendsto_exp_atTop.comp he).congr'
  exact (eventually_power_geometric_exp H g hm).mono fun _ hn ↦ hn.symm

/-- A small logarithmic count error implies both polynomial count bounds.
The positive lower exponent also rules out the totalized value `log 0 = 0`. -/
theorem nat_count_rpow_bounds_of_log_error {n N : ℕ} (hn : 1 < n)
    {f η : ℝ} (hη : 0 < η) (hηf : η < f)
    (herr : |Real.log N / Real.log n - f| < η) :
    (n : ℝ) ^ (f - η) ≤ N ∧ (N : ℝ) ≤ (n : ℝ) ^ (f + η) := by
  have hf : 0 < f := hη.trans hηf
  have hNp : 0 < N := by
    by_contra hbad
    have hz : N = 0 := Nat.eq_zero_of_not_pos hbad
    simp only [hz, Nat.cast_zero, Real.log_zero, zero_div, zero_sub, abs_neg,
      abs_of_pos hf] at herr
    linarith
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hln := Real.log_pos hn'
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hb := abs_lt.mp herr
  constructor
  · have hh : (f - η) * Real.log n < Real.log N :=
      (lt_div_iff₀ hln).mp (by linarith : f - η < Real.log N / Real.log n)
    have he := Real.exp_lt_exp.mpr hh
    rw [Real.exp_log hNr] at he
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hn')]
    exact (by simpa only [mul_comm] using he.le)
  · have hh : Real.log N < (f + η) * Real.log n :=
      (div_lt_iff₀ hln).mp (by linarith : Real.log N / Real.log n < f + η)
    have he := Real.exp_lt_exp.mpr hh
    rw [Real.exp_log hNr] at he
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hn')]
    exact (by simpa only [mul_comm] using he.le)

end HeightPaper
