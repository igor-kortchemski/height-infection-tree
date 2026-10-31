module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Logarithmic scales for geometric forest maxima -/

public section

open Filter
open scoped Topology

namespace HeightPaper

theorem tendsto_log_nat_atTop : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem eventually_nat_pos_of_log_ratio (N : ℕ → ℕ) {f : ℝ} (hf : 0 < f)
    (hN : Tendsto (fun n ↦ Real.log (N n) / Real.log n) atTop (𝓝 f)) :
    ∀ᶠ n in atTop, 0 < N n := by
  filter_upwards [hN.eventually (lt_mem_nhds hf)] with n hn
  by_contra hbad
  have hz : N n = 0 := Nat.eq_zero_of_not_pos hbad
  simp only [hz, Nat.cast_zero, Real.log_zero, zero_div, lt_self_iff_false] at hn

theorem tendsto_ceil_log_ratio {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ ↦ (⌈a * Real.log n⌉₊ : ℝ) / Real.log n) atTop (𝓝 a) :=
  (tendsto_nat_ceil_mul_div_atTop ha).comp tendsto_log_nat_atTop

/-- The logarithmic exponent of a variable geometric forest scale. -/
theorem tendsto_geometric_exponent_ratio (N H : ℕ → ℕ) (means : ℕ → ℝ)
    {f a m : ℝ} (hm : 0 < m)
    (hN : Tendsto (fun n ↦ Real.log (N n) / Real.log n) atTop (𝓝 f))
    (hH : Tendsto (fun n ↦ (H n : ℝ) / Real.log n) atTop (𝓝 a))
    (hmeans : Tendsto means atTop (𝓝 m)) :
    Tendsto (fun n ↦ (Real.log (N n) + (H n : ℝ) * Real.log (means n)) / Real.log n)
      atTop (𝓝 (f + a * Real.log m)) := by
  have ht := hN.add (hH.mul ((Real.continuousAt_log hm.ne').tendsto.comp hmeans))
  convert ht using 1
  funext n
  simp only [Function.comp_apply]
  ring

private theorem eventually_geometric_scale_exp (N H : ℕ → ℕ) (means : ℕ → ℝ)
    {f m : ℝ} (hf : 0 < f) (hm : 0 < m)
    (hN : Tendsto (fun n ↦ Real.log (N n) / Real.log n) atTop (𝓝 f))
    (hmeans : Tendsto means atTop (𝓝 m)) :
    ∀ᶠ n in atTop, (N n : ℝ) * means n ^ H n =
      Real.exp (Real.log (N n) + (H n : ℝ) * Real.log (means n)) := by
  filter_upwards [eventually_nat_pos_of_log_ratio N hf hN,
    hmeans.eventually (lt_mem_nhds hm)] with n hNn hmn
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hmn,
    Real.exp_log (by exact_mod_cast hNn)]

/-- A strict upper-height gap forces the geometric expected upper count to
zero, including a varying mean converging to a positive limit. -/
theorem tendsto_geometric_scale_zero (N H : ℕ → ℕ) (means : ℕ → ℝ)
    {f a m : ℝ} (hf : 0 < f) (hm : 0 < m)
    (hN : Tendsto (fun n ↦ Real.log (N n) / Real.log n) atTop (𝓝 f))
    (hH : Tendsto (fun n ↦ (H n : ℝ) / Real.log n) atTop (𝓝 a))
    (hmeans : Tendsto means atTop (𝓝 m)) (hgap : f + a * Real.log m < 0) :
    Tendsto (fun n ↦ (N n : ℝ) * means n ^ H n) atTop (𝓝 0) := by
  have hratio := tendsto_geometric_exponent_ratio N H means hm hN hH hmeans
  have hprod := tendsto_log_nat_atTop.atTop_mul_neg hgap hratio
  have hexponent : Tendsto
      (fun n ↦ Real.log (N n) + (H n : ℝ) * Real.log (means n)) atTop atBot := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hlog : Real.log n ≠ 0 := (Real.log_pos hn').ne'
    simp only [mul_div_cancel₀ _ hlog]
  apply (Real.tendsto_exp_atBot.comp hexponent).congr'
  exact (eventually_geometric_scale_exp N H means hf hm hN hmeans).mono (fun _ hn ↦ hn.symm)

/-- A strict lower-height gap makes the geometric expected count diverge. -/
theorem tendsto_geometric_scale_atTop (N H : ℕ → ℕ) (means : ℕ → ℝ)
    {f a m : ℝ} (hf : 0 < f) (hm : 0 < m)
    (hN : Tendsto (fun n ↦ Real.log (N n) / Real.log n) atTop (𝓝 f))
    (hH : Tendsto (fun n ↦ (H n : ℝ) / Real.log n) atTop (𝓝 a))
    (hmeans : Tendsto means atTop (𝓝 m)) (hgap : 0 < f + a * Real.log m) :
    Tendsto (fun n ↦ (N n : ℝ) * means n ^ H n) atTop atTop := by
  have hratio := tendsto_geometric_exponent_ratio N H means hm hN hH hmeans
  have hprod := tendsto_log_nat_atTop.atTop_mul_pos hgap hratio
  have hexponent : Tendsto
      (fun n ↦ Real.log (N n) + (H n : ℝ) * Real.log (means n)) atTop atTop := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hlog : Real.log n ≠ 0 := (Real.log_pos hn').ne'
    simp only [mul_div_cancel₀ _ hlog]
  apply (Real.tendsto_exp_atTop.comp hexponent).congr'
  exact (eventually_geometric_scale_exp N H means hf hm hN hmeans).mono (fun _ hn ↦ hn.symm)

end HeightPaper
