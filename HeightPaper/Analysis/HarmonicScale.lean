module

public import HeightPaper.Analysis.LogCounts
public import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Harmonic boundary terms at a diverging scale -/

public section

open Filter
open scoped Topology

namespace HeightPaper

theorem harmonic_sub_log_bounds (N : ℕ) :
    0 ≤ (harmonic N : ℝ) - Real.log N ∧ (harmonic N : ℝ) - Real.log N ≤ 1 := by
  have hlo : Real.log (N : ℝ) ≤ harmonic N := by
    simpa using log_le_harmonic_floor (N : ℝ) (Nat.cast_nonneg N)
  have hhi := harmonic_le_one_add_log N
  constructor <;> linarith

theorem tendsto_harmonic_ratio_of_log_ratio {ι : Type*} {ℓ : Filter ι}
    (N : ι → ℕ) (scale : ι → ℝ) (hscale : Tendsto scale ℓ atTop) {a : ℝ}
    (hlog : Tendsto (fun i ↦ Real.log (N i) / scale i) ℓ (𝓝 a)) :
    Tendsto (fun i ↦ (harmonic (N i) : ℝ) / scale i) ℓ (𝓝 a) := by
  have he : Tendsto (fun i ↦ ((harmonic (N i) : ℝ) - Real.log (N i)) / scale i)
      ℓ (𝓝 0) := by
    apply squeeze_zero' _ _ (hscale.const_div_atTop 1)
    · filter_upwards [hscale.eventually_gt_atTop 0] with i hi
      exact div_nonneg (harmonic_sub_log_bounds (N i)).1 hi.le
    · filter_upwards [hscale.eventually_gt_atTop 0] with i hi
      exact div_le_div_of_nonneg_right (harmonic_sub_log_bounds (N i)).2 hi.le
  have hh := he.add hlog
  rw [zero_add] at hh
  convert hh using 1
  funext i
  ring

end HeightPaper
