module

public import HeightPaper.Analysis.FluidBarrier
public import Mathlib.Analysis.Normed.Group.Bounded

/-! # The macroscopic observation time and the logarithmic inversion scale -/

@[expose] public section

open Filter
open scoped Topology

namespace HeightPaper

/-- Changing from log(floor(T n)) to log n costs a bounded deterministic
quantity. In particular these two scales are never identified exactly. -/
theorem log_floor_sub_log_bounded {T : ℝ} (hT : 0 < T) :
    ∃ D > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
      0 < n ∧ 0 < ⌊T * n⌋₊ ∧ |Real.log (⌊T * n⌋₊ : ℝ) - Real.log n| ≤ D := by
  have hratio := (tendsto_floor_fraction hT.le).log hT.ne'
  obtain ⟨D, hD, hb⟩ := (Metric.isBounded_range_of_tendsto _ hratio).exists_pos_norm_le
  have ht : Tendsto (fun n : ℕ => ⌊T * n⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hT)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 1)
  refine ⟨D, hD, N + 1, ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have hH : 0 < ⌊T * n⌋₊ := hN n (by omega)
  refine ⟨hn0, hH, ?_⟩
  have hh := hb (Real.log ((⌊T * n⌋₊ : ℝ) / n)) ⟨n, rfl⟩
  rw [Real.log_div (by exact_mod_cast hH.ne') (by exact_mod_cast hn0.ne'), Real.norm_eq_abs] at hh
  exact hh

end HeightPaper
