module

public import HeightPaper.Analysis.LogCounts
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # A divergent cutoff negligible on the terminal logarithmic scale -/

@[expose] public section

open Filter
open scoped Topology

namespace HeightPaper

noncomputable def logCutoff (N : ℕ) : ℕ := ⌊Real.log N⌋₊

theorem tendsto_logCutoff_atTop : Tendsto logCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem eventually_logCutoff_le : ∀ᶠ N : ℕ in atTop, logCutoff N ≤ N := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply Nat.le_of_lt_succ
  apply (Nat.floor_lt (Real.log_natCast_nonneg N)).mpr
  exact (Real.log_le_sub_one_of_pos hNp).trans_lt (by push_cast; linarith)

theorem tendsto_log_logCutoff_div_log :
    Tendsto (fun N : ℕ ↦ Real.log (logCutoff N) / Real.log N) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hlog.eventually_gt_atTop 0] with N hN
    exact div_nonneg (Real.log_natCast_nonneg _) hN.le
  · filter_upwards [tendsto_logCutoff_atTop.eventually (eventually_ge_atTop 1),
      hlog.eventually_gt_atTop 0] with N hJ hN
    apply div_le_div_of_nonneg_right _ hN.le
    apply Real.log_le_log (by exact_mod_cast (show 0 < logCutoff N by omega))
    exact Nat.floor_le hN.le

theorem moment_error_power_eq {M d J u D p : ℝ} (hd : 0 ≤ d) (hJ : 0 < J) :
    M * J ^ u / (d * J ^ (-D)) ^ p = (M / d ^ p) * J ^ (u + D * p) := by
  rw [Real.mul_rpow hd (Real.rpow_nonneg hJ.le _), ← Real.rpow_mul hJ.le,
    show -D * p = -(D * p) by ring, Real.rpow_neg hJ.le, Real.rpow_add hJ]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem tendsto_moment_error_power_zero {M d u D p : ℝ} (hd : 0 ≤ d)
    (hexp : u + D * p < 0) (J : ℕ → ℕ) (hJ : Tendsto J atTop atTop) :
    Tendsto (fun N ↦ M * (J N : ℝ) ^ u / (d * (J N : ℝ) ^ (-D)) ^ p)
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun N ↦ (J N : ℝ) ^ (u + D * p)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (neg_pos.mpr hexp)).comp
      (tendsto_natCast_atTop_atTop.comp hJ) using 1
    simp only [neg_neg, Function.comp_def]
  have hh := hpow.const_mul (M / d ^ p)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hJ.eventually (eventually_ge_atTop 1)] with N hN
  exact (moment_error_power_eq hd (by exact_mod_cast (show 0 < J N by omega))).symm

/-- Any fixed power lost at the logarithmic cutoff is smaller than an
arbitrarily small positive power of the terminal index. -/
theorem eventually_rpow_le_mul_logCutoff_rpow {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (a D : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (a - ε) ≤ C * (N : ℝ) ^ a * (logCutoff N : ℝ) ^ (-D) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hratio : Tendsto (fun N : ℕ ↦ Real.log C / Real.log N + ε -
      D * (Real.log (logCutoff N) / Real.log N)) atTop (𝓝 ε) := by
    convert ((tendsto_const_nhds (x := Real.log C)).div_atTop hlog).add_const ε |>.sub
      (tendsto_log_logCutoff_div_log.const_mul D) using 1 <;> simp
  filter_upwards [hratio.eventually_const_lt hε, hlog.eventually_gt_atTop 0,
    tendsto_logCutoff_atTop.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1]
      with N hr hlogN hJ hN
  change 0 < Real.log N at hlogN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hJp : (0 : ℝ) < logCutoff N := by exact_mod_cast (show 0 < logCutoff N by omega)
  have he : (a - ε) * Real.log N ≤ Real.log C + a * Real.log N - D * Real.log (logCutoff N) := by
    have hh := mul_pos hr hlogN
    field_simp [hlogN.ne'] at hh
    nlinarith only [hh]
  rw [Real.rpow_def_of_pos hNp, Real.rpow_def_of_pos hNp, Real.rpow_def_of_pos hJp]
  rw [show C = Real.exp (Real.log C) from (Real.exp_log hC).symm,
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [he]

end HeightPaper
