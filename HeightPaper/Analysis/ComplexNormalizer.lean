module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The complex logarithmic normalizer

These are the deterministic log-product arguments used in the paper's
`lem:asymptotics Cnkz` and `lemme majoration C`. The logarithm is taken separately
for each factor; no claim that the principal logarithm of a product is additive
is needed. A common radius gives constants uniform over the complex parameter.
-/

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace HeightPaper

/-- The quadratic remainder in the principal logarithm near one. -/
noncomputable def complexLogRemainder (z : ℂ) : ℂ := Complex.log (1 + z) - z

/-- The exact quadratic bound used in the manuscript, including the boundary
of the disk of radius one half. -/
theorem norm_complexLogRemainder_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖complexLogRemainder z‖ ≤ ‖z‖ ^ 2 := by
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1 - ‖z‖)]
    linarith
  calc
    _ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := Complex.norm_log_one_add_sub_self_le hz1
    _ ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
    _ = _ := by ring

theorem complex_one_add_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ≠ 0 := by
  intro h
  have heq : z = -1 := by linear_combination h
  simp [heq] at hz

/-- Sum of the individual logarithmic remainders of a finite product. -/
noncomputable def complexProductRemainder {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ i ∈ s, complexLogRemainder (z * (a i : ℂ))

/-- A factorwise smallness condition gives an exact exponential representation.
It also records the branch choice used in the paper's logarithmic expansion. -/
theorem prod_one_add_eq_exp_complexProductRemainder {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (z : ℂ) (hsmall : ∀ i ∈ s, ‖z * (a i : ℂ)‖ < 1) :
    (∏ i ∈ s, (1 + z * (a i : ℂ))) =
      Complex.exp (z * (∑ i ∈ s, a i : ℝ) + complexProductRemainder s a z) := by
  have heq : z * (∑ i ∈ s, a i : ℝ) + complexProductRemainder s a z =
      ∑ i ∈ s, Complex.log (1 + z * (a i : ℂ)) := by
    simp only [complexProductRemainder, complexLogRemainder, Complex.ofReal_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  exact (Complex.exp_log (complex_one_add_ne_zero (hsmall i hi))).symm

theorem norm_complexProductRemainder_le {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (z : ℂ) (hsmall : ∀ i ∈ s, ‖z * (a i : ℂ)‖ ≤ 1 / 2) :
    ‖complexProductRemainder s a z‖ ≤ ‖z‖ ^ 2 * ∑ i ∈ s, (a i) ^ 2 := by
  calc
    _ ≤ ∑ i ∈ s, ‖complexLogRemainder (z * (a i : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖z * (a i : ℂ)‖ ^ 2 :=
      Finset.sum_le_sum (fun i hi ↦ norm_complexLogRemainder_le (hsmall i hi))
    _ = _ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
        Finset.mul_sum]

/-- The real logarithm of the product's norm has the real part of the same
quadratic remainder. No principal-logarithm additivity is assumed. -/
theorem log_norm_prod_one_add {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (z : ℂ) (hsmall : ∀ i ∈ s, ‖z * (a i : ℂ)‖ < 1) :
    Real.log ‖∏ i ∈ s, (1 + z * (a i : ℂ))‖ =
      z.re * ∑ i ∈ s, a i + (complexProductRemainder s a z).re := by
  rw [prod_one_add_eq_exp_complexProductRemainder s a z hsmall, Complex.norm_exp,
    Real.log_exp]
  simp

theorem abs_log_norm_prod_one_add_sub_le {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (z : ℂ) (hsmall : ∀ i ∈ s, ‖z * (a i : ℂ)‖ ≤ 1 / 2) :
    |Real.log ‖∏ i ∈ s, (1 + z * (a i : ℂ))‖ - z.re * ∑ i ∈ s, a i| ≤
      ‖z‖ ^ 2 * ∑ i ∈ s, (a i) ^ 2 := by
  rw [log_norm_prod_one_add s a z (fun i hi ↦
    lt_of_le_of_lt (hsmall i hi) (by norm_num)), add_sub_cancel_left]
  exact (Complex.abs_re_le_norm _).trans (norm_complexProductRemainder_le s a z hsmall)

/-- One constant controls the error simultaneously for all parameters in a
closed disk, rather than a different constant for each parameter. -/
theorem norm_complexProductRemainder_le_uniform {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) {R : ℝ} (_hR : 0 ≤ R)
    (hsmall : ∀ i ∈ s, R * |a i| ≤ 1 / 2) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖complexProductRemainder s a z‖ ≤ R ^ 2 * ∑ i ∈ s, (a i) ^ 2 := by
  intro z hz
  have hs : ∀ i ∈ s, ‖z * (a i : ℂ)‖ ≤ 1 / 2 := by
    intro i hi
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hz (abs_nonneg _)).trans (hsmall i hi)
  exact (norm_complexProductRemainder_le s a z hs).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz 2)
      (Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)))

/-- Square summability gives uniform convergence of the error series on the
whole disk, the deterministic convergence step in `lemme majoration C`. -/
theorem complexProductRemainder_tendstoUniformlyOn (a : ℕ → ℝ) {R : ℝ}
    (_hR : 0 ≤ R) (ha : Summable (fun i ↦ (a i) ^ 2))
    (hsmall : ∀ i, R * |a i| ≤ 1 / 2) :
    TendstoUniformlyOn (fun N z ↦ complexProductRemainder (Finset.range N) a z)
      (fun z ↦ ∑' i, complexLogRemainder (z * (a i : ℂ))) atTop
      (Metric.closedBall 0 R) := by
  apply tendstoUniformlyOn_tsum_nat (ha.mul_left (R ^ 2))
  intro i z hz
  have hzR : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hs : ‖z * (a i : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hzR (abs_nonneg _)).trans (hsmall i)
  calc
    _ ≤ ‖z * (a i : ℂ)‖ ^ 2 := norm_complexLogRemainder_le hs
    _ = ‖z‖ ^ 2 * (a i) ^ 2 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    _ ≤ R ^ 2 * (a i) ^ 2 := by gcongr

/-- The uniformly convergent correction is analytic inside the common safe
parameter disk. This supplies the analytic function in the deterministic part
of `lemme majoration C`. -/
theorem complexLogRemainderSeries_analyticOnNhd (a : ℕ → ℝ) {R : ℝ}
    (_hR : 0 ≤ R) (ha : Summable (fun i ↦ (a i) ^ 2))
    (hsmall : ∀ i, R * |a i| ≤ 1 / 2) :
    AnalyticOnNhd ℂ (fun z ↦ ∑' i, complexLogRemainder (z * (a i : ℂ)))
      (Metric.ball 0 R) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  apply Complex.differentiableOn_tsum_of_summable_norm (ha.mul_left (R ^ 2))
  · intro i z hz
    have hzR : ‖z‖ ≤ R := (by
      simpa only [Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < R).le
    have hs : ‖z * (a i : ℂ)‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hzR (abs_nonneg _)).trans (hsmall i)
    have hslit : 1 + z * (a i : ℂ) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      have hre := (abs_le.mp (Complex.abs_re_le_norm (z * (a i : ℂ)))).1
      simp only [Complex.add_re, Complex.one_re]
      linarith
    exact (((differentiableAt_const (1 : ℂ)).add
      (differentiableAt_id.mul_const (a i : ℂ))).clog hslit).sub
      (differentiableAt_id.mul_const (a i : ℂ)) |>.differentiableWithinAt
  · exact Metric.isOpen_ball
  · intro i z hz
    have hzR : ‖z‖ ≤ R := (by
      simpa only [Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < R).le
    have hs : ‖z * (a i : ℂ)‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hzR (abs_nonneg _)).trans (hsmall i)
    calc
      _ ≤ ‖z * (a i : ℂ)‖ ^ 2 := norm_complexLogRemainder_le hs
      _ = ‖z‖ ^ 2 * (a i) ^ 2 := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      _ ≤ R ^ 2 * (a i) ^ 2 := by gcongr

/-- Scalar convergence can be multiplied by a complex parameter uniformly on
any bounded disk. -/
theorem tendstoUniformlyOn_complex_mul_of_tendsto {b : ℕ → ℝ} {L R : ℝ}
    (hR : 0 ≤ R) (hb : Tendsto b atTop (𝓝 L)) :
    TendstoUniformlyOn (fun N (z : ℂ) ↦ z * (b N : ℂ)) (fun z ↦ z * (L : ℂ))
      atTop (Metric.closedBall 0 R) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hR1 : 0 < R + 1 := by linarith
  filter_upwards [Metric.tendsto_nhds.mp hb (ε / (R + 1)) (div_pos hε hR1)] with N hN
  intro z hz
  have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hN' : |b N - L| < ε / (R + 1) := by simpa only [Real.dist_eq] using hN
  rw [dist_eq_norm, ← mul_sub, ← Complex.ofReal_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_sub_comm L (b N)]
  calc
    ‖z‖ * |b N - L| ≤ (R + 1) * |b N - L| := by gcongr; linarith
    _ < (R + 1) * (ε / (R + 1)) := mul_lt_mul_of_pos_left hN' hR1
    _ = ε := mul_div_cancel₀ ε hR1.ne'

/-- A limit for the centered reciprocal sum yields a uniform complex limit for
the centered logarithmic product. The only stochastic input needed to apply
this pathwise theorem is the stated reciprocal-sum convergence and square
summability. -/
theorem complexNormalizerCentered_tendstoUniformlyOn (a : ℕ → ℝ)
    {R γ L : ℝ} (hR : 0 ≤ R) (ha : Summable (fun i ↦ (a i) ^ 2))
    (hsmall : ∀ i, R * |a i| ≤ 1 / 2)
    (hcenter : Tendsto (fun N ↦ (∑ i ∈ Finset.range N, a i) - γ * Real.log N)
      atTop (𝓝 L)) :
    TendstoUniformlyOn
      (fun N z ↦ z * (((∑ i ∈ Finset.range N, a i) - γ * Real.log N : ℝ) : ℂ) +
        complexProductRemainder (Finset.range N) a z)
      (fun z ↦ z * (L : ℂ) + ∑' i, complexLogRemainder (z * (a i : ℂ)))
      atTop (Metric.closedBall 0 R) := by
  exact (tendstoUniformlyOn_complex_mul_of_tendsto hR hcenter).add
    (complexProductRemainder_tendstoUniformlyOn a hR ha hsmall)

/-- The limiting centered logarithmic normalizer is analytic. -/
theorem complexNormalizerLimit_analyticOnNhd (a : ℕ → ℝ) {R : ℝ}
    (hR : 0 ≤ R) (ha : Summable (fun i ↦ (a i) ^ 2))
    (hsmall : ∀ i, R * |a i| ≤ 1 / 2) (L : ℝ) :
    AnalyticOnNhd ℂ
      (fun z ↦ z * (L : ℂ) + ∑' i, complexLogRemainder (z * (a i : ℂ)))
      (Metric.ball 0 R) :=
  (analyticOnNhd_id.mul analyticOnNhd_const).add
    (complexLogRemainderSeries_analyticOnNhd a hR ha hsmall)

end HeightPaper
