module

public import HeightPaper.Analysis.ComplexNormalizer
public import HeightPaper.Model.PrescribedShifted
public import HeightPaper.Model.RealNormalizer
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# The paper's shifted complex normalizer estimates

The actual prescribed-event product is written as the exponential of its
linear birth-reciprocal sum plus an explicit quadratic remainder. Smallness is
required only after the cutoff. Bounds are deterministic and uniform in the
complex weight on a common disk; their stochastic tightness assumptions are
not asserted here.
-/

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace HeightPaper.Model

/-- Each actual normalizer factor has the paper's reciprocal-count form. -/
theorem prescribedProfileFactor_eq_birthReciprocal (w : ℂ)
    (events : ℕ → Bool) (i₀ i : ℕ) :
    prescribedProfileFactor w (events i) (prescribedWalk events i₀ i) =
      1 + (w - 1) * (birthReciprocal events i₀ i : ℂ) := by
  cases he : events i <;>
    simp [prescribedProfileFactor, birthReciprocal, he, div_eq_mul_inv]

theorem prescribedNormalizerFrom_eq_birthReciprocal (w : ℂ)
    (events : ℕ → Bool) (i₀ j k : ℕ) :
    prescribedNormalizerFrom w events i₀ j k =
      ∏ i ∈ Finset.Ico j k, (1 + (w - 1) * (birthReciprocal events i₀ i : ℂ)) := by
  simp only [prescribedNormalizerFrom, prescribedProfileFactor_eq_birthReciprocal]

/-- The sum of the principal logarithm remainders after the cutoff. -/
noncomputable def normalizerRemainderFrom (w : ℂ) (events : ℕ → Bool)
    (i₀ j k : ℕ) : ℂ :=
  complexProductRemainder (Finset.Ico j k) (birthReciprocal events i₀) (w - 1)

theorem prescribedNormalizerFrom_eq_exp (w : ℂ) (events : ℕ → Bool)
    (i₀ j k : ℕ)
    (hsmall : ∀ i ∈ Finset.Ico j k,
      ‖w - 1‖ * birthReciprocal events i₀ i < 1) :
    prescribedNormalizerFrom w events i₀ j k =
      Complex.exp ((w - 1) * (∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i : ℝ) +
        normalizerRemainderFrom w events i₀ j k) := by
  rw [prescribedNormalizerFrom_eq_birthReciprocal]
  apply prod_one_add_eq_exp_complexProductRemainder
  intro i hi
  simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (birthReciprocal_nonneg events i₀ i)] using hsmall i hi

/-- The safe cutoff guarantees that the complex product does not vanish. -/
theorem prescribedNormalizerFrom_ne_zero_of_small (w : ℂ) (events : ℕ → Bool)
    (i₀ j k : ℕ)
    (hsmall : ∀ i ∈ Finset.Ico j k,
      ‖w - 1‖ * birthReciprocal events i₀ i < 1) :
    prescribedNormalizerFrom w events i₀ j k ≠ 0 := by
  rw [prescribedNormalizerFrom_eq_exp w events i₀ j k hsmall]
  exact Complex.exp_ne_zero _

/-- An explicit quadratic error for the shifted complex product. -/
theorem norm_normalizerRemainderFrom_le (w : ℂ) (events : ℕ → Bool)
    (i₀ j k : ℕ)
    (hsmall : ∀ i ∈ Finset.Ico j k,
      ‖w - 1‖ * birthReciprocal events i₀ i ≤ 1 / 2) :
    ‖normalizerRemainderFrom w events i₀ j k‖ ≤
      ‖w - 1‖ ^ 2 * ∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2 := by
  apply norm_complexProductRemainder_le
  intro i hi
  simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (birthReciprocal_nonneg events i₀ i)] using hsmall i hi

/-- The real part of the complex expansion controls the norm in the denominator
of the paper's moment ratios. -/
theorem prescribedNormalizerFrom_log_norm_remainder (w : ℂ) (events : ℕ → Bool)
    (i₀ j k : ℕ)
    (hsmall : ∀ i ∈ Finset.Ico j k,
      ‖w - 1‖ * birthReciprocal events i₀ i ≤ 1 / 2) :
    |Real.log ‖prescribedNormalizerFrom w events i₀ j k‖ -
      (w.re - 1) * ∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i| ≤
      ‖w - 1‖ ^ 2 * ∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2 := by
  rw [prescribedNormalizerFrom_eq_birthReciprocal]
  apply abs_log_norm_prod_one_add_sub_le
  intro i hi
  simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (birthReciprocal_nonneg events i₀ i)] using hsmall i hi

/-- The cutoff can be selected once for a whole disk of weights. -/
theorem norm_normalizerRemainderFrom_le_uniform (events : ℕ → Bool)
    (i₀ j k : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hsmall : ∀ i ∈ Finset.Ico j k, R * birthReciprocal events i₀ i ≤ 1 / 2) :
    ∀ w : ℂ, ‖w - 1‖ ≤ R →
      ‖normalizerRemainderFrom w events i₀ j k‖ ≤
        R ^ 2 * ∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2 := by
  intro w hw
  apply norm_complexProductRemainder_le_uniform _ _ hR _ (w - 1) hw
  intro i hi
  simpa only [abs_of_nonneg (birthReciprocal_nonneg events i₀ i)] using hsmall i hi

/-- The positive real normalizer with the same cutoff convention. -/
noncomputable def realNormalizerFrom (v : ℝ) (events : ℕ → Bool) (i₀ j k : ℕ) : ℝ :=
  ∏ i ∈ Finset.Ico j k, (1 + (v - 1) * birthReciprocal events i₀ i)

theorem prescribedNormalizerFrom_ofReal (v : ℝ) (events : ℕ → Bool)
    (i₀ j k : ℕ) :
    prescribedNormalizerFrom (v : ℂ) events i₀ j k =
      (realNormalizerFrom v events i₀ j k : ℂ) := by
  simp only [prescribedNormalizerFrom_eq_birthReciprocal, realNormalizerFrom,
    Complex.ofReal_prod, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one]

theorem realNormalizerFrom_pos {v : ℝ} (hv : 1 ≤ v) (events : ℕ → Bool)
    (i₀ j k : ℕ) : 0 < realNormalizerFrom v events i₀ j k := by
  apply Finset.prod_pos
  intro i hi
  have := mul_nonneg (sub_nonneg.mpr hv) (birthReciprocal_nonneg events i₀ i)
  linarith

theorem realNormalizerFrom_log_remainder {v : ℝ} (hv : 1 ≤ v)
    (events : ℕ → Bool) (i₀ j k : ℕ) :
    |Real.log (realNormalizerFrom v events i₀ j k) -
      (v - 1) * ∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i| ≤
      (v - 1) ^ 2 * ∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2 :=
  abs_log_prod_one_add_sub_le _ _ (sub_nonneg.mpr hv)
    (fun i _ ↦ birthReciprocal_nonneg events i₀ i)

/-- The moment-ratio expansion of `lem:asymptotics Cnkz`, with an explicit
quadratic error before applying probability estimates to the reciprocal sums. -/
theorem normalizerFrom_momentRatio_log_remainder {v : ℝ} (hv : 1 ≤ v)
    (w : ℂ) (p : ℝ) (events : ℕ → Bool) (i₀ j k : ℕ)
    (hsmall : ∀ i ∈ Finset.Ico j k,
      ‖w - 1‖ * birthReciprocal events i₀ i ≤ 1 / 2) :
    |Real.log (realNormalizerFrom v events i₀ j k /
        ‖prescribedNormalizerFrom w events i₀ j k‖ ^ p) -
      (v - 1 - p * (w.re - 1)) *
        ∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i| ≤
      ((v - 1) ^ 2 + |p| * ‖w - 1‖ ^ 2) *
        ∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2 := by
  have hC := realNormalizerFrom_pos hv events i₀ j k
  have hD : 0 < ‖prescribedNormalizerFrom w events i₀ j k‖ := norm_pos_iff.mpr
    (prescribedNormalizerFrom_ne_zero_of_small w events i₀ j k
      (fun i hi ↦ lt_of_le_of_lt (hsmall i hi) (by norm_num)))
  rw [Real.log_div hC.ne' (Real.rpow_pos_of_pos hD p).ne', Real.log_rpow hD p]
  have hreal := realNormalizerFrom_log_remainder hv events i₀ j k
  have hcomplex := prescribedNormalizerFrom_log_norm_remainder w events i₀ j k hsmall
  have heq : Real.log (realNormalizerFrom v events i₀ j k) -
      p * Real.log ‖prescribedNormalizerFrom w events i₀ j k‖ -
      (v - 1 - p * (w.re - 1)) * ∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i =
      (Real.log (realNormalizerFrom v events i₀ j k) -
        (v - 1) * ∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) -
      p * (Real.log ‖prescribedNormalizerFrom w events i₀ j k‖ -
        (w.re - 1) * ∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) := by ring
  rw [heq]
  have htri := abs_sub
    (Real.log (realNormalizerFrom v events i₀ j k) -
      (v - 1) * ∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i)
    (p * (Real.log ‖prescribedNormalizerFrom w events i₀ j k‖ -
      (w.re - 1) * ∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i))
  rw [abs_mul] at htri
  have hmul := mul_le_mul_of_nonneg_left hcomplex (abs_nonneg p)
  nlinarith only [htri, hreal, hmul]

/-- The preceding ratio estimate at the exponential tilts printed in the paper. -/
theorem normalizerFrom_exp_momentRatio_log_remainder (z : ℂ) {p : ℝ}
    (hp : 0 ≤ p) (hz : 0 ≤ z.re) (events : ℕ → Bool) (i₀ j k : ℕ)
    (hsmall : ∀ i ∈ Finset.Ico j k,
      ‖Complex.exp z - 1‖ * birthReciprocal events i₀ i ≤ 1 / 2) :
    |Real.log (realNormalizerFrom (Real.exp (p * z.re)) events i₀ j k /
        ‖prescribedNormalizerFrom (Complex.exp z) events i₀ j k‖ ^ p) -
      (Real.exp (p * z.re) - 1 - p * ((Complex.exp z).re - 1)) *
        ∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i| ≤
      ((Real.exp (p * z.re) - 1) ^ 2 + |p| * ‖Complex.exp z - 1‖ ^ 2) *
        ∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2 :=
  normalizerFrom_momentRatio_log_remainder
    (Real.one_le_exp_iff.mpr (mul_nonneg hp hz)) _ _ _ _ _ _ hsmall

/-- Common bounds for the centered reciprocal sum and square sum give a common
logarithmic error for all complex weights in a disk. -/
theorem normalizerFrom_log_norm_polynomial_error (events : ℕ → Bool)
    (i₀ j k : ℕ) {R B Q γ t : ℝ} (hR : 0 ≤ R)
    (hsmall : ∀ i ∈ Finset.Ico j k, R * birthReciprocal events i₀ i ≤ 1 / 2)
    (hcenter : |(∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) -
      γ * Real.log t| ≤ B)
    (hsquare : (∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2) ≤ Q)
    (w : ℂ) (hw : ‖w - 1‖ ≤ R) :
    |Real.log ‖prescribedNormalizerFrom w events i₀ j k‖ -
      γ * (w.re - 1) * Real.log t| ≤ R * B + R ^ 2 * Q := by
  have hsmall' : ∀ i ∈ Finset.Ico j k,
      ‖w - 1‖ * birthReciprocal events i₀ i ≤ 1 / 2 := by
    intro i hi
    exact (mul_le_mul_of_nonneg_right hw (birthReciprocal_nonneg events i₀ i)).trans
      (hsmall i hi)
  have hlog := prescribedNormalizerFrom_log_norm_remainder w events i₀ j k hsmall'
  have hre : |w.re - 1| ≤ R := by
    simpa only [Complex.sub_re, Complex.one_re] using
      (Complex.abs_re_le_norm (w - 1)).trans hw
  have heq : Real.log ‖prescribedNormalizerFrom w events i₀ j k‖ -
      γ * (w.re - 1) * Real.log t =
      (Real.log ‖prescribedNormalizerFrom w events i₀ j k‖ -
        (w.re - 1) * ∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) +
      (w.re - 1) * ((∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) -
        γ * Real.log t) := by ring
  rw [heq]
  calc
    _ ≤ |Real.log ‖prescribedNormalizerFrom w events i₀ j k‖ -
        (w.re - 1) * ∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i| +
      |(w.re - 1) * ((∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) -
        γ * Real.log t)| := abs_add_le _ _
    _ ≤ (‖w - 1‖ ^ 2 * ∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2) +
        R * B := by
      apply add_le_add hlog
      rw [abs_mul]
      exact mul_le_mul hre hcenter (abs_nonneg _) hR
    _ ≤ R * B + R ^ 2 * Q := by
      have hQ0 : 0 ≤ ∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2 :=
        Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
      have hp := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hw 2) hsquare hQ0
        (sq_nonneg R)
      linarith

/-- The paper's polynomial bounds for the norm, with constants independent of
the weight inside the safe disk. -/
theorem normalizerFrom_polynomial_bounds (events : ℕ → Bool)
    (i₀ j k : ℕ) {R B Q γ t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (hsmall : ∀ i ∈ Finset.Ico j k, R * birthReciprocal events i₀ i ≤ 1 / 2)
    (hcenter : |(∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) -
      γ * Real.log t| ≤ B)
    (hsquare : (∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2) ≤ Q)
    (w : ℂ) (hw : ‖w - 1‖ ≤ R) :
    Real.exp (-(R * B + R ^ 2 * Q)) * t ^ (γ * (w.re - 1)) ≤
        ‖prescribedNormalizerFrom w events i₀ j k‖ ∧
      ‖prescribedNormalizerFrom w events i₀ j k‖ ≤
        Real.exp (R * B + R ^ 2 * Q) * t ^ (γ * (w.re - 1)) := by
  have he := normalizerFrom_log_norm_polynomial_error events i₀ j k
    hR hsmall hcenter hsquare w hw
  have hn : 0 < ‖prescribedNormalizerFrom w events i₀ j k‖ := by
    apply norm_pos_iff.mpr
    apply prescribedNormalizerFrom_ne_zero_of_small
    intro i hi
    exact lt_of_le_of_lt
      ((mul_le_mul_of_nonneg_right hw (birthReciprocal_nonneg events i₀ i)).trans
        (hsmall i hi)) (by norm_num)
  have hpower (D : ℝ) : Real.exp D * t ^ (γ * (w.re - 1)) =
      Real.exp (D + γ * (w.re - 1) * Real.log t) := by
    rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
    congr 1
    ring
  constructor
  · rw [hpower]
    calc
      _ ≤ Real.exp (Real.log ‖prescribedNormalizerFrom w events i₀ j k‖) := by
        apply Real.exp_le_exp.mpr
        linarith [(abs_le.mp he).1]
      _ = _ := Real.exp_log hn
  · rw [hpower]
    calc
      _ = Real.exp (Real.log ‖prescribedNormalizerFrom w events i₀ j k‖) :=
        (Real.exp_log hn).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        linarith [(abs_le.mp he).2]

/-- Reindexing the shifted remainder by elapsed time after the cutoff. -/
theorem normalizerRemainderFrom_add (w : ℂ) (events : ℕ → Bool)
    (i₀ j N : ℕ) :
    normalizerRemainderFrom w events i₀ j (j + N) =
      complexProductRemainder (Finset.range N)
        (fun i ↦ birthReciprocal events i₀ (j + i)) (w - 1) := by
  simp only [normalizerRemainderFrom, complexProductRemainder,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

/-- The centered logarithm constructed from individual factor logarithms. -/
noncomputable def normalizerCenteredLogFrom (events : ℕ → Bool)
    (i₀ j k : ℕ) (γ : ℝ) (w : ℂ) : ℂ :=
  (w - 1) * (((∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) -
    γ * Real.log k : ℝ) : ℂ) + normalizerRemainderFrom w events i₀ j k

/-- The limiting analytic correction, retaining the weight multiplying the
centered reciprocal-sum limit. -/
noncomputable def normalizerLogLimitFrom (events : ℕ → Bool)
    (i₀ j : ℕ) (L : ℝ) (w : ℂ) : ℂ :=
  (w - 1) * (L : ℂ) + ∑' i,
    complexLogRemainder ((w - 1) * (birthReciprocal events i₀ (j + i) : ℂ))

/-- Exact factorization into the leading power and the centered logarithm. -/
theorem prescribedNormalizerFrom_eq_exp_centered (w : ℂ) (events : ℕ → Bool)
    (i₀ j k : ℕ) (γ : ℝ)
    (hsmall : ∀ i ∈ Finset.Ico j k,
      ‖w - 1‖ * birthReciprocal events i₀ i < 1) :
    prescribedNormalizerFrom w events i₀ j k =
      Complex.exp ((γ : ℂ) * (w - 1) * (Real.log k : ℂ) +
        normalizerCenteredLogFrom events i₀ j k γ w) := by
  rw [prescribedNormalizerFrom_eq_exp w events i₀ j k hsmall]
  congr 1
  simp only [normalizerCenteredLogFrom, Complex.ofReal_sub, Complex.ofReal_mul]
  ring

/-- The shifted normalizer has a uniform centered-logarithm limit on every
common safe disk whenever the pathwise reciprocal sum has its centered limit.
The physical time in the logarithm is `j + N`, so the cutoff is retained. -/
theorem normalizerCenteredLogFrom_tendstoUniformlyOn (events : ℕ → Bool)
    (i₀ j : ℕ) {R γ L : ℝ} (hR : 0 ≤ R)
    (hsquare : Summable (fun i ↦ (birthReciprocal events i₀ (j + i)) ^ 2))
    (hsmall : ∀ i, R * birthReciprocal events i₀ (j + i) ≤ 1 / 2)
    (hcenter : Tendsto (fun N ↦
      (∑ i ∈ Finset.Ico j (j + N), birthReciprocal events i₀ i) -
        γ * Real.log (j + N)) atTop (𝓝 L)) :
    TendstoUniformlyOn (fun N ↦ normalizerCenteredLogFrom events i₀ j (j + N) γ)
      (normalizerLogLimitFrom events i₀ j L) atTop (Metric.closedBall 1 R) := by
  have hlin := tendstoUniformlyOn_complex_mul_of_tendsto hR hcenter
  have hrem := complexProductRemainder_tendstoUniformlyOn
    (fun i ↦ birthReciprocal events i₀ (j + i)) hR hsquare (fun i ↦ by
      simpa only [abs_of_nonneg (birthReciprocal_nonneg events i₀ (j + i))] using hsmall i)
  have h := (hlin.add hrem).comp (fun w : ℂ ↦ w - 1)
  have hset : (fun w : ℂ ↦ w - 1) ⁻¹' Metric.closedBall 0 R = Metric.closedBall 1 R := by
    ext w
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  change TendstoUniformlyOn
    (fun N (w : ℂ) ↦ (w - 1) *
      (((∑ i ∈ Finset.Ico j (j + N), birthReciprocal events i₀ i) -
        γ * Real.log (j + N : ℕ) : ℝ) : ℂ) +
      normalizerRemainderFrom w events i₀ j (j + N))
    (fun w ↦ (w - 1) * (L : ℂ) + ∑' i,
      complexLogRemainder ((w - 1) * (birthReciprocal events i₀ (j + i) : ℂ)))
    atTop (Metric.closedBall 1 R)
  simpa only [hset, Function.comp_def, normalizerRemainderFrom_add, Pi.add_apply, Nat.cast_add] using h

/-- The correction appearing in the shifted normalizer asymptotic is analytic
inside the same safe disk. -/
theorem normalizerLogLimitFrom_analyticOnNhd (events : ℕ → Bool)
    (i₀ j : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hsquare : Summable (fun i ↦ (birthReciprocal events i₀ (j + i)) ^ 2))
    (hsmall : ∀ i, R * birthReciprocal events i₀ (j + i) ≤ 1 / 2) (L : ℝ) :
    AnalyticOnNhd ℂ (normalizerLogLimitFrom events i₀ j L) (Metric.ball 1 R) := by
  have h := complexNormalizerLimit_analyticOnNhd
    (fun i ↦ birthReciprocal events i₀ (j + i)) hR hsquare (fun i ↦ by
      simpa only [abs_of_nonneg (birthReciprocal_nonneg events i₀ (j + i))] using hsmall i) L
  apply h.comp (analyticOnNhd_id.sub analyticOnNhd_const)
  intro w hw
  simpa only [Metric.mem_ball, dist_eq_norm, sub_zero, Pi.sub_apply] using hw

/-- A count path tending to infinity admits one safe cutoff for an entire
compact set of complex tilts. This proves existence, not tightness or parameter
uniformity of the random cutoffs appearing in `lem:JnJ`. -/
theorem exists_safeCutoff_of_count_tendsto (events : ℕ → Bool) (i₀ : ℕ)
    (hcount : Tendsto (fun i ↦ (prescribedWalk events i₀ i : ℝ)) atTop atTop)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ J : ℕ, ∀ i ≥ J, ∀ z ∈ K,
      ‖Complex.exp z - 1‖ * birthReciprocal events i₀ i ≤ 1 / 2 := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
    (Complex.continuous_exp.sub continuous_const).continuousOn
  obtain ⟨J, hJ⟩ := eventually_atTop.mp ((tendsto_atTop.mp hcount) (2 * max R 0))
  refine ⟨J, ?_⟩
  intro i hi z hz
  have hbound : ‖Complex.exp z - 1‖ ≤ max R 0 := (hR z hz).trans (le_max_left _ _)
  have hc := hJ i hi
  unfold birthReciprocal
  cases events i
  · simp
  · simp only [↓reduceIte]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < (prescribedWalk events i₀ i : ℝ) + 1)).mpr
    linarith

/-- The analytic correction as a function of the paper's exponential tilt `z`.
The safe domain is expressed without choosing a branch of any global log. -/
theorem normalizerLogLimitFrom_exp_analyticOnNhd (events : ℕ → Bool)
    (i₀ j : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hsquare : Summable (fun i ↦ (birthReciprocal events i₀ (j + i)) ^ 2))
    (hsmall : ∀ i, R * birthReciprocal events i₀ (j + i) ≤ 1 / 2) (L : ℝ) :
    AnalyticOnNhd ℂ (fun z ↦ normalizerLogLimitFrom events i₀ j L (Complex.exp z))
      {z | ‖Complex.exp z - 1‖ < R} := by
  apply (normalizerLogLimitFrom_analyticOnNhd events i₀ j hR hsquare hsmall L).comp
    analyticOnNhd_cexp
  intro z hz
  simpa only [Metric.mem_ball, dist_eq_norm, Set.mem_ofPred_eq] using hz

end HeightPaper.Model
