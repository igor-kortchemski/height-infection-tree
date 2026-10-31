module

public import HeightPaper.Probability.FiniteFourierMoment
public import HeightPaper.Model.AnalyticProfileLimit

/-! # Conditional outer Fourier integrals of the finite epidemic profile -/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical

namespace HeightPaper

theorem finitePMF_integral_intervalL1 {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : PMF α) (hν : ν.support.Finite)
    (a b : ℝ) (f : α → ℝ → ℂ) (hf : ∀ q ∈ ν.support, Continuous (f q)) :
    (∫ q, (∫ v in a..b, ‖f q v‖) ∂ν.toMeasure) =
      ∫ v in a..b, ∫ q, ‖f q v‖ ∂ν.toMeasure := by
  rw [finitePMF_integral_eq_finset_sum ν hν]
  simp_rw [finitePMF_integral_eq_finset_sum ν hν]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_smul]
  · intro q hq
    exact ((hf q (by simpa using hq)).norm.intervalIntegrable a b).smul ((ν q).toReal)

theorem finitePMF_mean_norm_interval_le {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : PMF α) (hν : ν.support.Finite)
    {a b : ℝ} (hab : a ≤ b) (f : α → ℝ → ℂ)
    (hf : ∀ q ∈ ν.support, Continuous (f q)) {B : ℝ}
    (hB : ∀ v ∈ Icc a b, (∫ q, ‖f q v‖ ∂ν.toMeasure) ≤ B) :
    (∫ q, ‖∫ v in a..b, f q v‖ ∂ν.toMeasure) ≤ (b - a) * B := by
  have hi : IntervalIntegrable (fun v ↦ ∫ q, ‖f q v‖ ∂ν.toMeasure) volume a b := by
    simp_rw [finitePMF_integral_eq_finset_sum ν hν]
    convert (IntervalIntegrable.sum hν.toFinset (fun q hq ↦
      ((hf q (by simpa using hq)).norm.intervalIntegrable (μ := volume) a b).smul ((ν q).toReal))) using 1
    ext v
    simp only [Finset.sum_apply, Pi.smul_apply]
  calc
    _ ≤ ∫ q, (∫ v in a..b, ‖f q v‖) ∂ν.toMeasure :=
      integral_mono (FinitePMF.integrable_of_finite_support ν hν _)
        (FinitePMF.integrable_of_finite_support ν hν _)
        (fun q ↦ intervalIntegral.norm_integral_le_integral_norm hab)
    _ = ∫ v in a..b, ∫ q, ‖f q v‖ ∂ν.toMeasure := finitePMF_integral_intervalL1 ν hν a b f hf
    _ ≤ ∫ _v in a..b, B := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const hB
    _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]

theorem finitePMF_mean_norm_outer_le {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : PMF α) (hν : ν.support.Finite)
    (f : α → ℝ → ℂ) (hf : ∀ q ∈ ν.support, Continuous (f q))
    {B δ : ℝ} (hB0 : 0 ≤ B) (hδ : 0 ≤ δ) (hδπ : δ ≤ Real.pi)
    (hmean : ∀ v : ℝ, δ ≤ |v| → |v| ≤ Real.pi → (∫ q, ‖f q v‖ ∂ν.toMeasure) ≤ B) :
    (∫ q, ‖(∫ v in -Real.pi..-δ, f q v) + ∫ v in δ..Real.pi, f q v‖ ∂ν.toMeasure) ≤
      2 * Real.pi * B := by
  have hleft : (∫ q, ‖∫ v in -Real.pi..-δ, f q v‖ ∂ν.toMeasure) ≤
      (-δ - -Real.pi) * B := by
    apply finitePMF_mean_norm_interval_le ν hν (by linarith : -Real.pi ≤ -δ)
      f hf
    intro v hv
    apply hmean v
    · linarith [neg_le_abs v, hv.2]
    · exact abs_le.mpr ⟨hv.1, by linarith [Real.pi_pos, hv.2]⟩
  have hright : (∫ q, ‖∫ v in δ..Real.pi, f q v‖ ∂ν.toMeasure) ≤
      (Real.pi - δ) * B := by
    apply finitePMF_mean_norm_interval_le ν hν hδπ f hf
    intro v hv
    apply hmean v
    · exact hv.1.trans (le_abs_self v)
    · exact abs_le.mpr ⟨by linarith [Real.pi_pos, hv.1], hv.2⟩
  calc
    _ ≤ ∫ q, ‖∫ v in -Real.pi..-δ, f q v‖ +
        ‖∫ v in δ..Real.pi, f q v‖ ∂ν.toMeasure :=
      integral_mono (FinitePMF.integrable_of_finite_support ν hν _)
        (FinitePMF.integrable_of_finite_support ν hν _) (fun q ↦ norm_add_le _ _)
    _ = (∫ q, ‖∫ v in -Real.pi..-δ, f q v‖ ∂ν.toMeasure) +
        ∫ q, ‖∫ v in δ..Real.pi, f q v‖ ∂ν.toMeasure :=
      integral_add (FinitePMF.integrable_of_finite_support ν hν _)
        (FinitePMF.integrable_of_finite_support ν hν _)
    _ ≤ (-δ - -Real.pi) * B + (Real.pi - δ) * B := add_le_add hleft hright
    _ ≤ _ := by nlinarith

namespace CountCoupling

open Model

noncomputable def finiteSaddleIntegrand (l : ℝ) (k : ℕ) (x : ℝ)
    (q : FinitePath k) (v : ℝ) : ℂ :=
  normalizedActiveWeight (Complex.exp ((x : ℂ) + (v : ℂ) * Complex.I)) q.last /
      (Real.exp (growthFactor l * (Real.exp x - 1) * Real.log k) : ℂ) *
    Complex.exp (-((Real.log k * growthFactor l * Real.exp x * v : ℝ) : ℂ) * Complex.I)

theorem continuous_finiteSaddleIntegrand (l : ℝ) (k : ℕ) (x : ℝ) (q : FinitePath k) :
    Continuous (finiteSaddleIntegrand l k x q) := by
  unfold finiteSaddleIntegrand
  have hc : Continuous (fun v : ℝ ↦
      normalizedActiveWeight (Complex.exp ((x : ℂ) + (v : ℂ) * Complex.I)) q.last) :=
    (differentiable_normalizedActiveWeight_exp q.last).continuous.comp (by fun_prop)
  fun_prop

theorem norm_finiteSaddleIntegrand (l : ℝ) (k : ℕ) (x : ℝ) (q : FinitePath k) (v : ℝ) :
    ‖finiteSaddleIntegrand l k x q v‖ =
      ‖normalizedActiveWeight (Complex.exp ((x : ℂ) + (v : ℂ) * Complex.I)) q.last /
        (Real.exp (growthFactor l * (Real.exp x - 1) * Real.log k) : ℂ)‖ := by
  simp only [finiteSaddleIntegrand, norm_mul, Complex.norm_exp, Complex.mul_re,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, neg_zero, sub_self,
    Real.exp_zero, mul_one]

theorem finiteSaddleIntegrand_moment (l : ℝ) (n H k : ℕ) (u : ℕ → ℝ) (x v p : ℝ) :
    (∫ q, ‖finiteSaddleIntegrand l k x q v‖ ^ p
      ∂kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k) =
      finiteSaddleMoment l n H u k x ((x : ℂ) + (v : ℂ) * Complex.I) p := by
  simp only [norm_finiteSaddleIntegrand]
  rfl

noncomputable def finiteSaddleOuterIntegral (l : ℝ) (k : ℕ) (x δ : ℝ) (q : FinitePath k) : ℂ :=
  (∫ v in -Real.pi..-δ, finiteSaddleIntegrand l k x q v) +
    ∫ v in δ..Real.pi, finiteSaddleIntegrand l k x q v

theorem finiteSaddleScale_le_of_abs_ge {l η x p δ v : ℝ} (hl : 1 < l) (hp : 0 ≤ p)
    {k : ℕ} (hk : 1 ≤ k) (hδ : 0 ≤ δ) (hv : δ ≤ |v|) :
    finiteSaddleScale l η k x v p ≤ finiteSaddleScale l η k x δ p := by
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  have hγ := (growthFactor_pos hl).le
  have hcoef : 0 ≤ (2 / Real.pi ^ 2) * p * growthFactor l * Real.exp x * Real.log k := by positivity
  have hs : δ ^ 2 ≤ v ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hδ hv 2
  unfold finiteSaddleScale
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  apply add_le_add _ le_rfl
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hs hcoef]

theorem finiteSaddle_integrand_mean_le {l D η : ℝ} (hl : 1 < l) (hD : 0 ≤ D)
    {n H : ℕ} {u : ℕ → ℝ} (hs : ∀ i ≤ H, 0 < finiteWalk l n u i)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ H) (hJ : finiteSafeCutoff l n H u ≤ k)
    {x p δ v : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2 * profileRoot l)
    (hp : 1 < p) (hp2 : p ≤ 2) (hδ : 0 ≤ δ) (hvδ : δ ≤ |v|) (hvπ : |v| ≤ Real.pi)
    (hmargin : complexProfileMomentExponent l (x : ℂ) p ≤ -1 - η)
    (hgood : u ∉ finiteSaddleMomentBad η D l n H) :
    (∫ q, ‖finiteSaddleIntegrand l k x q v‖
      ∂kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k) ≤
      (D * finiteSaddleScale l η k x δ p) ^ p⁻¹ := by
  let ν := kernelPathLaw (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k
  have hν : ν.support.Finite :=
    finite_support_kernelPathLaw _ (fun i s ↦ finite_support_prescribedStep _ s) (initial n) k
  have hp0 : 0 < p := by linarith
  have hm : finiteSaddleMoment l n H u k x ((x : ℂ) + (v : ℂ) * Complex.I) p ≤
      D * finiteSaddleScale l η k x v p :=
    le_of_not_gt (fun h ↦ hgood ⟨hs, k, hk1, hk, hJ, x, hx0, hx, v, hvπ,
      p, ⟨hp, hp2⟩, hmargin, h⟩)
  have hmδ := hm.trans (mul_le_mul_of_nonneg_left
    (finiteSaddleScale_le_of_abs_ge hl hp0.le hk1 hδ hvδ) hD)
  have hLp : MemLp (fun q ↦ finiteSaddleIntegrand l k x q v) (ENNReal.ofReal p) ν.toMeasure := by
    apply (integrable_norm_rpow_iff (FinitePath.measurable _).aestronglyMeasurable
      (by simp [hp0]) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      FinitePMF.integrable_of_finite_support ν hν (fun q ↦ ‖finiteSaddleIntegrand l k x q v‖ ^ p)
  apply (integral_norm_le_moment_root ν.toMeasure hp.le hLp).trans
  apply Real.rpow_le_rpow (integral_nonneg (fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _))
    _ (by positivity)
  change (∫ q, ‖finiteSaddleIntegrand l k x q v‖ ^ p
    ∂kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k) ≤ _
  rw [finiteSaddleIntegrand_moment l n H k u x v p]
  exact hmδ

/-- Outside a central window, the actual conditional expected norm of the
two Fourier tails is bounded by the root of the existing uniform moment
envelope. Finite history support supplies every needed integrability fact. -/
theorem finiteSaddle_outer_integral_mean_le {l D η : ℝ} (hl : 1 < l) (hD : 0 ≤ D)
    {n H : ℕ} {u : ℕ → ℝ} (hs : ∀ i ≤ H, 0 < finiteWalk l n u i)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ H) (hJ : finiteSafeCutoff l n H u ≤ k)
    {x p δ : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2 * profileRoot l)
    (hp : 1 < p) (hp2 : p ≤ 2) (hδ : 0 ≤ δ) (hδπ : δ ≤ Real.pi)
    (hmargin : complexProfileMomentExponent l (x : ℂ) p ≤ -1 - η)
    (hgood : u ∉ finiteSaddleMomentBad η D l n H) :
    (∫ q, ‖finiteSaddleOuterIntegral l k x δ q‖
      ∂kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k) ≤
      2 * Real.pi * (D * finiteSaddleScale l η k x δ p) ^ p⁻¹ := by
  let ν := kernelPathLaw (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k
  have hν : ν.support.Finite :=
    finite_support_kernelPathLaw _ (fun i s ↦ finite_support_prescribedStep _ s) (initial n) k
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
  apply finitePMF_mean_norm_outer_le ν hν (finiteSaddleIntegrand l k x)
    (fun q _ ↦ continuous_finiteSaddleIntegrand l k x q)
    (Real.rpow_nonneg (by unfold finiteSaddleScale; positivity) _) hδ hδπ
  exact fun _ hvδ hvπ ↦ finiteSaddle_integrand_mean_le hl hD hs hk1 hk hJ
    hx0 hx hp hp2 hδ hvδ hvπ hmargin hgood

/-- Fourier inversion at an arbitrary real exponential scale. In particular,
`a = log n` need not agree with the event-time scale `log k`. -/
noncomputable def finiteSaddleIntegrandAtScale (l : ℝ) (k : ℕ) (a x : ℝ)
    (q : FinitePath k) (v : ℝ) : ℂ :=
  normalizedActiveWeight (Complex.exp ((x : ℂ) + (v : ℂ) * Complex.I)) q.last /
      (Real.exp (growthFactor l * (Real.exp x - 1) * a) : ℂ) *
    Complex.exp (-((a * growthFactor l * Real.exp x * v : ℝ) : ℂ) * Complex.I)

theorem continuous_finiteSaddleIntegrandAtScale (l : ℝ) (k : ℕ) (a x : ℝ)
    (q : FinitePath k) : Continuous (finiteSaddleIntegrandAtScale l k a x q) := by
  unfold finiteSaddleIntegrandAtScale
  have hc : Continuous (fun v : ℝ ↦
      normalizedActiveWeight (Complex.exp ((x : ℂ) + (v : ℂ) * Complex.I)) q.last) :=
    (differentiable_normalizedActiveWeight_exp q.last).continuous.comp (by fun_prop)
  fun_prop

theorem norm_finiteSaddleIntegrandAtScale (l : ℝ) (k : ℕ) (a x : ℝ)
    (q : FinitePath k) (v : ℝ) :
    ‖finiteSaddleIntegrandAtScale l k a x q v‖ =
      Real.exp (growthFactor l * (Real.exp x - 1) * (Real.log k - a)) *
        ‖finiteSaddleIntegrand l k x q v‖ := by
  rw [norm_finiteSaddleIntegrand]
  simp only [finiteSaddleIntegrandAtScale, norm_mul, Complex.norm_exp, Complex.mul_re,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, neg_zero, sub_self,
    Real.exp_zero, mul_one, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [mul_sub (growthFactor l * (Real.exp x - 1)) (Real.log k) a, Real.exp_sub]
  field_simp

noncomputable def finiteSaddleOuterIntegralAtScale (l : ℝ) (k : ℕ) (a x δ : ℝ)
    (q : FinitePath k) : ℂ :=
  (∫ v in -Real.pi..-δ, finiteSaddleIntegrandAtScale l k a x q v) +
    ∫ v in δ..Real.pi, finiteSaddleIntegrandAtScale l k a x q v

/-- The conditional Fourier-tail estimate retains the exact deterministic
change from event time to the chosen inversion scale. -/
theorem finiteSaddle_outer_integral_atScale_mean_le {l D η : ℝ} (hl : 1 < l) (hD : 0 ≤ D)
    {n H : ℕ} {u : ℕ → ℝ} (hs : ∀ i ≤ H, 0 < finiteWalk l n u i)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ H) (hJ : finiteSafeCutoff l n H u ≤ k)
    (a : ℝ) {x p δ : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2 * profileRoot l)
    (hp : 1 < p) (hp2 : p ≤ 2) (hδ : 0 ≤ δ) (hδπ : δ ≤ Real.pi)
    (hmargin : complexProfileMomentExponent l (x : ℂ) p ≤ -1 - η)
    (hgood : u ∉ finiteSaddleMomentBad η D l n H) :
    (∫ q, ‖finiteSaddleOuterIntegralAtScale l k a x δ q‖
      ∂kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k) ≤
      2 * Real.pi * Real.exp (growthFactor l * (Real.exp x - 1) * (Real.log k - a)) *
        (D * finiteSaddleScale l η k x δ p) ^ p⁻¹ := by
  let ν := kernelPathLaw (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k
  have hν : ν.support.Finite :=
    finite_support_kernelPathLaw _ (fun i s ↦ finite_support_prescribedStep _ s) (initial n) k
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
  have hB : 0 ≤ (D * finiteSaddleScale l η k x δ p) ^ p⁻¹ :=
    Real.rpow_nonneg (by unfold finiteSaddleScale; positivity) _
  have hmean (v : ℝ) (hvδ : δ ≤ |v|) (hvπ : |v| ≤ Real.pi) :
      (∫ q, ‖finiteSaddleIntegrandAtScale l k a x q v‖ ∂ν.toMeasure) ≤
        Real.exp (growthFactor l * (Real.exp x - 1) * (Real.log k - a)) *
          (D * finiteSaddleScale l η k x δ p) ^ p⁻¹ := by
    simp_rw [norm_finiteSaddleIntegrandAtScale]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (finiteSaddle_integrand_mean_le hl hD hs hk1 hk hJ hx0 hx hp hp2 hδ hvδ hvπ hmargin hgood)
      (Real.exp_pos _).le
  simpa only [finiteSaddleOuterIntegralAtScale, ν, kernelPathMeasure, mul_assoc] using
    finitePMF_mean_norm_outer_le ν hν (finiteSaddleIntegrandAtScale l k a x)
      (fun q _ ↦ continuous_finiteSaddleIntegrandAtScale l k a x q)
      (mul_nonneg (Real.exp_pos _).le hB) hδ hδπ hmean

end CountCoupling
end HeightPaper
