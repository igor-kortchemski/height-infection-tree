module

public import HeightPaper.Probability.LocalProfileGeneralComplexAnalytic
public import HeightPaper.Probability.LocalProfileLimitMoment
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Conditional Lp tails on strict complex moment windows
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology ENNReal BigOperators

namespace HeightPaper.CountCoupling

/-- On a probability space, a higher integrable norm moment controls every
smaller positive norm moment. -/
theorem integral_norm_rpow_le_high_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℂ) (hf : AEStronglyMeasurable f μ)
    {q p : ℝ} (hq : 0 < q) (hqp : q ≤ p)
    (hfp : Integrable (fun ω ↦ ‖f ω‖ ^ p) μ) :
    (∫ ω, ‖f ω‖ ^ q ∂μ) ≤
      (∫ ω, ‖f ω‖ ^ p ∂μ) ^ (q / p) := by
  have hp : 0 < p := hq.trans_le hqp
  have hmem : MemLp f (ENNReal.ofReal p) μ := by
    have hfp' : Integrable (fun ω ↦ ‖f ω‖ ^ (ENNReal.ofReal p).toReal) μ := by
      simpa only [ENNReal.toReal_ofReal hp.le] using hfp
    exact (integrable_norm_rpow_iff hf (by simp [hp]) (by simp)).1 hfp'
  have hmemq : MemLp f (ENNReal.ofReal q) μ :=
    hmem.mono_exponent (ENNReal.ofReal_le_ofReal hqp)
  have hnorm := eLpNorm_le_eLpNorm_of_exponent_le
    (μ := μ) (f := f) (ENNReal.ofReal_le_ofReal hqp)
  have hreal := ENNReal.toReal_mono hmem.eLpNorm_ne_top hnorm
  rw [toReal_eLpNorm, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by simp [hq]) (by simp) hf,
    lpNorm_eq_integral_norm_rpow_toReal (by simp [hp]) (by simp) hf] at hreal
  simp only [ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal hp.le] at hreal
  have hIq : 0 ≤ (∫ ω, ‖f ω‖ ^ q ∂μ) :=
    integral_nonneg (fun ω ↦ Real.rpow_nonneg (norm_nonneg _) _)
  have hIp : 0 ≤ (∫ ω, ‖f ω‖ ^ p ∂μ) :=
    integral_nonneg (fun ω ↦ Real.rpow_nonneg (norm_nonneg _) _)
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg hIq _ ) hreal hq.le
  rw [Real.rpow_inv_rpow hIq hq.ne', ← Real.rpow_mul hIp] at hr
  convert hr using 1 <;> ring

/-- The canonical complex analytic limit inherits a common conditional
moment tail on every smaller disk inside a strict moment window. -/
theorem localProfile_ae_complex_disk_limit_moment_tail
    {l p : ℝ} {z₀ : ℂ} (hl : 1 < l)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (hz : z₀.re < profileRoot l)
    (he : complexProfileMomentExponent l z₀ p < -1) :
    ∃ η : ℝ, 0 < η ∧ ∃ r > (0 : ℝ),
      ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
        ∃ D : ℝ, 0 ≤ D ∧
          ∀ n : ℕ, ∀ z ∈ closedBall z₀ r, ∀ j : ℕ,
            localSafeCutoff l u ≤ j → 1 ≤ j →
            Integrable (fun ω ↦ ‖localAnalyticProfileLimit l n u ω z -
              Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p)
              (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
            (∫ ω, ‖localAnalyticProfileLimit l n u ω z -
              Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p
              ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤
                D * (j : ℝ) ^ (-η) := by
  obtain ⟨η, hη, ρ, hρ, hwindow⟩ :=
    exists_localProfile_complex_moment_disk hl hp hp2 hz he
  obtain ⟨R, hR, hcan⟩ :=
    localProfile_ae_canonical_complex_analytic_limit hl hp hp2 hz he
  let r := min (ρ / 2) (R / 2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrρ : r < ρ := by dsimp [r]; linarith [min_le_left (ρ / 2) (R / 2)]
  have hrR : r < R := by dsimp [r]; linarith [min_le_right (ρ / 2) (R / 2)]
  have hwindow' : ∀ z : ℂ, dist z z₀ < ρ →
      z.re < profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η :=
    fun z hz' ↦ hwindow l le_rfl z hz'
  refine ⟨η, hη, r, hr, ?_⟩
  filter_upwards [hcan l le_rfl,
    localProfile_ae_complex_window_moment_decay hl hp hp2 hη hwindow']
    with u hu hword
  intro hs
  obtain ⟨D, hD, _, hm⟩ := hword hs
  refine ⟨D, hD, ?_⟩
  intro n z hz' j hJj hj
  have hlim : ∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
      Tendsto (fun m ↦ Model.prescribedNormalizedProfile (Complex.exp z)
        (localBirth l u) (Model.initial n) (localSafeCutoff l u)
        (localSafeCutoff l u + 2 ^ m) (ω (localSafeCutoff l u + 2 ^ m))) atTop
        (𝓝 (localAnalyticProfileLimit l n u ω z)) := by
    filter_upwards [(hu hs n).1] with ω hω
    exact ((hω r hr.le hrR).1.tendsto_at hz')
  have hb (N : ℕ) (hjN : j ≤ N) :
      localProfileMomentDifference l u n z p j N ≤ D * (j : ℝ) ^ (-η) := by
    exact hm n z ((mem_closedBall.mp hz').trans_lt hrρ) j N hJj hj hjN
  exact localAnalyticProfileLimit_moment_sub_le l u n j z
    (zero_lt_one.trans hp) (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    hJj hlim hb

/-- The conditional `p`th moment tends to zero uniformly over each closed
complex disk inside the source moment domain. -/
theorem localProfile_ae_complex_disk_limit_uniform_lp
    {l p : ℝ} {z₀ : ℂ} (hl : 1 < l)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (hz : z₀.re < profileRoot l)
    (he : complexProfileMomentExponent l z₀ p < -1) :
    ∃ r > (0 : ℝ),
      ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
        ∀ ε > (0 : ℝ), ∀ᶠ j : ℕ in atTop,
          ∀ n : ℕ, ∀ z ∈ closedBall z₀ r,
            (∫ ω, ‖localAnalyticProfileLimit l n u ω z -
              Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p
              ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤ ε := by
  obtain ⟨η, hη, r, hr, hword⟩ :=
    localProfile_ae_complex_disk_limit_moment_tail hl hp hp2 hz he
  refine ⟨r, hr, ?_⟩
  filter_upwards [hword] with u hu
  intro hs ε hε
  obtain ⟨D, hD, htail⟩ := hu hs
  have hscale : Tendsto (fun j : ℕ => D * (j : ℝ) ^ (-η)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (((tendsto_rpow_neg_atTop hη).comp tendsto_natCast_atTop_atTop).const_mul D)
  filter_upwards [eventually_ge_atTop (localSafeCutoff l u), eventually_ge_atTop 1,
    hscale.eventually (Iio_mem_nhds hε)] with j hJj hj hsmall
  intro n z hz'
  exact (htail n z hz' j hJj hj).2.trans hsmall.le

end HeightPaper.CountCoupling
