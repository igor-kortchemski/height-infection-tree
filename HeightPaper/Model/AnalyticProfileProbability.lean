module

public import HeightPaper.Model.AnalyticProfilePolynomial
public import HeightPaper.Probability.UniformLimitMeasure

/-!
# Full-time local uniform convergence in probability

Cauchy's formula and the explicit moment tail control the simultaneous
deviation on an inner disk. The common analytic dyadic limit inherits that
bound by continuity from below of the trajectory measure.
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology BigOperators ENNReal

namespace HeightPaper.Model

theorem measurable_analyticSequenceLimit_eval {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℂ → ℂ) (z : ℂ) (hF : ∀ m, Measurable (fun ω => F m ω z)) :
    Measurable (fun ω => analyticSequenceLimit F ω z) :=
  (hF 0).add (Measurable.tsum (fun m => (hF (m + 1)).sub (hF m)))

theorem prescribedTrajectory_limit_aemeasurable (events : ℕ → Bool)
    (s₀ : State) (J : ℕ) (z : ℂ) (times : ℕ → ℕ) (L : (ℕ → State) → ℂ)
    (hlim : ∀ᵐ ω ∂prescribedTrajectoryMeasure events s₀,
      Tendsto (fun m => prescribedNormalizedProfile (Complex.exp z) events s₀ J
        (times m) (ω (times m))) atTop (𝓝 (L ω))) :
    AEMeasurable L (prescribedTrajectoryMeasure events s₀) := by
  apply aemeasurable_of_tendsto_metrizable_ae' _ hlim
  intro m
  exact ((measurable_state (prescribedNormalizedProfile (Complex.exp z) events s₀ J (times m))).comp
    (measurable_pi_apply (X := fun _ : ℕ => State) (times m))).aemeasurable

theorem prescribedTrajectory_uniform_difference_probability_le_of_two_normalizers
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) (z₀ : ℂ) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) {j k : ℕ} (hJj : J ≤ j) (hjk : j ≤ k)
    (hCj : ∀ z ∈ closedBall z₀ R,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J j ≠ 0)
    (hCk : ∀ z ∈ closedBall z₀ R,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0)
    {p B ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε)
    (hbound : ∀ z ∈ sphere z₀ R,
      (∫ ω, ‖prescribedNormalizedProfile (Complex.exp z) events s₀ J k (ω k) -
          prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)‖ ^ p
        ∂prescribedTrajectoryMeasure events s₀) ≤ B) :
    (prescribedTrajectoryMeasure events s₀).real
      {ω | ∃ z ∈ closedBall z₀ r,
        ε < ‖prescribedNormalizedProfile (Complex.exp z) events s₀ J k (ω k) -
          prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)‖} ≤
      (R / (2 * Real.pi * (R - r)) * (2 * Real.pi) * B ^ p⁻¹) / ε := by
  let μ := prescribedTrajectoryMeasure events s₀
  let F (ω : ℕ → State) (z : ℂ) :=
    prescribedNormalizedProfile (Complex.exp z) events s₀ J k (ω k) -
      prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)
  let D (q : FinitePath k) (z : ℂ) :=
    prescribedNormalizedProfile (Complex.exp z) events s₀ J k q.last -
      prescribedNormalizedProfile (Complex.exp z) events s₀ J j (q.eval j)
  let C := R / (2 * Real.pi * (R - r))
  have hR : 0 < R := hr.trans_lt hrR
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hdiff (ω : ℕ → State) : DifferentiableOn ℂ (F ω) (closedBall z₀ R) :=
    (differentiableOn_prescribedNormalizedProfile_exp events s₀ _ J k
      hCk).sub
      (differentiableOn_prescribedNormalizedProfile_exp events s₀ _ J j hCj)
  have hcont (q : FinitePath k) : ContinuousOn (D q) (sphere z₀ |R|) := by
    rw [abs_of_pos hR]
    exact ((differentiableOn_prescribedNormalizedProfile_exp events s₀ _ J k
      hCk).sub
      (differentiableOn_prescribedNormalizedProfile_exp events s₀ _ J j hCj)).continuousOn.mono
      sphere_subset_closedBall
  have heq (ω : ℕ → State) : D (trajectoryPrefix k ω) = F ω := by
    ext z
    simp only [D, F, trajectoryPrefix_last, trajectoryPrefix_eval k _ j hjk]
  have hi : Integrable (fun ω => circleL1 z₀ R (F ω)) μ := by
    have h := kernelTrajectory_integrable_prefix (fun i => prescribedStep (events i))
      (fun i s => finite_support_prescribedStep (events i) s) s₀ k
      (fun q => circleL1 z₀ R (D q))
    simpa only [heq, μ, prescribedTrajectoryMeasure] using h
  have hLp (z : ℂ) (i : ℕ) (hi : J ≤ i) : MemLp
      (fun ω => prescribedNormalizedProfile (Complex.exp z) events s₀ J i (ω i))
      (ENNReal.ofReal p) μ := by
    have h := prescribedTrajectory_profile_memLp (Complex.exp z) events s₀ J
      (i - J) (lt_of_lt_of_le zero_lt_one hp)
    simpa only [Nat.add_sub_of_le hi] using h
  have hmean : (∫ ω, circleL1 z₀ R (F ω) ∂μ) ≤ (2 * Real.pi) * B ^ p⁻¹ := by
    have htransfer := kernelTrajectory_integral_prefix (fun i => prescribedStep (events i))
      s₀ k (fun q => circleL1 z₀ R (D q))
    simp only [heq] at htransfer
    change (∫ ω, circleL1 z₀ R (F ω)
      ∂FinitePMF.kernelTrajectoryMeasure _ (fun _ => measurable_state _) s₀) ≤ _
    rw [htransfer]
    apply finitePMF_integral_circleL1_le _
      (finite_support_kernelPathLaw _ (fun i s => finite_support_prescribedStep (events i) s) s₀ k)
      z₀ R D (fun q _ => hcont q)
    intro z hz
    have he := kernelTrajectory_integral_prefix (fun i => prescribedStep (events i))
      s₀ k (fun q => ‖D q z‖)
    simp only [heq] at he
    change (∫ q, ‖D q z‖ ∂kernelPathMeasure _ s₀ k) ≤ B ^ p⁻¹
    rw [← he]
    exact (integral_norm_le_moment_root μ hp
      ((hLp z k (hJj.trans hjk)).sub (hLp z j hJj))).trans
      (Real.rpow_le_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))
        (hbound z (by simpa only [abs_of_pos hR] using hz)) (by positivity))
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => C * circleL1 z₀ R (F ω))
    (ae_of_all μ (fun ω => mul_nonneg hC0 (circleL1_nonneg _ _ _))) (hi.const_mul C) ε
  have hsub : {ω | ∃ z ∈ closedBall z₀ r, ε < ‖F ω z‖} ⊆
      {ω | ε ≤ C * circleL1 z₀ R (F ω)} := by
    rintro ω ⟨z, hz, he⟩
    exact he.le.trans (norm_le_circleL1 hr hrR (hdiff ω) hz)
  calc
    _ ≤ μ.real {ω | ε ≤ C * circleL1 z₀ R (F ω)} := measureReal_mono hsub
    _ ≤ (∫ ω, C * circleL1 z₀ R (F ω) ∂μ) / ε :=
      (le_div_iff₀ hε).mpr (by nlinarith [hmarkov])
    _ ≤ _ := by
      rw [integral_const_mul]
      apply div_le_div_of_nonneg_right _ hε.le
      simpa only [C, mul_assoc] using mul_le_mul_of_nonneg_left hmean hC0

theorem prescribedTrajectory_uniform_difference_probability_le
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) (z₀ : ℂ) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) {j k : ℕ} (hJj : J ≤ j) (hjk : j ≤ k)
    (hC : ∀ i ≥ J, ∀ z ∈ closedBall z₀ R,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J i ≠ 0)
    {p B ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε)
    (hbound : ∀ z ∈ sphere z₀ R,
      (∫ ω, ‖prescribedNormalizedProfile (Complex.exp z) events s₀ J k (ω k) -
          prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)‖ ^ p
        ∂prescribedTrajectoryMeasure events s₀) ≤ B) :
    (prescribedTrajectoryMeasure events s₀).real
      {ω | ∃ z ∈ closedBall z₀ r,
        ε < ‖prescribedNormalizedProfile (Complex.exp z) events s₀ J k (ω k) -
          prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)‖} ≤
      (R / (2 * Real.pi * (R - r)) * (2 * Real.pi) * B ^ p⁻¹) / ε :=
  prescribedTrajectory_uniform_difference_probability_le_of_two_normalizers events s₀ J z₀
    hr hrR hJj hjk (hC j hJj) (hC k (hJj.trans hjk)) hp hε hbound

/-- The common dyadic analytic version satisfies a uniform probability tail
at every later physical time, not just at dyadic times. -/
theorem prescribedTrajectory_uniform_limit_probability_le
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) (z₀ : ℂ) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hC : ∀ i ≥ J, ∀ z ∈ closedBall z₀ R,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J i ≠ 0)
    {p D η : ℝ} (hp : 1 ≤ p) (hD : 0 ≤ D) (_hη : 0 < η)
    (hbound : ∀ j k : ℕ, J ≤ j → 1 ≤ j → j ≤ k → ∀ z ∈ sphere z₀ R,
      (∫ ω, ‖prescribedNormalizedProfile (Complex.exp z) events s₀ J k (ω k) -
          prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)‖ ^ p
        ∂prescribedTrajectoryMeasure events s₀) ≤ D * (j : ℝ) ^ (-η))
    (L : (ℕ → State) → ℂ → ℂ)
    (hlim : ∀ᵐ ω ∂prescribedTrajectoryMeasure events s₀,
      TendstoUniformlyOn
        (fun m z => prescribedNormalizedProfile (Complex.exp z) events s₀ J
          (J + 2 ^ m) (ω (J + 2 ^ m))) (L ω) atTop (closedBall z₀ r))
    {j : ℕ} (hJj : J ≤ j) (hj : 1 ≤ j) {ε : ℝ} (hε : 0 < ε) :
    (prescribedTrajectoryMeasure events s₀).real
      {ω | ∃ z ∈ closedBall z₀ r,
        ε < ‖L ω z - prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)‖} ≤
      (R / (2 * Real.pi * (R - r)) * (2 * Real.pi) *
        (D * (j : ℝ) ^ (-η)) ^ p⁻¹) / (ε / 2) := by
  let μ := prescribedTrajectoryMeasure events s₀
  let C := (R / (2 * Real.pi * (R - r)) * (2 * Real.pi) *
    (D * (j : ℝ) ^ (-η)) ^ p⁻¹) / (ε / 2)
  have hR : 0 < R := hr.trans_lt hrR
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have ht : Tendsto (fun m : ℕ => J + 2 ^ m) atTop atTop := by
    apply tendsto_atTop_mono (fun m => Nat.le_add_left (2 ^ m) J)
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))
  have hh := measure_uniform_exceedance_limit_le μ (closedBall z₀ r)
    (fun m ω z => prescribedNormalizedProfile (Complex.exp z) events s₀ J
      (J + 2 ^ m) (ω (J + 2 ^ m))) L
    (fun ω z => prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j))
    (hlim.mono (fun ω hω z hz => hω.tendsto_at hz))
    (show ε / 2 < ε by linarith) (C := ENNReal.ofReal C) ?_
  · have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    simpa only [ENNReal.toReal_ofReal hC0, μ, C, Measure.real] using hh'
  · filter_upwards [ht.eventually (eventually_ge_atTop j)] with m hm
    have hb := prescribedTrajectory_uniform_difference_probability_le events s₀ J z₀
      hr hrR hJj hm hC hp (show 0 < ε / 2 by positivity) (hbound j _ hJj hj hm)
    apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hC0, μ, C, Measure.real] using hb

/-- One analytic limit, obtained almost surely along dyadic times, is the
limit of the full profile sequence uniformly in probability on every smaller
closed disk. -/
theorem prescribedTrajectory_exists_analytic_limit_in_probability_of_moment_decay
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) (z₀ : ℂ) {R : ℝ} (hR : 0 < R)
    (hC : ∀ k ≥ J, ∀ z ∈ closedBall z₀ R,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0)
    {p D η : ℝ} (hp : 1 ≤ p) (hD : 0 ≤ D) (hη : 0 < η)
    (hbound : ∀ j k : ℕ, J ≤ j → 1 ≤ j → j ≤ k → ∀ z ∈ sphere z₀ R,
      (∫ ω, ‖prescribedNormalizedProfile (Complex.exp z) events s₀ J k (ω k) -
          prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)‖ ^ p
        ∂prescribedTrajectoryMeasure events s₀) ≤ D * (j : ℝ) ^ (-η)) :
    ∃ L : (ℕ → State) → ℂ → ℂ,
      (∀ᵐ ω ∂prescribedTrajectoryMeasure events s₀,
        ∀ r : ℝ, 0 ≤ r → r < R →
          TendstoUniformlyOn
            (fun m z => prescribedNormalizedProfile (Complex.exp z) events s₀ J
              (J + 2 ^ m) (ω (J + 2 ^ m))) (L ω) atTop (closedBall z₀ r) ∧
            DifferentiableOn ℂ (L ω) (ball z₀ r)) ∧
      ∀ r : ℝ, 0 ≤ r → r < R → ∀ ε > (0 : ℝ),
        Tendsto (fun k => (prescribedTrajectoryMeasure events s₀).real
          {ω | ∃ z ∈ closedBall z₀ r,
            ε < ‖L ω z - prescribedNormalizedProfile (Complex.exp z) events s₀ J
              (J + k) (ω (J + k))‖}) atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ := prescribedTrajectory_exists_analytic_dyadic_limit_of_moment_decay
    events s₀ J z₀ hR hC hp hD hη hbound
  refine ⟨L, hL, ?_⟩
  intro r hr hrR ε hε
  have ht : Tendsto (fun k : ℕ => ((J + k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun k => Nat.le_add_left k J) tendsto_id)
  have hpow : Tendsto (fun k : ℕ => (D * (((J + k : ℕ) : ℝ) ^ (-η))) ^ p⁻¹)
      atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop hη).comp ht).const_mul D
    have h' : Tendsto (fun k : ℕ => D * (((J + k : ℕ) : ℝ) ^ (-η))) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using h
    exact h'.rpow_const_nhds_zero (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hp))
  have hupper := (hpow.const_mul
    (R / (2 * Real.pi * (R - r)) * (2 * Real.pi))).div_const (ε / 2)
  simp only [mul_zero, zero_div] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact prescribedTrajectory_uniform_limit_probability_le events s₀ J z₀ hr hrR hC hp hD hη
    hbound L (hL.mono (fun ω hω => (hω r hr hrR).1)) (Nat.le_add_right _ _)
    (hk.trans (Nat.le_add_left _ _)) hε

end HeightPaper.Model
