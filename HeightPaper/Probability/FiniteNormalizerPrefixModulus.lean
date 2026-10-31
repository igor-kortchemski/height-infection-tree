module

public import HeightPaper.Probability.FiniteAnalyticResidual
public import HeightPaper.Analysis.AnalyticAmplitudeControl

/-!
# Uniform complex-tilt modulus of a bounded normalizer prefix

The finite profile normalized after the random cutoff equals the unshifted
profile multiplied by this prefix product. A deterministic modulus, uniform
over every event word and every bounded cutoff, controls that conversion.
-/

@[expose] public section

open Metric Set

namespace HeightPaper.CountCoupling

open Model

/-- On a real-positive weight window, the shifted profile is exactly the
unshifted profile times its finite normalizer prefix. -/
theorem prescribedNormalizedProfile_eq_unshifted_mul_prefix
    {w : ℂ} (hw : 1 ≤ w.re) (events : ℕ → Bool) (s₀ s : State)
    {J k : ℕ} (hJk : J ≤ k) :
    prescribedNormalizedProfile w events s₀ J k s =
      prescribedNormalizedProfile w events s₀ 0 k s *
        prescribedNormalizer w events (infectious s₀) J := by
  have hp : prescribedNormalizer w events (infectious s₀) J ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt (zero_lt_one.trans_le
      (one_le_norm_prescribedNormalizer hw events (infectious s₀) J))
  have h := prescribedNormalizedProfile_zero_eq_div_prefix w events s₀ s hJk
  exact ((eq_div_iff hp).mp h).symm

/-- The prefix normalizer has a deterministic complex-tilt modulus, with no
dependence on the event word or on the cutoff below `K`. -/
theorem prescribedNormalizer_exp_prefix_modulus
    (x : ℝ) {R : ℝ} (hR : 0 < R) (K : ℕ)
    (events : ℕ → Bool) (i₀ J : ℕ) (hJ : J ≤ K)
    {z : ℂ} (hz : z ∈ ball (x : ℂ) R) :
    ‖prescribedNormalizer (Complex.exp z) events i₀ J -
      prescribedNormalizer (Complex.exp (x : ℂ)) events i₀ J‖ ≤
      (2 * (2 + Real.exp (x + R)) ^ K / R) * ‖z - (x : ℂ)‖ := by
  let M : ℝ := (2 + Real.exp (x + R)) ^ K
  have hbound (w : ℂ) (hw : w ∈ ball (x : ℂ) R) :
      ‖prescribedNormalizer (Complex.exp w) events i₀ J‖ ≤ M := by
    have hdiff : w.re - x ≤ ‖w - (x : ℂ)‖ := by
      simpa only [Complex.sub_re, Complex.ofReal_re] using
        (Complex.re_le_norm (w - (x : ℂ)))
    have hdist : ‖w - (x : ℂ)‖ < R := by
      simpa only [mem_ball, dist_eq_norm] using hw
    have hre : w.re ≤ x + R := by linarith
    have hnorm : ‖Complex.exp w‖ ≤ Real.exp (x + R) := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr hre
    have hbase : 1 ≤ 2 + Real.exp (x + R) := by
      linarith [Real.exp_pos (x + R)]
    calc
      _ ≤ (2 + ‖Complex.exp w‖) ^ J :=
        norm_prescribedNormalizer_le _ _ _ _
      _ ≤ (2 + Real.exp (x + R)) ^ J := by gcongr
      _ ≤ M := pow_le_pow_right₀ hbase hJ
  have hdiff : DifferentiableOn ℂ
      (fun w ↦ prescribedNormalizer (Complex.exp w) events i₀ J)
      (ball (x : ℂ) R) := by
    have hh := differentiable_prescribedNormalizerFrom_exp events i₀ 0 J
    simpa only [prescribedNormalizerFrom_zero] using hh.differentiableOn
  exact analytic_norm_sub_center_le hR hdiff hbound hz

/-- Exact transfer of small-tilt continuity from the unshifted profile to
the source profile normalized after a bounded cutoff. -/
theorem prescribedNormalizedProfile_shifted_tilt_bound
    (x : ℝ) {R : ℝ} (hR : 0 < R) (K : ℕ)
    (events : ℕ → Bool) (s₀ s : State)
    {J k : ℕ} (hJ : J ≤ K) (hJk : J ≤ k)
    {z : ℂ} (hz : z ∈ ball (x : ℂ) R)
    (hwz : 1 ≤ (Complex.exp z).re)
    (hwx : 1 ≤ (Complex.exp (x : ℂ)).re) :
    ‖prescribedNormalizedProfile (Complex.exp z) events s₀ J k s -
      prescribedNormalizedProfile (Complex.exp (x : ℂ)) events s₀ J k s‖ ≤
      (2 + Real.exp (x + R)) ^ K *
        ‖prescribedNormalizedProfile (Complex.exp z) events s₀ 0 k s -
          prescribedNormalizedProfile (Complex.exp (x : ℂ)) events s₀ 0 k s‖ +
      ‖prescribedNormalizedProfile (Complex.exp (x : ℂ)) events s₀ 0 k s‖ *
        (2 * (2 + Real.exp (x + R)) ^ K / R) * ‖z - (x : ℂ)‖ := by
  let M : ℝ := (2 + Real.exp (x + R)) ^ K
  let A : ℂ := prescribedNormalizedProfile (Complex.exp z) events s₀ 0 k s
  let L : ℂ := prescribedNormalizedProfile (Complex.exp (x : ℂ)) events s₀ 0 k s
  let Pz : ℂ := prescribedNormalizer (Complex.exp z) events (infectious s₀) J
  let Px : ℂ := prescribedNormalizer (Complex.exp (x : ℂ)) events (infectious s₀) J
  have hdiff : z.re - x ≤ ‖z - (x : ℂ)‖ := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      (Complex.re_le_norm (z - (x : ℂ)))
  have hdist : ‖z - (x : ℂ)‖ < R := by
    simpa only [mem_ball, dist_eq_norm] using hz
  have hre : z.re ≤ x + R := by linarith
  have hnorm : ‖Complex.exp z‖ ≤ Real.exp (x + R) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr hre
  have hbase : 1 ≤ 2 + Real.exp (x + R) := by
    linarith [Real.exp_pos (x + R)]
  have hPz : ‖Pz‖ ≤ M := by
    calc
      _ ≤ (2 + ‖Complex.exp z‖) ^ J :=
        norm_prescribedNormalizer_le _ _ _ _
      _ ≤ (2 + Real.exp (x + R)) ^ J := by gcongr
      _ ≤ M := pow_le_pow_right₀ hbase hJ
  have hPdiff : ‖Pz - Px‖ ≤ (2 * M / R) * ‖z - (x : ℂ)‖ :=
    prescribedNormalizer_exp_prefix_modulus x hR K events (infectious s₀) J hJ hz
  rw [prescribedNormalizedProfile_eq_unshifted_mul_prefix hwz events s₀ s hJk,
    prescribedNormalizedProfile_eq_unshifted_mul_prefix hwx events s₀ s hJk]
  change ‖A * Pz - L * Px‖ ≤ _
  have heq : A * Pz - L * Px = (A - L) * Pz + L * (Pz - Px) := by ring
  rw [heq]
  calc
    _ ≤ ‖(A - L) * Pz‖ + ‖L * (Pz - Px)‖ := norm_add_le _ _
    _ = ‖A - L‖ * ‖Pz‖ + ‖L‖ * ‖Pz - Px‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖A - L‖ * M + ‖L‖ * ((2 * M / R) * ‖z - (x : ℂ)‖) := by
      gcongr
    _ = _ := by dsimp [A, L, M]; ring

end HeightPaper.CountCoupling
