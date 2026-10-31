module

public import HeightPaper.Probability.FiniteComplexNormalizer
public import HeightPaper.Model.UnshiftedProfile
public import HeightPaper.Model.AnalyticProfileLimit

/-!
# The entire normalizer residual in Fourier inversion

The finite product times its deterministic exponential centering is entire.
Its chosen logarithmic error is used only for bounds, never differentiated.
The centering scale is arbitrary, in particular log n rather than log H.
-/

@[expose] public section

open Complex Set
open scoped BigOperators

namespace HeightPaper.Model

theorem norm_prescribedNormalizer_le (w : ℂ) (events : ℕ → Bool) (i₀ k : ℕ) :
    ‖prescribedNormalizer w events i₀ k‖ ≤ (2 + ‖w‖) ^ k := by
  rw [← prescribedNormalizerFrom_zero, prescribedNormalizerFrom_eq_birthReciprocal]
  calc
    _ = ∏ i ∈ Finset.Ico 0 k, ‖1 + (w - 1) * (birthReciprocal events i₀ i : ℂ)‖ :=
      norm_prod _ _
    _ ≤ ∏ _i ∈ Finset.Ico 0 k, (2 + ‖w‖) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      calc
        _ ≤ ‖(1 : ℂ)‖ + ‖(w - 1) * (birthReciprocal events i₀ i : ℂ)‖ := norm_add_le _ _
        _ = 1 + ‖w - 1‖ * birthReciprocal events i₀ i := by
          rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg (birthReciprocal_nonneg _ _ _)]
        _ ≤ 1 + ‖w - 1‖ := by
          nlinarith [birthReciprocal_le_one events i₀ i, norm_nonneg (w - 1)]
        _ ≤ 2 + ‖w‖ := by have hh := norm_sub_le w (1 : ℂ); rw [norm_one] at hh; linarith
    _ = _ := by simp

end HeightPaper.Model

namespace HeightPaper.CountCoupling

open Model

noncomputable def finiteUnshiftedNormalizerResidual (l : ℝ) (n H : ℕ)
    (u : ℕ → ℝ) (a : ℝ) (z : ℂ) : ℂ :=
  prescribedNormalizer (Complex.exp z) (finiteBirth l n u) 1 H *
    Complex.exp (-((growthFactor l : ℂ) * (Complex.exp z - 1) * (a : ℂ)))

theorem differentiable_finiteUnshiftedNormalizerResidual (l : ℝ) (n H : ℕ)
    (u : ℕ → ℝ) (a : ℝ) : Differentiable ℂ (finiteUnshiftedNormalizerResidual l n H u a) := by
  unfold finiteUnshiftedNormalizerResidual
  have hp := differentiable_prescribedNormalizerFrom_exp (finiteBirth l n u) 1 0 H
  simp only [prescribedNormalizerFrom_zero] at hp
  exact hp.mul (by fun_prop)

theorem finiteUnshiftedNormalizerResidual_eq_prefix_exp {l : ℝ} {n H : ℕ} {u : ℕ → ℝ}
    (hs : ∀ i ≤ H, 0 < finiteWalk l n u i) (a : ℝ) {z : ℂ}
    (hz : z.re ≤ 2 * profileRoot l) :
    finiteUnshiftedNormalizerResidual l n H u a z =
      prescribedNormalizer (Complex.exp z) (finiteBirth l n u) 1 (finiteSafeCutoff l n H u) *
        Complex.exp (finiteNormalizerLogError l n H u H z +
          (growthFactor l : ℂ) * (Complex.exp z - 1) * ((Real.log H - a : ℝ) : ℂ)) := by
  rw [finiteUnshiftedNormalizerResidual,
    prescribedNormalizer_split _ _ _ (finiteSafeCutoff_le_horizon l n H u)]
  change (_ * finiteComplexNormalizer l n H u H z) * _ = _
  rw [finiteComplexNormalizer_eq_exp hs le_rfl hz, mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [growthFactor, Complex.ofReal_sub]
  ring

/-- An upper bound before every complex tilt in a bounded vertical strip.
The prefix cutoff contributes an explicit finite power. -/
theorem norm_finiteUnshiftedNormalizerResidual_le {l a R b G : ℝ} {n H J : ℕ} {u : ℕ → ℝ}
    (hs : ∀ i ≤ H, 0 < finiteWalk l n u i) (hJ : finiteSafeCutoff l n H u ≤ J)
    {z : ℂ} (hz : z.re ≤ 2 * profileRoot l) (hzb : z.re ≤ b)
    (herror : ‖finiteNormalizerLogError l n H u H z‖ ≤ R)
    (hscale : ‖(growthFactor l : ℂ) * (Complex.exp z - 1) * ((Real.log H - a : ℝ) : ℂ)‖ ≤ G) :
    ‖finiteUnshiftedNormalizerResidual l n H u a z‖ ≤
      (2 + Real.exp b) ^ J * Real.exp (R + G) := by
  rw [finiteUnshiftedNormalizerResidual_eq_prefix_exp hs a hz, norm_mul, Complex.norm_exp]
  have hp : ‖prescribedNormalizer (Complex.exp z) (finiteBirth l n u) 1
      (finiteSafeCutoff l n H u)‖ ≤ (2 + Real.exp b) ^ J := by
    apply (norm_prescribedNormalizer_le _ _ _ _).trans
    rw [Complex.norm_exp]
    apply (pow_le_pow_left₀ (by positivity : 0 ≤ 2 + Real.exp z.re)
      (show 2 + Real.exp z.re ≤ 2 + Real.exp b by linarith [Real.exp_le_exp.mpr hzb]) _).trans
    exact pow_le_pow_right₀ (by linarith [Real.exp_pos b]) hJ
  apply mul_le_mul hp (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
  rw [Complex.add_re]
  exact add_le_add ((Complex.re_le_norm _).trans herror) ((Complex.re_le_norm _).trans hscale)

/-- On a positive-real neighborhood, the residual also has a positive lower
norm bound. No convergence of the residual itself is assumed. -/
theorem exp_neg_le_norm_finiteUnshiftedNormalizerResidual {l a R G : ℝ}
    {n H : ℕ} {u : ℕ → ℝ} (hs : ∀ i ≤ H, 0 < finiteWalk l n u i)
    {z : ℂ} (hz : z.re ≤ 2 * profileRoot l) (hw : 1 ≤ (Complex.exp z).re)
    (herror : ‖finiteNormalizerLogError l n H u H z‖ ≤ R)
    (hscale : ‖(growthFactor l : ℂ) * (Complex.exp z - 1) * ((Real.log H - a : ℝ) : ℂ)‖ ≤ G) :
    Real.exp (-(R + G)) ≤ ‖finiteUnshiftedNormalizerResidual l n H u a z‖ := by
  rw [finiteUnshiftedNormalizerResidual_eq_prefix_exp hs a hz, norm_mul, Complex.norm_exp]
  have hre : -(R + G) ≤ (finiteNormalizerLogError l n H u H z +
      (growthFactor l : ℂ) * (Complex.exp z - 1) * ((Real.log H - a : ℝ) : ℂ)).re := by
    rw [Complex.add_re]
    have h₁ := (Complex.abs_re_le_norm (finiteNormalizerLogError l n H u H z)).trans herror
    have h₂ := (Complex.abs_re_le_norm
      ((growthFactor l : ℂ) * (Complex.exp z - 1) * ((Real.log H - a : ℝ) : ℂ))).trans hscale
    linarith [(abs_le.mp h₁).1, (abs_le.mp h₂).1]
  exact (Real.exp_le_exp.mpr hre).trans
    (le_mul_of_one_le_left (Real.exp_pos _).le (one_le_norm_prescribedNormalizer hw _ _ _))

end HeightPaper.CountCoupling
