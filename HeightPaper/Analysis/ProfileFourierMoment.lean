module

public import HeightPaper.Analysis.ComplexMomentExponent
public import HeightPaper.Analysis.ProfileSaddlePoint

/-!
# Cancellation of the complex moment growth in Fourier inversion

The general moment bound can grow away from the real axis. Multiplication by
the actual normalizer phase cancels that growth, leaving a Gaussian term and
an exponentially small term controlled by the real moment exponent.
-/

@[expose] public section

namespace HeightPaper

theorem complexProfileMomentExponent_phase_cancel (l x u p : ℝ) :
    complexProfileMomentExponent l ((x : ℂ) + (u : ℂ) * Complex.I) p + 1 +
      p * growthFactor l *
        ((Complex.exp ((x : ℂ) + (u : ℂ) * Complex.I)).re - Real.exp x) =
      complexProfileMomentExponent l (x : ℂ) p + 1 := by
  simp only [complexProfileMomentExponent, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero, Complex.exp_ofReal_re]
  ring

/-- The maximum in the all-exponent growth estimate causes no singularity
at exponent `-1`. Each of its two branches has a different useful bound. -/
theorem profile_growth_phase_split {l x u p a η : ℝ} (ha : 0 ≤ a)
    (hmargin : complexProfileMomentExponent l (x : ℂ) p ≤ -1 - η) :
    Real.exp (max (complexProfileMomentExponent l ((x : ℂ) + (u : ℂ) * Complex.I) p + 1) 0 * a) *
      Real.exp (p * growthFactor l *
        ((Complex.exp ((x : ℂ) + (u : ℂ) * Complex.I)).re - Real.exp x) * a) ≤
      Real.exp (p * growthFactor l *
        ((Complex.exp ((x : ℂ) + (u : ℂ) * Complex.I)).re - Real.exp x) * a) +
        Real.exp (-η * a) := by
  let α := complexProfileMomentExponent l ((x : ℂ) + (u : ℂ) * Complex.I) p + 1
  let b := p * growthFactor l *
    ((Complex.exp ((x : ℂ) + (u : ℂ) * Complex.I)).re - Real.exp x)
  have hab : α + b ≤ -η := by
    have he := complexProfileMomentExponent_phase_cancel l x u p
    dsimp only [α, b]
    linarith
  change Real.exp (max α 0 * a) * Real.exp (b * a) ≤ Real.exp (b * a) + Real.exp (-η * a)
  by_cases hα : 0 ≤ α
  · rw [max_eq_left hα, ← Real.exp_add]
    have he : Real.exp (α * a + b * a) ≤ Real.exp (-η * a) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hab ha])
    exact he.trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  · rw [max_eq_right (le_of_not_ge hα), zero_mul, Real.exp_zero, one_mul]
    exact le_add_of_nonneg_right (Real.exp_pos _).le

/-- The weighted general moment growth is controlled on the full lattice
interval, including far from the real saddle. -/
theorem profile_growth_phase_bound {l x u p a η : ℝ} (hl : 1 < l)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hu : |u| ≤ Real.pi)
    (hmargin : complexProfileMomentExponent l (x : ℂ) p ≤ -1 - η) :
    Real.exp (max (complexProfileMomentExponent l ((x : ℂ) + (u : ℂ) * Complex.I) p + 1) 0 * a) *
      Real.exp (p * growthFactor l *
        ((Complex.exp ((x : ℂ) + (u : ℂ) * Complex.I)).re - Real.exp x) * a) ≤
      Real.exp (-(2 / Real.pi ^ 2) * p * growthFactor l * Real.exp x * a * u ^ 2) +
        Real.exp (-η * a) := by
  refine (profile_growth_phase_split ha hmargin).trans ?_
  apply add_le_add
  swap
  · exact le_rfl
  have hre : (Complex.exp ((x : ℂ) + (u : ℂ) * Complex.I)).re =
      Real.exp x * Real.cos u := by simp [Complex.exp_re]
  have hg := poissonSaddlePhase_gaussian_bound (mul_nonneg hp ha)
    (mul_nonneg (growthFactor_pos hl).le (Real.exp_pos x).le) hu
  rw [norm_exp_poissonSaddlePhase] at hg
  convert hg using 1 <;> congr 1
  · rw [hre]
    ring
  · ring

end HeightPaper
