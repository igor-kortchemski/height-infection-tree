module

public import HeightPaper.Model.NormalizedProfile
public import HeightPaper.Analysis.ProfileSaddlePoint
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact Fourier inversion of the active profile

The height variable remains an integer. All identities include states with no
active vertices, whose normalized profile and transform are both zero.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.Model

/-- The normalized active profile, with value zero when the active count is zero. -/
noncomputable def normalizedActiveProfile (s : State) (k : ℕ) : ℝ :=
  (activeProfile s k : ℝ) / (infectious s : ℝ)

theorem normalizedActiveProfile_nonneg (s : State) (k : ℕ) :
    0 ≤ normalizedActiveProfile s k := by
  unfold normalizedActiveProfile
  positivity

theorem normalizedActiveProfile_of_infectious_eq_zero {s : State}
    (hs : infectious s = 0) (k : ℕ) : normalizedActiveProfile s k = 0 := by
  simp [normalizedActiveProfile, hs]

/-- Orthogonality of integer frequencies on a full Fourier period. -/
theorem integral_exp_int_frequency (m : ℤ) :
    (∫ u : ℝ in -Real.pi..Real.pi,
      Complex.exp (((m : ℂ) * Complex.I) * u)) =
      if m = 0 then (2 * (Real.pi : ℂ)) else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [intervalIntegral.integral_const, Complex.real_smul]
    ring
  · rw [ite_eq_right hm, integral_exp_mul_complex (mul_ne_zero (by exact_mod_cast hm)
      Complex.I_ne_zero)]
    have hplus :
        Complex.exp (((m : ℂ) * Complex.I) * (Real.pi : ℂ)) =
          Complex.cos ((m : ℂ) * Real.pi) := by
      rw [mul_right_comm, Complex.exp_mul_I]
      simp [Complex.sin_int_mul_pi]
    have hminus :
        Complex.exp (((m : ℂ) * Complex.I) * ((-Real.pi : ℝ) : ℂ)) =
          Complex.cos ((m : ℂ) * Real.pi) := by
      rw [mul_right_comm, Complex.exp_mul_I]
      simp [Complex.sin_int_mul_pi]
    rw [hplus, hminus, sub_self, zero_div]

/-- Exponential tilting preserves exact extraction of integer coefficients. -/
theorem integral_exp_int_tilt (m : ℤ) (h : ℝ) :
    (∫ u : ℝ in -Real.pi..Real.pi,
      Complex.exp ((m : ℂ) * ((h : ℂ) + u * Complex.I))) =
      if m = 0 then (2 * (Real.pi : ℂ)) else 0 := by
  have heq (u : ℝ) :
      Complex.exp ((m : ℂ) * ((h : ℂ) + u * Complex.I)) =
        Complex.exp ((m : ℂ) * h) * Complex.exp (((m : ℂ) * Complex.I) * u) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, integral_exp_int_frequency]
  split_ifs with hm
  · simp [hm]
  · simp

theorem integral_exp_nat_coefficient (j k : ℕ) (h : ℝ) :
    (∫ u : ℝ in -Real.pi..Real.pi,
      Complex.exp ((h : ℂ) + u * Complex.I) ^ j *
        Complex.exp (-(k : ℂ) * ((h : ℂ) + u * Complex.I))) =
      if j = k then (2 * (Real.pi : ℂ)) else 0 := by
  have heq (u : ℝ) :
      Complex.exp ((h : ℂ) + u * Complex.I) ^ j *
          Complex.exp (-(k : ℂ) * ((h : ℂ) + u * Complex.I)) =
        Complex.exp ((((j : ℤ) - (k : ℤ)) : ℂ) * ((h : ℂ) + u * Complex.I)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [heq]
  simpa [sub_eq_zero] using integral_exp_int_tilt ((j : ℤ) - (k : ℤ)) h

/-- Exact finite-lattice inversion for any finite weighted family of heights. -/
theorem finite_lattice_fourier_inversion {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (d : ι → ℕ) (k : ℕ) (h : ℝ) :
    (∫ u : ℝ in -Real.pi..Real.pi,
      (∑ i ∈ s, a i * Complex.exp ((h : ℂ) + u * Complex.I) ^ d i) *
        Complex.exp (-(k : ℂ) * ((h : ℂ) + u * Complex.I))) =
      (2 * Real.pi : ℝ) * ∑ i ∈ s with d i = k, a i := by
  classical
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [mul_assoc, intervalIntegral.integral_const_mul,
      integral_exp_nat_coefficient]
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp [mul_comm]
  · intro i hi
    apply Continuous.intervalIntegrable
    fun_prop

/-- Exact Fourier inversion of the unnormalized active profile. -/
theorem activeProfile_fourier_inversion (s : State) (k : ℕ) (h : ℝ) :
    (∫ u : ℝ in -Real.pi..Real.pi,
      activeWeight (Complex.exp ((h : ℂ) + u * Complex.I)) s *
        Complex.exp (-(k : ℂ) * ((h : ℂ) + u * Complex.I))) =
      (2 * Real.pi : ℝ) * (activeProfile s k : ℂ) := by
  simpa [activeWeight, activeProfile] using
    finite_lattice_fourier_inversion s.active (fun _ => 1) s.tree.depth k h

/-- Exact inversion of the normalized Laplace transform, including zero mass. -/
theorem normalizedActiveProfile_fourier_inversion (s : State) (k : ℕ) (h : ℝ) :
    (∫ u : ℝ in -Real.pi..Real.pi,
      normalizedActiveWeight (Complex.exp ((h : ℂ) + u * Complex.I)) s *
        Complex.exp (-(k : ℂ) * ((h : ℂ) + u * Complex.I))) =
      (2 * Real.pi : ℝ) * (normalizedActiveProfile s k : ℂ) := by
  simp only [normalizedActiveWeight, div_mul_eq_mul_div]
  rw [intervalIntegral.integral_div, activeProfile_fourier_inversion]
  simp [normalizedActiveProfile, mul_div_assoc]

/-- The exact residual factor after removing the Poisson exponential scale.
It is a function of the complex argument and stays inside Fourier inversion. -/
noncomputable def profileResidual (s : State) (γ a : ℝ) (z : ℂ) : ℂ :=
  normalizedActiveWeight (Complex.exp z) s *
    Complex.exp (-(a : ℂ) * poissonExponent γ z)

theorem profileResidual_mul_exp (s : State) (γ a : ℝ) (z : ℂ) :
    profileResidual s γ a z * Complex.exp ((a : ℂ) * poissonExponent γ z) =
      normalizedActiveWeight (Complex.exp z) s := by
  unfold profileResidual
  rw [mul_assoc, ← Complex.exp_add]
  simp

/-- Exact saddle-point inversion at the integer lattice height `k = a*γ*exp h`.
Only the deterministic rate factor is taken outside the oscillatory integral. -/
theorem normalizedActiveProfile_saddle_inversion (s : State) (k : ℕ) (γ a h : ℝ)
    (hk : (k : ℝ) = a * (γ * Real.exp h)) :
    (2 * Real.pi : ℝ) * (normalizedActiveProfile s k : ℂ) =
      Complex.exp ((-a * poissonRateAtTilt γ h : ℝ) : ℂ) *
        ∫ u : ℝ in -Real.pi..Real.pi,
          profileResidual s γ a ((h : ℂ) + u * Complex.I) *
            Complex.exp ((a : ℂ) * poissonSaddlePhase (γ * Real.exp h) u) := by
  rw [← normalizedActiveProfile_fourier_inversion s k h,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  have hkC : (k : ℂ) = (a : ℂ) * ((γ * Real.exp h : ℝ) : ℂ) := by
    exact_mod_cast hk
  have hexp : (a : ℂ) * poissonExponent γ ((h : ℂ) + u * Complex.I) -
      (k : ℂ) * ((h : ℂ) + u * Complex.I) =
      ((-a * poissonRateAtTilt γ h : ℝ) : ℂ) +
        (a : ℂ) * poissonSaddlePhase (γ * Real.exp h) u := by
    rw [hkC, mul_assoc, ← mul_sub, poissonExponent_saddle_identity]
    push_cast
    ring
  calc
    _ = (profileResidual s γ a ((h : ℂ) + u * Complex.I) *
          Complex.exp ((a : ℂ) * poissonExponent γ ((h : ℂ) + u * Complex.I))) *
          Complex.exp (-(k : ℂ) * ((h : ℂ) + u * Complex.I)) := by
      rw [profileResidual_mul_exp]
    _ = profileResidual s γ a ((h : ℂ) + u * Complex.I) *
          Complex.exp ((a : ℂ) * poissonExponent γ ((h : ℂ) + u * Complex.I) -
            (k : ℂ) * ((h : ℂ) + u * Complex.I)) := by
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      ring
    _ = _ := by rw [hexp, Complex.exp_add]; ring

end HeightPaper.Model
