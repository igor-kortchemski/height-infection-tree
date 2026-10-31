module

public import HeightPaper.Model.ProfileFourier

/-! # Exact residual and centered raw Fourier integrand -/

@[expose] public section

namespace HeightPaper.Model

/-- The actual finite saddle amplitude is entire, including at zero mass. -/
theorem differentiable_profileResidual (s : State) (γ a : ℝ) :
    Differentiable ℂ (profileResidual s γ a) := by
  unfold profileResidual poissonExponent normalizedActiveWeight activeWeight
  fun_prop

/-- The residual retained inside saddle inversion is exactly the raw
normalized profile divided by its real growth scale, with a unit phase.
The event time and the chosen inversion scale need not coincide. -/
theorem profileResidual_saddle_integrand_eq (s : State) (γ a x v : ℝ) :
    profileResidual s γ a ((x : ℂ) + (v : ℂ) * Complex.I) *
      Complex.exp ((a : ℂ) * poissonSaddlePhase (γ * Real.exp x) v) =
        normalizedActiveWeight (Complex.exp ((x : ℂ) + (v : ℂ) * Complex.I)) s /
          (Real.exp (γ * (Real.exp x - 1) * a) : ℂ) *
            Complex.exp (-((a * γ * Real.exp x * v : ℝ) : ℂ) * Complex.I) := by
  have he : -(a : ℂ) * poissonExponent γ ((x : ℂ) + (v : ℂ) * Complex.I) +
      (a : ℂ) * poissonSaddlePhase (γ * Real.exp x) v =
        -((γ * (Real.exp x - 1) * a : ℝ) : ℂ) +
          (-((a * γ * Real.exp x * v : ℝ) : ℂ) * Complex.I) := by
    simp only [poissonExponent, poissonSaddlePhase, Complex.exp_add,
      ← Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  calc
    _ = normalizedActiveWeight (Complex.exp ((x : ℂ) + (v : ℂ) * Complex.I)) s *
        Complex.exp (-(a : ℂ) * poissonExponent γ ((x : ℂ) + (v : ℂ) * Complex.I) +
          (a : ℂ) * poissonSaddlePhase (γ * Real.exp x) v) := by
      rw [profileResidual, mul_assoc, ← Complex.exp_add]
    _ = _ := by
      rw [he]
      conv_lhs =>
        arg 2
        rw [Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp]
      ring

end HeightPaper.Model
