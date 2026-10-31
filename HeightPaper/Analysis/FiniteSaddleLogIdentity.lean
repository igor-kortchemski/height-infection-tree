module

public import HeightPaper.Probability.FiniteSaddleAmplitudeCentral
public import HeightPaper.StrongProfileStatement

/-! # Exact logarithmic normalization of the finite saddle integral -/

@[expose] public section

open MeasureTheory Set

namespace HeightPaper.CountCoupling

open Model

/-- On an exact lattice height, a positive normalized saddle integral gives
the exact logarithmic profile correction. The sole remaining terms are its
amplitude and the bounded tilt-dependent Gaussian factor. -/
theorem coupled_profile_log_saddle_identity (l : ℝ) (n H k : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) (x : ℝ)
    (ha : 0 < Real.log n) (hθ : 0 < growthFactor l * Real.exp x)
    (hk : (k : ℝ) = growthFactor l * Real.exp x * Real.log n)
    (hZ : 0 < ‖(Real.sqrt (Real.log n *
        (growthFactor l * Real.exp x) / 2) : ℂ) *
          (∫ v : ℝ in -Real.pi..Real.pi,
            finiteSaddleIntegrandAtScale l H (Real.log n) x
              (coupledTreeHistory l n H q) v)‖) :
    0 < normalizedActiveProfile (coupledTreeState l n q H) k ∧
      Real.log (normalizedActiveProfile (coupledTreeState l n q H) k) -
        strongProfileLogScale l n x =
        Real.log ‖(Real.sqrt (Real.log n *
          (growthFactor l * Real.exp x) / 2) : ℂ) *
            (∫ v : ℝ in -Real.pi..Real.pi,
              finiteSaddleIntegrandAtScale l H (Real.log n) x
                (coupledTreeHistory l n H q) v)‖ -
          Real.log (2 * Real.pi) -
          (1 / 2 : ℝ) * Real.log ((growthFactor l * Real.exp x) / 2) := by
  let a : ℝ := Real.log n
  let θ : ℝ := growthFactor l * Real.exp x
  let s := coupledTreeState l n q H
  let J : ℂ := ∫ v : ℝ in -Real.pi..Real.pi,
    finiteSaddleIntegrandAtScale l H a x (coupledTreeHistory l n H q) v
  let Z : ℂ := (Real.sqrt (a * θ / 2) : ℂ) * J
  let P : ℝ := normalizedActiveProfile s k
  have hθ2 : 0 < θ / 2 := by positivity
  have harg : a * θ / 2 = a * (θ / 2) := by ring
  have hsqrt : 0 < Real.sqrt (a * θ / 2) := Real.sqrt_pos.mpr (by positivity)
  have hπ : 0 < 2 * Real.pi := by positivity
  have hPnonneg : 0 ≤ P := normalizedActiveProfile_nonneg s k
  have hinv := normalizedActiveProfile_coupled_saddle_inversion l n H k q a x
    (by dsimp [a, θ]; rw [hk]; ring)
  have hnorm : (2 * Real.pi) * P =
      Real.exp (-a * poissonRateAtTilt (growthFactor l) x) * ‖J‖ := by
    have hh := congrArg norm hinv
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, Complex.ofReal_re] at hh
    change |(2 : ℝ)| * |Real.pi| * |P| =
      Real.exp (-a * poissonRateAtTilt (growthFactor l) x) * ‖J‖ at hh
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos, abs_of_nonneg hPnonneg] at hh
    exact hh
  have hZnorm : ‖Z‖ = Real.sqrt (a * θ / 2) * ‖J‖ := by
    simp only [Z, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsqrt]
  have hscaled : (2 * Real.pi * P) * Real.sqrt (a * θ / 2) =
      Real.exp (-a * poissonRateAtTilt (growthFactor l) x) * ‖Z‖ := by
    rw [hnorm, hZnorm]
    ring
  have hP : 0 < P := by
    by_contra hh
    have hp0 : P = 0 := le_antisymm (le_of_not_gt hh) hPnonneg
    rw [hp0] at hscaled
    have hright := mul_pos
      (Real.exp_pos (-a * poissonRateAtTilt (growthFactor l) x)) hZ
    simp only [mul_zero, zero_mul] at hscaled
    linarith
  have hrate : -a * poissonRateAtTilt (growthFactor l) x =
      (profileExponent l x - 1) * a := by
    rw [← neg_poissonRateAtTilt_growthFactor]
    ring
  have hlog := congrArg Real.log hscaled
  rw [Real.log_mul (mul_ne_zero hπ.ne' hP.ne') hsqrt.ne',
    Real.log_mul hπ.ne' hP.ne',
    Real.log_mul (Real.exp_pos _).ne' hZ.ne',
    Real.log_exp, harg, Real.log_sqrt (by positivity : 0 ≤ a * (θ / 2)),
    Real.log_mul ha.ne' hθ2.ne'] at hlog
  rw [← harg] at hlog
  dsimp only [P, s, a, θ] at hlog
  dsimp only [P, s, Z, J, a, θ] at hP ⊢
  constructor
  · exact hP
  · unfold strongProfileLogScale
    rw [hrate] at hlog
    linarith

end HeightPaper.CountCoupling
