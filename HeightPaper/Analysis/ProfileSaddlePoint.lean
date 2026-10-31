module

public import HeightPaper.Analysis.Parameters
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Deterministic Poisson saddle-point estimates

The centered phase used by lattice Fourier inversion is
`θ * (exp (iu) - 1 - iu)`. These estimates keep its complex phase and give
explicit bounds uniform in the positive saddle parameter `θ`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace HeightPaper

noncomputable def poissonExponent (γ : ℝ) (z : ℂ) : ℂ :=
  (γ : ℂ) * (Complex.exp z - 1)

noncomputable def poissonSaddlePhase (θ u : ℝ) : ℂ :=
  (θ : ℂ) * (Complex.exp ((u : ℂ) * Complex.I) - 1 - (u : ℂ) * Complex.I)

noncomputable def poissonRateAtTilt (γ h : ℝ) : ℝ :=
  γ * (h * Real.exp h - Real.exp h + 1)

theorem neg_poissonRateAtTilt_growthFactor (l h : ℝ) :
    -poissonRateAtTilt (growthFactor l) h = profileExponent l h - 1 := by
  unfold poissonRateAtTilt profileExponent
  ring

/-- Exact centering at the saddle, with no error term. -/
theorem poissonExponent_saddle_identity (γ h u : ℝ) :
    poissonExponent γ ((h : ℂ) + u * Complex.I) -
        ((γ * Real.exp h : ℝ) : ℂ) * ((h : ℂ) + u * Complex.I) =
      -(poissonRateAtTilt γ h : ℂ) + poissonSaddlePhase (γ * Real.exp h) u := by
  simp only [poissonExponent, poissonSaddlePhase, poissonRateAtTilt,
    Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_exp]
  ring

@[simp] theorem poissonSaddlePhase_re (θ u : ℝ) :
    (poissonSaddlePhase θ u).re = θ * (Real.cos u - 1) := by
  simp [poissonSaddlePhase, Complex.exp_mul_I, Complex.cos_ofReal_re]

@[simp] theorem poissonSaddlePhase_zero (θ : ℝ) : poissonSaddlePhase θ 0 = 0 := by
  simp [poissonSaddlePhase]

theorem continuous_poissonSaddlePhase (θ : ℝ) : Continuous (poissonSaddlePhase θ) := by
  unfold poissonSaddlePhase
  fun_prop

theorem norm_exp_poissonSaddlePhase (a θ u : ℝ) :
    ‖Complex.exp ((a : ℂ) * poissonSaddlePhase θ u)‖ =
      Real.exp (a * θ * (Real.cos u - 1)) := by
  rw [Complex.norm_exp]
  simp [mul_assoc]

/-- Global Gaussian domination on the full lattice inversion interval. -/
theorem poissonSaddlePhase_gaussian_bound {a θ u : ℝ}
    (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hu : |u| ≤ Real.pi) :
    ‖Complex.exp ((a : ℂ) * poissonSaddlePhase θ u)‖ ≤
      Real.exp (-(2 / Real.pi ^ 2) * a * θ * u ^ 2) := by
  rw [norm_exp_poissonSaddlePhase]
  apply Real.exp_le_exp.mpr
  have hc := Real.cos_le_one_sub_mul_cos_sq hu
  have hm := mul_le_mul_of_nonneg_left hc (mul_nonneg ha hθ)
  nlinarith

/-- Away from the saddle, a uniform exponentially small bound. -/
theorem poissonSaddlePhase_far_bound {a θ θ₀ δ u : ℝ}
    (ha : 0 ≤ a) (hθ₀ : 0 ≤ θ₀) (hθ : θ₀ ≤ θ)
    (hδ : 0 ≤ δ) (hδu : δ ≤ |u|) (hu : |u| ≤ Real.pi) :
    ‖Complex.exp ((a : ℂ) * poissonSaddlePhase θ u)‖ ≤
      Real.exp (-(2 / Real.pi ^ 2) * a * θ₀ * δ ^ 2) := by
  refine (poissonSaddlePhase_gaussian_bound ha (hθ₀.trans hθ) hu).trans ?_
  apply Real.exp_le_exp.mpr
  have hs : δ ^ 2 ≤ u ^ 2 := by nlinarith [sq_abs u]
  have hm : θ₀ * δ ^ 2 ≤ θ * u ^ 2 :=
    mul_le_mul hθ hs (sq_nonneg δ) (hθ₀.trans hθ)
  have hc : 0 ≤ (2 / Real.pi ^ 2) * a := by positivity
  have := mul_le_mul_of_nonneg_left hm hc
  nlinarith

/-- The complex Taylor remainder is cubic with an explicit uniform constant. -/
theorem poissonSaddlePhase_cubic_bound {θ u : ℝ} (hθ : 0 ≤ θ) (hu : |u| ≤ 1) :
    ‖poissonSaddlePhase θ u + ((θ * u ^ 2 / 2 : ℝ) : ℂ)‖ ≤ θ * |u| ^ 3 := by
  have hn : ‖(u : ℂ) * Complex.I‖ ≤ 1 := by simpa using hu
  have hb := Complex.exp_bound hn (show 0 < (3 : ℕ) by omega)
  have heq : poissonSaddlePhase θ u + ((θ * u ^ 2 / 2 : ℝ) : ℂ) =
      (θ : ℂ) * (Complex.exp ((u : ℂ) * Complex.I) -
        ∑ m ∈ Finset.range 3, ((u : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) := by
    simp only [poissonSaddlePhase, Finset.sum_range_succ]
    norm_num [mul_pow, Complex.I_sq]
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ]
  apply mul_le_mul_of_nonneg_left _ hθ
  refine hb.trans ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  norm_num
  nlinarith [pow_nonneg (abs_nonneg u) 3]

/-- Exponentiation of a small complex remainder, retaining the real Gaussian factor. -/
theorem norm_exp_sub_exp_le_of_sub_norm_le_one {z w : ℂ} (h : ‖z - w‖ ≤ 1) :
    ‖Complex.exp z - Complex.exp w‖ ≤ 2 * ‖z - w‖ * Real.exp w.re := by
  have heq : Complex.exp z - Complex.exp w =
      Complex.exp w * (Complex.exp (z - w) - 1) := by
    rw [mul_sub, ← Complex.exp_add]
    simp
  rw [heq, norm_mul, Complex.norm_exp]
  have hb := mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_le h)
    (Real.exp_pos w.re).le
  nlinarith

theorem poissonSaddlePhase_exp_gaussian_error {a θ u : ℝ}
    (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hu : |u| ≤ 1) (hsmall : a * θ * |u| ^ 3 ≤ 1) :
    ‖Complex.exp ((a : ℂ) * poissonSaddlePhase θ u) -
        Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      2 * a * θ * |u| ^ 3 * Real.exp (-a * θ * u ^ 2 / 2) := by
  have hr : ‖(a : ℂ) * poissonSaddlePhase θ u -
      ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ)‖ ≤ a * θ * |u| ^ 3 := by
    have heq : (a : ℂ) * poissonSaddlePhase θ u -
        ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ) =
        (a : ℂ) * (poissonSaddlePhase θ u + ((θ * u ^ 2 / 2 : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left
      (poissonSaddlePhase_cubic_bound hθ hu) ha
  refine (norm_exp_sub_exp_le_of_sub_norm_le_one (hr.trans hsmall)).trans ?_
  simp only [Complex.ofReal_re]
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2))
    (Real.exp_pos (-a * θ * u ^ 2 / 2)).le
  nlinarith

/-- Integrated central Taylor error. Its relative error is at most `2*a*θ*δ³`. -/
theorem poissonSaddlePhase_integral_gaussian_error {a θ δ : ℝ}
    (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hsmall : a * θ * δ ^ 3 ≤ 1) :
    ‖(∫ u : ℝ in -δ..δ, Complex.exp ((a : ℂ) * poissonSaddlePhase θ u)) -
        ((∫ u : ℝ in -δ..δ, Real.exp (-a * θ * u ^ 2 / 2) : ℝ) : ℂ)‖ ≤
      2 * a * θ * δ ^ 3 *
        ∫ u : ℝ in -δ..δ, Real.exp (-a * θ * u ^ 2 / 2) := by
  have hi₁ : IntervalIntegrable
      (fun u => Complex.exp ((a : ℂ) * poissonSaddlePhase θ u)) volume (-δ) δ :=
    (Complex.continuous_exp.comp (continuous_const.mul (continuous_poissonSaddlePhase θ))).intervalIntegrable ..
  have hi₂ : IntervalIntegrable
      (fun u : ℝ => Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ)) volume (-δ) δ := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcast : ((∫ u : ℝ in -δ..δ, Real.exp (-a * θ * u ^ 2 / 2) : ℝ) : ℂ) =
      ∫ u : ℝ in -δ..δ, Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp only [Complex.ofReal_exp]
  rw [hcast, ← intervalIntegral.integral_sub hi₁ hi₂]
  have hb := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun u : ℝ => Complex.exp ((a : ℂ) * poissonSaddlePhase θ u) -
      Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ))
    (by linarith : -δ ≤ δ)
    (g := fun u : ℝ => 2 * a * θ * δ ^ 3 * Real.exp (-a * θ * u ^ 2 / 2))
    (ae_of_all volume (fun u hu => ?_))
    (show IntervalIntegrable
      (fun u : ℝ => 2 * a * θ * δ ^ 3 * Real.exp (-a * θ * u ^ 2 / 2))
        volume (-δ) δ from (by apply Continuous.intervalIntegrable; fun_prop))
  · simpa only [intervalIntegral.integral_const_mul] using hb
  · have huδ : |u| ≤ δ := abs_le.mpr ⟨hu.1.le, hu.2⟩
    have hu3 : |u| ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ (abs_nonneg u) huδ 3
    have ham : a * θ * |u| ^ 3 ≤ a * θ * δ ^ 3 :=
      mul_le_mul_of_nonneg_left hu3 (mul_nonneg ha hθ)
    refine (poissonSaddlePhase_exp_gaussian_error ha hθ (huδ.trans hδ1)
      (ham.trans hsmall)).trans ?_
    gcongr

/-- Gaussian rescaling, with the truncation endpoints explicit. -/
theorem gaussian_window_rescale {b : ℝ} (hb : 0 < b) (δ : ℝ) :
    (∫ u : ℝ in -δ..δ, Real.exp (-b * u ^ 2)) =
      (Real.sqrt b)⁻¹ *
        ∫ v : ℝ in -(δ * Real.sqrt b)..δ * Real.sqrt b, Real.exp (-v ^ 2) := by
  have hs : Real.sqrt b ≠ 0 := (Real.sqrt_pos.2 hb).ne'
  have heq (u : ℝ) : Real.exp (-b * u ^ 2) =
      Real.exp (-(u * Real.sqrt b) ^ 2) := by
    congr 1
    rw [mul_pow, Real.sq_sqrt hb.le]
    ring
  simp_rw [heq]
  simpa using intervalIntegral.integral_comp_mul_right
    (fun v : ℝ => Real.exp (-v ^ 2)) hs (a := -δ) (b := δ)

/-- A Gaussian window tending to the whole line has the exact limiting mass. -/
theorem gaussian_window_tendsto {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    Tendsto (fun n => ∫ v : ℝ in -r n..r n, Real.exp (-v ^ 2)) atTop
      (𝓝 (Real.sqrt Real.pi)) := by
  have hi : Integrable (fun v : ℝ => Real.exp (-v ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (show 0 < (1 : ℝ) by norm_num)
  have h := intervalIntegral_tendsto_integral hi (tendsto_neg_atTop_atBot.comp hr) hr
  have heq : (∫ v : ℝ, Real.exp (-v ^ 2)) = Real.sqrt Real.pi := by
    simpa using integral_gaussian (1 : ℝ)
  rwa [heq] at h

end HeightPaper
