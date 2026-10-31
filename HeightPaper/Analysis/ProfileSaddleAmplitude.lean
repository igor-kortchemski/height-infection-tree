module

public import HeightPaper.Analysis.ProfileSaddlePoint

/-!
# Saddle integrals with varying complex amplitudes

The finite normalizer residual remains inside the oscillatory integral.
Central variation, cubic phase error, Gaussian truncation and the outer
integral are bounded separately. No positivity or inverse bound on the
amplitude is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace HeightPaper

theorem poissonSaddleAmplitude_pointwise_error {a θ δ M η u : ℝ}
    (ha : 0 ≤ a) (hθ : 0 ≤ θ) (_hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : 0 ≤ M) (_hη : 0 ≤ η) (hsmall : a * θ * δ ^ 3 ≤ 1)
    {A A₀ : ℂ} (hA : ‖A‖ ≤ M) (hclose : ‖A - A₀‖ ≤ η) (hu : |u| ≤ δ) :
    ‖A * Complex.exp ((a : ℂ) * poissonSaddlePhase θ u) -
        A₀ * Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      (η + 2 * M * a * θ * δ ^ 3) * Real.exp (-a * θ * u ^ 2 / 2) := by
  have hu3 : |u| ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ (abs_nonneg u) hu 3
  have ham := mul_le_mul_of_nonneg_left hu3 (mul_nonneg ha hθ)
  have he := poissonSaddlePhase_exp_gaussian_error ha hθ (hu.trans hδ1) (ham.trans hsmall)
  have he' : ‖Complex.exp ((a : ℂ) * poissonSaddlePhase θ u) -
      Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ)‖ ≤
        2 * a * θ * δ ^ 3 * Real.exp (-a * θ * u ^ 2 / 2) := by
    apply he.trans
    gcongr
  have heq : A * Complex.exp ((a : ℂ) * poissonSaddlePhase θ u) -
      A₀ * Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ) =
      A * (Complex.exp ((a : ℂ) * poissonSaddlePhase θ u) -
        Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ)) +
      (A - A₀) * Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ) := by ring
  rw [heq]
  calc
    _ ≤ ‖A‖ * ‖Complex.exp ((a : ℂ) * poissonSaddlePhase θ u) -
          Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ)‖ +
        ‖A - A₀‖ * Real.exp (-a * θ * u ^ 2 / 2) := by
      simpa only [norm_mul, Complex.norm_exp, Complex.ofReal_re] using norm_add_le
        (A * (Complex.exp ((a : ℂ) * poissonSaddlePhase θ u) -
          Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ)))
        ((A - A₀) * Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ))
    _ ≤ M * (2 * a * θ * δ ^ 3 * Real.exp (-a * θ * u ^ 2 / 2)) +
        η * Real.exp (-a * θ * u ^ 2 / 2) := by
      exact add_le_add (mul_le_mul hA he' (norm_nonneg _) hM)
        (mul_le_mul_of_nonneg_right hclose (Real.exp_pos _).le)
    _ = _ := by ring

/-- The relative central error records both amplitude variation and the
cubic phase remainder. -/
theorem poissonSaddleAmplitude_central_error {a θ δ M η : ℝ}
    (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : 0 ≤ M) (hη : 0 ≤ η) (hsmall : a * θ * δ ^ 3 ≤ 1)
    (A : ℝ → ℂ) (A₀ : ℂ) (hcont : ContinuousOn A (Icc (-δ) δ))
    (hA : ∀ u ∈ Icc (-δ) δ, ‖A u‖ ≤ M)
    (hclose : ∀ u ∈ Icc (-δ) δ, ‖A u - A₀‖ ≤ η) :
    ‖(∫ u : ℝ in -δ..δ, A u * Complex.exp ((a : ℂ) * poissonSaddlePhase θ u)) -
        A₀ * ((∫ u : ℝ in -δ..δ, Real.exp (-a * θ * u ^ 2 / 2) : ℝ) : ℂ)‖ ≤
      (η + 2 * M * a * θ * δ ^ 3) *
        ∫ u : ℝ in -δ..δ, Real.exp (-a * θ * u ^ 2 / 2) := by
  have hab : -δ ≤ δ := by linarith
  have hp : Continuous (fun u : ℝ => Complex.exp ((a : ℂ) * poissonSaddlePhase θ u)) :=
    Complex.continuous_exp.comp (continuous_const.mul (continuous_poissonSaddlePhase θ))
  have hi₁ : IntervalIntegrable
      (fun u => A u * Complex.exp ((a : ℂ) * poissonSaddlePhase θ u)) volume (-δ) δ :=
    (hcont.mul hp.continuousOn).intervalIntegrable_of_Icc hab
  have hi₂ : IntervalIntegrable
      (fun u : ℝ => A₀ * Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ)) volume (-δ) δ := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcast : A₀ * ((∫ u : ℝ in -δ..δ, Real.exp (-a * θ * u ^ 2 / 2) : ℝ) : ℂ) =
      ∫ u : ℝ in -δ..δ, A₀ * Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_const_mul, ← intervalIntegral.integral_ofReal]
    simp only [Complex.ofReal_exp]
  rw [hcast, ← intervalIntegral.integral_sub hi₁ hi₂]
  have hb := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun u : ℝ => A u * Complex.exp ((a : ℂ) * poissonSaddlePhase θ u) -
      A₀ * Complex.exp ((-a * θ * u ^ 2 / 2 : ℝ) : ℂ)) hab
    (g := fun u : ℝ => (η + 2 * M * a * θ * δ ^ 3) * Real.exp (-a * θ * u ^ 2 / 2))
    (ae_of_all volume (fun u hu => ?_))
    (show IntervalIntegrable
      (fun u : ℝ => (η + 2 * M * a * θ * δ ^ 3) * Real.exp (-a * θ * u ^ 2 / 2))
        volume (-δ) δ from (by apply Continuous.intervalIntegrable; fun_prop))
  · simpa only [intervalIntegral.integral_const_mul] using hb
  · have hu' : u ∈ Icc (-δ) δ := ⟨hu.1.le, hu.2⟩
    exact poissonSaddleAmplitude_pointwise_error ha hθ hδ hδ1 hM hη hsmall
      (hA u hu') (hclose u hu') (abs_le.mpr hu')

/-- Explicit Gaussian truncation error, uniform in the positive scale. -/
theorem gaussian_window_tail_bound {b δ : ℝ} (hb : 0 < b) (hδ : 0 ≤ δ) :
    0 ≤ Real.sqrt (Real.pi / b) - ∫ u : ℝ in -δ..δ, Real.exp (-b * u ^ 2) ∧
      Real.sqrt (Real.pi / b) - (∫ u : ℝ in -δ..δ, Real.exp (-b * u ^ 2)) ≤
        Real.exp (-b * δ ^ 2 / 2) * Real.sqrt (Real.pi / (b / 2)) := by
  have hi := integrable_exp_neg_mul_sq hb
  have hi₂ := integrable_exp_neg_mul_sq (show 0 < b / 2 by positivity)
  have hab : -δ ≤ δ := by linarith
  have heq : Real.sqrt (Real.pi / b) - (∫ u : ℝ in -δ..δ, Real.exp (-b * u ^ 2)) =
      ∫ u : ℝ in (Ioc (-δ) δ)ᶜ, Real.exp (-b * u ^ 2) := by
    rw [← integral_gaussian b, intervalIntegral.integral_of_le hab]
    linarith [integral_add_compl (s := Ioc (-δ) δ) measurableSet_Ioc hi]
  rw [heq]
  constructor
  · exact integral_nonneg (fun _ => (Real.exp_pos _).le)
  · calc
      _ ≤ ∫ u : ℝ in (Ioc (-δ) δ)ᶜ,
          Real.exp (-b * δ ^ 2 / 2) * Real.exp (-(b / 2) * u ^ 2) := by
        apply setIntegral_mono_on hi.integrableOn
          (hi₂.const_mul (Real.exp (-b * δ ^ 2 / 2))).integrableOn measurableSet_Ioc.compl
        intro u hu
        have hu' : δ ≤ |u| := by
          simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hu
          rcases hu with h | h
          · exact (by linarith : δ ≤ -u).trans (neg_le_abs u)
          · exact h.le.trans (le_abs_self u)
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hh : δ ^ 2 ≤ u ^ 2 := by nlinarith [sq_abs u]
        nlinarith [mul_le_mul_of_nonneg_left hh hb.le]
      _ ≤ ∫ u : ℝ, Real.exp (-b * δ ^ 2 / 2) * Real.exp (-(b / 2) * u ^ 2) :=
        setIntegral_le_integral (hi₂.const_mul _) (ae_of_all _ (fun _ => by positivity))
      _ = _ := by rw [integral_const_mul, integral_gaussian]

/-- A bound on the two outer pieces of the full lattice inversion interval.
The integrand can be controlled directly, without separately bounding a
normalizer residual. -/
theorem fourier_outer_integral_bound {δ B : ℝ} (hδ : 0 ≤ δ)
    (hδπ : δ ≤ Real.pi) (hB : 0 ≤ B) (F : ℝ → ℂ)
    (hF : ∀ u, δ ≤ |u| → |u| ≤ Real.pi → ‖F u‖ ≤ B) :
    ‖(∫ u : ℝ in -Real.pi..-δ, F u) + (∫ u : ℝ in δ..Real.pi, F u)‖ ≤
      2 * Real.pi * B := by
  have hl : ‖∫ u : ℝ in -Real.pi..-δ, F u‖ ≤ B * |-δ - -Real.pi| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [uIoc_of_le (by linarith : -Real.pi ≤ -δ)] at hu
    exact hF u ((by linarith [hu.2] : δ ≤ -u).trans (neg_le_abs u))
      (abs_le.mpr ⟨hu.1.le, by linarith [hu.2, Real.pi_pos]⟩)
  have hr : ‖∫ u : ℝ in δ..Real.pi, F u‖ ≤ B * |Real.pi - δ| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [uIoc_of_le hδπ] at hu
    exact hF u (hu.1.le.trans (le_abs_self u))
      (abs_le.mpr ⟨by linarith [hu.1, Real.pi_pos], hu.2⟩)
  have hn := norm_add_le (∫ u : ℝ in -Real.pi..-δ, F u)
    (∫ u : ℝ in δ..Real.pi, F u)
  rw [abs_of_nonneg (by linarith : 0 ≤ -δ - -Real.pi)] at hl
  rw [abs_of_nonneg (sub_nonneg.mpr hδπ)] at hr
  nlinarith [mul_nonneg hB hδ]

/-- An exponentially decaying envelope can be used directly on the two
outer intervals. -/
theorem fourier_outer_integral_exp_bound {a κ η δ B : ℝ}
    (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hδπ : δ ≤ Real.pi)
    (hB : 0 ≤ B) (F : ℝ → ℂ)
    (hF : ∀ u, δ ≤ |u| → |u| ≤ Real.pi →
      ‖F u‖ ≤ B * (Real.exp (-κ * a * u ^ 2) + Real.exp (-η * a))) :
    ‖(∫ u : ℝ in -Real.pi..-δ, F u) + (∫ u : ℝ in δ..Real.pi, F u)‖ ≤
      2 * Real.pi * (B * (Real.exp (-κ * a * δ ^ 2) + Real.exp (-η * a))) := by
  apply fourier_outer_integral_bound hδ hδπ (by positivity)
  intro u hδu hu
  refine (hF u hδu hu).trans (mul_le_mul_of_nonneg_left ?_ hB)
  apply add_le_add
  swap
  · exact le_rfl
  apply Real.exp_le_exp.mpr
  have hh : δ ^ 2 ≤ u ^ 2 := by nlinarith [sq_abs u]
  nlinarith [mul_le_mul_of_nonneg_left hh (mul_nonneg hκ ha)]

/-- Absolute full-lattice error from a central Gaussian approximation and
an outer integrand bound. The amplitude need not be positive or nonzero. -/
theorem lattice_saddle_error_of_central {b δ E B : ℝ}
    (hb : 0 < b) (hδ : 0 ≤ δ) (hδπ : δ ≤ Real.pi) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (F : ℝ → ℂ) (A₀ : ℂ)
    (hi : IntervalIntegrable F volume (-Real.pi) Real.pi)
    (hcentral : ‖(∫ u : ℝ in -δ..δ, F u) -
      A₀ * ((∫ u : ℝ in -δ..δ, Real.exp (-b * u ^ 2) : ℝ) : ℂ)‖ ≤
        E * ∫ u : ℝ in -δ..δ, Real.exp (-b * u ^ 2))
    (houter : ∀ u, δ ≤ |u| → |u| ≤ Real.pi → ‖F u‖ ≤ B) :
    ‖(∫ u : ℝ in -Real.pi..Real.pi, F u) -
      A₀ * (Real.sqrt (Real.pi / b) : ℂ)‖ ≤
        E * Real.sqrt (Real.pi / b) + 2 * Real.pi * B +
          ‖A₀‖ * (Real.exp (-b * δ ^ 2 / 2) * Real.sqrt (Real.pi / (b / 2))) := by
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hi₁ : IntervalIntegrable F volume (-Real.pi) (-δ) := by
    apply hi.mono_set
    rw [uIcc_of_le (by linarith : -Real.pi ≤ -δ), uIcc_of_le hπ]
    exact Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])
  have hi₂ : IntervalIntegrable F volume (-δ) δ := by
    apply hi.mono_set
    rw [uIcc_of_le (by linarith : -δ ≤ δ), uIcc_of_le hπ]
    exact Icc_subset_Icc (by linarith) hδπ
  have hi₃ : IntervalIntegrable F volume δ Real.pi := by
    apply hi.mono_set
    rw [uIcc_of_le hδπ, uIcc_of_le hπ]
    exact Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl
  have hsplit : (∫ u : ℝ in -Real.pi..Real.pi, F u) =
      ((∫ u : ℝ in -Real.pi..-δ, F u) + (∫ u : ℝ in -δ..δ, F u)) +
        (∫ u : ℝ in δ..Real.pi, F u) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂,
      intervalIntegral.integral_add_adjacent_intervals (hi₁.trans hi₂) hi₃]
  have ht := gaussian_window_tail_bound hb hδ
  have ho := fourier_outer_integral_bound hδ hδπ hB F houter
  let G : ℝ := ∫ u : ℝ in -δ..δ, Real.exp (-b * u ^ 2)
  let S : ℝ := Real.sqrt (Real.pi / b)
  have htail : ‖A₀ * ((G : ℂ) - (S : ℂ))‖ ≤
      ‖A₀‖ * (Real.exp (-b * δ ^ 2 / 2) * Real.sqrt (Real.pi / (b / 2))) := by
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by dsimp [G, S]; linarith [ht.1])]
    exact mul_le_mul_of_nonneg_left (by dsimp [G, S]; linarith [ht.2]) (norm_nonneg _)
  have hdecomp : (∫ u : ℝ in -Real.pi..Real.pi, F u) - A₀ * (S : ℂ) =
      ((∫ u : ℝ in -δ..δ, F u) - A₀ * (G : ℂ)) +
        ((∫ u : ℝ in -Real.pi..-δ, F u) + (∫ u : ℝ in δ..Real.pi, F u)) +
          A₀ * ((G : ℂ) - (S : ℂ)) := by rw [hsplit]; ring
  rw [show Real.sqrt (Real.pi / b) = S from rfl, hdecomp]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  have hcent : ‖(∫ u : ℝ in -δ..δ, F u) - A₀ * (G : ℂ)‖ ≤ E * S :=
    hcentral.trans (mul_le_mul_of_nonneg_left (by dsimp [G, S]; linarith [ht.1]) hE)
  exact add_le_add (add_le_add hcent ho) htail

/-- The natural saddle normalization removes the varying Gaussian scale
from the error constants. -/
theorem lattice_saddle_normalized_error {b δ E B : ℝ}
    (hb : 0 < b) (hδ : 0 ≤ δ) (hδπ : δ ≤ Real.pi) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (F : ℝ → ℂ) (A₀ : ℂ)
    (hi : IntervalIntegrable F volume (-Real.pi) Real.pi)
    (hcentral : ‖(∫ u : ℝ in -δ..δ, F u) -
      A₀ * ((∫ u : ℝ in -δ..δ, Real.exp (-b * u ^ 2) : ℝ) : ℂ)‖ ≤
        E * ∫ u : ℝ in -δ..δ, Real.exp (-b * u ^ 2))
    (houter : ∀ u, δ ≤ |u| → |u| ≤ Real.pi → ‖F u‖ ≤ B) :
    ‖(Real.sqrt b : ℂ) * (∫ u : ℝ in -Real.pi..Real.pi, F u) -
      A₀ * (Real.sqrt Real.pi : ℂ)‖ ≤
        E * Real.sqrt Real.pi + 2 * Real.pi * (Real.sqrt b * B) +
          ‖A₀‖ * Real.exp (-b * δ ^ 2 / 2) * Real.sqrt (2 * Real.pi) := by
  have hs : Real.sqrt b * Real.sqrt (Real.pi / b) = Real.sqrt Real.pi := by
    rw [← Real.sqrt_mul hb.le]
    congr 1
    field_simp
  have hs₂ : Real.sqrt b * Real.sqrt (Real.pi / (b / 2)) = Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul hb.le]
    congr 1
    field_simp
  have heq : (Real.sqrt b : ℂ) * (∫ u : ℝ in -Real.pi..Real.pi, F u) -
      A₀ * (Real.sqrt Real.pi : ℂ) =
      (Real.sqrt b : ℂ) * ((∫ u : ℝ in -Real.pi..Real.pi, F u) -
        A₀ * (Real.sqrt (Real.pi / b) : ℂ)) := by
    rw [← hs, Complex.ofReal_mul]
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hh := mul_le_mul_of_nonneg_left
    (lattice_saddle_error_of_central hb hδ hδπ hE hB F A₀ hi hcentral houter)
      (Real.sqrt_nonneg b)
  convert hh using 1
  calc
    _ = E * (Real.sqrt b * Real.sqrt (Real.pi / b)) +
        2 * Real.pi * (Real.sqrt b * B) + ‖A₀‖ * Real.exp (-b * δ ^ 2 / 2) *
          (Real.sqrt b * Real.sqrt (Real.pi / (b / 2))) := by rw [hs, hs₂]
    _ = _ := by ring

/-- The full varying-amplitude Poisson integral, with the exact Gaussian
normalization. The finite complex residual can be used as `A` unchanged. -/
theorem poissonSaddleAmplitude_lattice_error {a θ δ M η B : ℝ}
    (ha : 0 < a) (hθ : 0 < θ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : 0 ≤ M) (hη : 0 ≤ η) (hB : 0 ≤ B) (hsmall : a * θ * δ ^ 3 ≤ 1)
    (A : ℝ → ℂ) (A₀ : ℂ) (hcont : ContinuousOn A (Icc (-Real.pi) Real.pi))
    (hA : ∀ u ∈ Icc (-δ) δ, ‖A u‖ ≤ M)
    (hclose : ∀ u ∈ Icc (-δ) δ, ‖A u - A₀‖ ≤ η)
    (houter : ∀ u, δ ≤ |u| → |u| ≤ Real.pi →
      ‖A u * Complex.exp ((a : ℂ) * poissonSaddlePhase θ u)‖ ≤ B) :
    ‖(Real.sqrt (a * θ / 2) : ℂ) *
        (∫ u : ℝ in -Real.pi..Real.pi, A u * Complex.exp ((a : ℂ) * poissonSaddlePhase θ u)) -
      A₀ * (Real.sqrt Real.pi : ℂ)‖ ≤
        (η + 2 * M * a * θ * δ ^ 3) * Real.sqrt Real.pi +
          2 * Real.pi * (Real.sqrt (a * θ / 2) * B) +
            ‖A₀‖ * Real.exp (-a * θ * δ ^ 2 / 4) * Real.sqrt (2 * Real.pi) := by
  have hδπ : δ ≤ Real.pi := hδ1.trans (by linarith [Real.one_le_pi_div_two])
  have hcent := poissonSaddleAmplitude_central_error ha.le hθ.le hδ hδ1 hM hη hsmall A A₀
    (hcont.mono (Icc_subset_Icc (by linarith) hδπ)) hA hclose
  have heq : (fun u : ℝ => Real.exp (-a * θ * u ^ 2 / 2)) =
      (fun u : ℝ => Real.exp (-(a * θ / 2) * u ^ 2)) := by
    funext u
    congr 1
    ring
  rw [heq] at hcent
  have hi : IntervalIntegrable
      (fun u => A u * Complex.exp ((a : ℂ) * poissonSaddlePhase θ u))
        volume (-Real.pi) Real.pi := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith [Real.pi_pos])
    exact hcont.mul
      (Complex.continuous_exp.comp (continuous_const.mul (continuous_poissonSaddlePhase θ))).continuousOn
  have hh := lattice_saddle_normalized_error (show 0 < a * θ / 2 by positivity)
    hδ hδπ (show 0 ≤ η + 2 * M * a * θ * δ ^ 3 by positivity) hB _ A₀ hi hcent houter
  simpa only [show -(a * θ / 2) * δ ^ 2 / 2 = -a * θ * δ ^ 2 / 4 by ring] using hh

/-- Uniform saddle convergence with varying saddle scales and varying
amplitudes. The hypotheses separate a vanishing central error, a vanishing
scaled outer envelope, and a Gaussian window whose width tends to infinity.
There is no lower bound on the amplitude. -/
theorem lattice_saddle_uniform_error_tendsto {X : Type*} (K : Set X)
    (F : ℕ → X → ℝ → ℂ) (A₀ : ℕ → X → ℂ) (b δ : ℕ → X → ℝ)
    (E B r : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hE : ∀ n, 0 ≤ E n) (hB : ∀ n, 0 ≤ B n)
    (hE0 : Tendsto E atTop (𝓝 0)) (hB0 : Tendsto B atTop (𝓝 0))
    (hr : Tendsto r atTop atTop)
    (hb : ∀ n x, x ∈ K → 0 < b n x)
    (hδ : ∀ n x, x ∈ K → 0 ≤ δ n x)
    (hδπ : ∀ n x, x ∈ K → δ n x ≤ Real.pi)
    (hA : ∀ n x, x ∈ K → ‖A₀ n x‖ ≤ M)
    (hi : ∀ n x, x ∈ K → IntervalIntegrable (F n x) volume (-Real.pi) Real.pi)
    (hcentral : ∀ n x, x ∈ K →
      ‖(∫ u : ℝ in -(δ n x)..δ n x, F n x u) -
        A₀ n x * ((∫ u : ℝ in -(δ n x)..δ n x, Real.exp (-b n x * u ^ 2) : ℝ) : ℂ)‖ ≤
          E n * ∫ u : ℝ in -(δ n x)..δ n x, Real.exp (-b n x * u ^ 2))
    (houter : ∀ n x, x ∈ K → ∀ u, δ n x ≤ |u| → |u| ≤ Real.pi →
      Real.sqrt (b n x) * ‖F n x u‖ ≤ B n)
    (hwidth : ∀ n x, x ∈ K → r n ≤ b n x * (δ n x) ^ 2) :
    TendstoUniformlyOn
      (fun n x => (Real.sqrt (b n x) : ℂ) * (∫ u : ℝ in -Real.pi..Real.pi, F n x u) -
        A₀ n x * (Real.sqrt Real.pi : ℂ)) (fun _ => 0) atTop K := by
  have he : Tendsto (fun n => Real.exp (-r n / 2)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact (tendsto_neg_atTop_atBot.comp hr).atBot_div_const (by norm_num : (0 : ℝ) < 2)
  have hlimit : Tendsto (fun n => E n * Real.sqrt Real.pi + 2 * Real.pi * B n +
      M * Real.exp (-r n / 2) * Real.sqrt (2 * Real.pi)) atTop (𝓝 0) := by
    convert ((hE0.mul_const _).add (hB0.const_mul _)).add
      ((he.const_mul M).mul_const _) using 1
    simp
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hlimit.eventually (gt_mem_nhds hε)] with n hn
  intro x hx
  have hs : 0 < Real.sqrt (b n x) := Real.sqrt_pos.mpr (hb n x hx)
  have hout : ∀ u, δ n x ≤ |u| → |u| ≤ Real.pi →
      ‖F n x u‖ ≤ B n / Real.sqrt (b n x) := by
    intro u hu huπ
    apply (le_div_iff₀ hs).mpr
    simpa only [mul_comm] using houter n x hx u hu huπ
  have hh := lattice_saddle_normalized_error (hb n x hx) (hδ n x hx) (hδπ n x hx)
    (hE n) (div_nonneg (hB n) hs.le) (F n x) (A₀ n x) (hi n x hx) (hcentral n x hx) hout
  have hcancel : Real.sqrt (b n x) * (B n / Real.sqrt (b n x)) = B n := by field_simp
  rw [hcancel] at hh
  have hexp : Real.exp (-b n x * δ n x ^ 2 / 2) ≤ Real.exp (-r n / 2) := by
    apply Real.exp_le_exp.mpr
    linarith [hwidth n x hx]
  have htail : ‖A₀ n x‖ * Real.exp (-b n x * δ n x ^ 2 / 2) * Real.sqrt (2 * Real.pi) ≤
      M * Real.exp (-r n / 2) * Real.sqrt (2 * Real.pi) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul (hA n x hx) hexp (Real.exp_pos _).le hM) (Real.sqrt_nonneg _)
  rw [dist_zero_left]
  exact (hh.trans (add_le_add le_rfl htail)).trans_lt hn

end HeightPaper
