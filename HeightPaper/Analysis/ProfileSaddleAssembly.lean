module

public import HeightPaper.Analysis.ProfileSaddleAmplitude

/-!
# Saddle assembly with a direct outer-integral bound

The stochastic Fourier estimates bound the outer integral itself in mean,
then in probability. These deterministic assembly lemmas consume that bound
without requiring a pathwise supremum of the integrand over frequencies.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace HeightPaper

theorem lattice_saddle_error_of_central_outer {b δ E B : ℝ}
    (hb : 0 < b) (hδ : 0 ≤ δ) (hδπ : δ ≤ Real.pi) (hE : 0 ≤ E) (_hB : 0 ≤ B)
    (F : ℝ → ℂ) (A₀ : ℂ)
    (hi : IntervalIntegrable F volume (-Real.pi) Real.pi)
    (hcentral : ‖(∫ u : ℝ in -δ..δ, F u) -
      A₀ * ((∫ u : ℝ in -δ..δ, Real.exp (-b * u ^ 2) : ℝ) : ℂ)‖ ≤
        E * ∫ u : ℝ in -δ..δ, Real.exp (-b * u ^ 2))
    (houter : ‖(∫ u : ℝ in -Real.pi..-δ, F u) +
      (∫ u : ℝ in δ..Real.pi, F u)‖ ≤ B) :
    ‖(∫ u : ℝ in -Real.pi..Real.pi, F u) -
      A₀ * (Real.sqrt (Real.pi / b) : ℂ)‖ ≤
        E * Real.sqrt (Real.pi / b) + B +
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
  have ho := houter
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
theorem lattice_saddle_normalized_error_of_central_outer {b δ E B : ℝ}
    (hb : 0 < b) (hδ : 0 ≤ δ) (hδπ : δ ≤ Real.pi) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (F : ℝ → ℂ) (A₀ : ℂ)
    (hi : IntervalIntegrable F volume (-Real.pi) Real.pi)
    (hcentral : ‖(∫ u : ℝ in -δ..δ, F u) -
      A₀ * ((∫ u : ℝ in -δ..δ, Real.exp (-b * u ^ 2) : ℝ) : ℂ)‖ ≤
        E * ∫ u : ℝ in -δ..δ, Real.exp (-b * u ^ 2))
    (houter : ‖(∫ u : ℝ in -Real.pi..-δ, F u) +
      (∫ u : ℝ in δ..Real.pi, F u)‖ ≤ B) :
    ‖(Real.sqrt b : ℂ) * (∫ u : ℝ in -Real.pi..Real.pi, F u) -
      A₀ * (Real.sqrt Real.pi : ℂ)‖ ≤
        E * Real.sqrt Real.pi + Real.sqrt b * B +
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
    (lattice_saddle_error_of_central_outer hb hδ hδπ hE hB F A₀ hi hcentral houter)
      (Real.sqrt_nonneg b)
  convert hh using 1
  calc
    _ = E * (Real.sqrt b * Real.sqrt (Real.pi / b)) +
        Real.sqrt b * B + ‖A₀‖ * Real.exp (-b * δ ^ 2 / 2) *
          (Real.sqrt b * Real.sqrt (Real.pi / (b / 2))) := by rw [hs, hs₂]
    _ = _ := by ring

/-- The complete corrected varying-amplitude estimate, accepting the direct
outer-integral bound supplied by conditional Markov estimates. -/
theorem poissonSaddleAmplitude_lattice_error_of_outer {a θ δ M η B : ℝ}
    (ha : 0 < a) (hθ : 0 < θ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : 0 ≤ M) (hη : 0 ≤ η) (hB : 0 ≤ B) (hsmall : a * θ * δ ^ 3 ≤ 1)
    (A : ℝ → ℂ) (A₀ : ℂ) (hcont : ContinuousOn A (Icc (-Real.pi) Real.pi))
    (hA : ∀ u ∈ Icc (-δ) δ, ‖A u‖ ≤ M)
    (hclose : ∀ u ∈ Icc (-δ) δ, ‖A u - A₀‖ ≤ η)
    (houter : ‖(∫ u : ℝ in -Real.pi..-δ,
        A u * Complex.exp ((a : ℂ) * poissonSaddlePhase θ u)) +
      (∫ u : ℝ in δ..Real.pi, A u * Complex.exp ((a : ℂ) * poissonSaddlePhase θ u))‖ ≤ B) :
    ‖(Real.sqrt (a * θ / 2) : ℂ) *
        (∫ u : ℝ in -Real.pi..Real.pi, A u * Complex.exp ((a : ℂ) * poissonSaddlePhase θ u)) -
      A₀ * (Real.sqrt Real.pi : ℂ)‖ ≤
        (η + 2 * M * a * θ * δ ^ 3) * Real.sqrt Real.pi +
          Real.sqrt (a * θ / 2) * B +
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
  have hh := lattice_saddle_normalized_error_of_central_outer (show 0 < a * θ / 2 by positivity)
    hδ hδπ (show 0 ≤ η + 2 * M * a * θ * δ ^ 3 by positivity) hB _ A₀ hi hcent houter
  simpa only [show -(a * θ / 2) * δ ^ 2 / 2 = -a * θ * δ ^ 2 / 4 by ring] using hh

end HeightPaper
