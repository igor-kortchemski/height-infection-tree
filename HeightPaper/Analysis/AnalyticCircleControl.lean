module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Interior analytic control from boundary integrals

These deterministic estimates convert summable boundary increments into a
uniformly convergent analytic series on every smaller disk. In particular,
they apply to dyadic increments of the profile martingale.
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology BigOperators

namespace HeightPaper

noncomputable def circleL1 (c : ℂ) (R : ℝ) (f : ℂ → ℂ) : ℝ :=
  ∫ t : ℝ in 0..2 * Real.pi, ‖f (circleMap c R t)‖

theorem circleL1_nonneg (c : ℂ) (R : ℝ) (f : ℂ → ℂ) : 0 ≤ circleL1 c R f :=
  intervalIntegral.integral_nonneg Real.two_pi_pos.le (fun _ _ => norm_nonneg _)

theorem circleL1_integrable {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (sphere c |R|)) :
    IntervalIntegrable (fun t => ‖f (circleMap c R t)‖) volume 0 (2 * Real.pi) := by
  apply Continuous.intervalIntegrable
  exact (hf.comp_continuous (continuous_circleMap c R)
    (fun t => circleMap_mem_sphere' c R t)).norm

/-- Cauchy's formula bounds every point of an inner disk by the boundary L1 norm. -/
theorem norm_le_circleL1 {c w : ℂ} {r R : ℝ} {f : ℂ → ℂ}
    (hr : 0 ≤ r) (hrR : r < R) (hf : DifferentiableOn ℂ f (closedBall c R))
    (hw : w ∈ closedBall c r) :
    ‖f w‖ ≤ R / (2 * Real.pi * (R - r)) * circleL1 c R f := by
  have hR : 0 < R := hr.trans_lt hrR
  have hwR : w ∈ ball c R := lt_of_le_of_lt hw hrR
  have hdist (t : ℝ) : R - r ≤ ‖circleMap c R t - w‖ := by
    have hs := circleMap_mem_sphere c hR.le t
    rw [mem_sphere] at hs
    have ht := dist_triangle (circleMap c R t) w c
    have hw' : dist w c ≤ r := hw
    rw [hs, dist_eq_norm] at ht
    linarith
  have hbound (t : ℝ) :
      ‖deriv (circleMap c R) t •
        ((circleMap c R t - w)⁻¹ • f (circleMap c R t))‖ ≤
        (R * (R - r)⁻¹) * ‖f (circleMap c R t)‖ := by
    simp only [norm_smul, norm_inv, deriv_circleMap, norm_mul, norm_I,
      norm_circleMap_zero, abs_of_pos hR, mul_one]
    have hi := inv_anti₀ (sub_pos.mpr hrR) (hdist t)
    have hm := mul_le_mul_of_nonneg_right hi (norm_nonneg (f (circleMap c R t)))
    nlinarith
  have hcont : ContinuousOn f (sphere c |R|) := by
    rw [abs_of_pos hR]
    exact hf.continuousOn.mono sphere_subset_closedBall
  have hnorm : ‖∮ z in C(c, R), (z - w)⁻¹ • f z‖ ≤
      (R * (R - r)⁻¹) * circleL1 c R f := by
    unfold circleIntegral
    have hb := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun t => deriv (circleMap c R) t •
        ((circleMap c R t - w)⁻¹ • f (circleMap c R t)))
      (g := fun t => (R * (R - r)⁻¹) * ‖f (circleMap c R t)‖)
      Real.two_pi_pos.le (ae_of_all volume (fun t _ => hbound t))
      ((circleL1_integrable hcont).const_mul _)
    simpa only [intervalIntegral.integral_const_mul, circleL1] using hb
  rw [hf.circleIntegral_sub_inv_smul hwR, norm_smul] at hnorm
  have hc : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by simp
  rw [hc] at hnorm
  calc
    ‖f w‖ ≤ (R * (R - r)⁻¹ * circleL1 c R f) / (2 * Real.pi) :=
      (le_div_iff₀ Real.two_pi_pos).mpr (by nlinarith)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- A summable sequence of boundary L1 norms yields uniform interior convergence. -/
theorem analytic_series_uniform_of_circleL1 {c : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) (closedBall c R))
    (hs : Summable (fun n => circleL1 c R (f n))) :
    TendstoUniformlyOn (fun n z => ∑ i ∈ Finset.range n, f i z)
      (fun z => ∑' i, f i z) atTop (closedBall c r) := by
  exact tendstoUniformlyOn_tsum_nat (hs.mul_left (R / (2 * Real.pi * (R - r))))
    (fun n z hz => norm_le_circleL1 hr hrR (hf n) hz)

theorem analytic_series_differentiable_of_circleL1 {c : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) (closedBall c R))
    (hs : Summable (fun n => circleL1 c R (f n))) :
    DifferentiableOn ℂ (fun z => ∑' i, f i z) (ball c r) := by
  apply differentiableOn_tsum_of_summable_norm
    (hs.mul_left (R / (2 * Real.pi * (R - r))))
    (fun n => (hf n).mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall hrR.le))) isOpen_ball
  intro n z hz
  exact norm_le_circleL1 hr hrR (hf n) (ball_subset_closedBall hz)

end HeightPaper
