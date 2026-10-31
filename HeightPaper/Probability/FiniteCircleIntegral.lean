module

public import HeightPaper.Analysis.AnalyticCircleControl
public import HeightPaper.Probability.FinitePMF
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Boundary integrals of finite profile laws

Finite support permits exact interchange of the parent-draw expectation and
the circle integral, without any additional joint-integrability assumption.
-/

@[expose] public section

open MeasureTheory Complex Metric Set
open scoped BigOperators

namespace HeightPaper

theorem finitePMF_integral_eq_finset_sum {α E : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : PMF α) (hp : p.support.Finite) (f : α → E) :
    (∫ x, f x ∂p.toMeasure) = ∑ x ∈ hp.toFinset, (p x).toReal • f x := by
  classical
  rw [PMF.integral_eq_tsum p f (FinitePMF.integrable_of_finite_support p hp f)]
  apply tsum_eq_sum
  intro x hx
  have hz : p x = 0 := by simpa [PMF.mem_support_iff] using hx
  simp [hz]

theorem finitePMF_integral_circleL1 {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (hp : p.support.Finite)
    (c : ℂ) (R : ℝ) (f : α → ℂ → ℂ)
    (hf : ∀ x ∈ p.support, ContinuousOn (f x) (sphere c |R|)) :
    (∫ x, circleL1 c R (f x) ∂p.toMeasure) =
      ∫ t : ℝ in 0..2 * Real.pi, ∫ x, ‖f x (circleMap c R t)‖ ∂p.toMeasure := by
  classical
  rw [finitePMF_integral_eq_finset_sum p hp]
  simp only [circleL1]
  simp_rw [finitePMF_integral_eq_finset_sum p hp]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_smul]
  · intro x hx
    exact (circleL1_integrable (hf x (by simpa using hx))).smul ((p x).toReal)

theorem finitePMF_integral_circleL1_le {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (hp : p.support.Finite)
    (c : ℂ) (R : ℝ) (f : α → ℂ → ℂ)
    (hf : ∀ x ∈ p.support, ContinuousOn (f x) (sphere c |R|))
    {B : ℝ} (hB : ∀ z ∈ sphere c |R|, (∫ x, ‖f x z‖ ∂p.toMeasure) ≤ B) :
    (∫ x, circleL1 c R (f x) ∂p.toMeasure) ≤ 2 * Real.pi * B := by
  classical
  have hi : IntervalIntegrable
      (fun t => ∫ x, ‖f x (circleMap c R t)‖ ∂p.toMeasure) volume 0 (2 * Real.pi) := by
    simp_rw [finitePMF_integral_eq_finset_sum p hp]
    convert (IntervalIntegrable.sum hp.toFinset (fun x hx =>
      (circleL1_integrable (hf x (by simpa using hx))).smul ((p x).toReal))) using 1
    ext t
    simp only [Finset.sum_apply, Pi.smul_apply]
  rw [finitePMF_integral_circleL1 p hp c R f hf]
  have hb := intervalIntegral.integral_mono_on Real.two_pi_pos.le hi
    (intervalIntegrable_const (a := (0 : ℝ)) (b := 2 * Real.pi) (c := B))
    (fun t _ => hB _ (circleMap_mem_sphere' c R t))
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hb

end HeightPaper
