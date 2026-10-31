module

public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Iterated expectation for finite-support probability mass functions

Finite epidemic kernels have finite support even though their ambient state
space is infinite. These lemmas make that finiteness available to the ordinary
Bochner integral and identify PMF bind with measurable-kernel composition.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HeightPaper.FinitePMF

variable {α β : Type*}

theorem finite_support_map (p : PMF α) (hp : p.support.Finite) (f : α → β) :
    (p.map f).support.Finite := by
  rw [PMF.support_map]
  exact hp.image f

theorem finite_support_bind (p : PMF α) (q : α → PMF β) (hp : p.support.Finite)
    (hq : ∀ a ∈ p.support, (q a).support.Finite) : (p.bind q).support.Finite := by
  rw [PMF.support_bind]
  exact hp.biUnion hq

variable [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β]

theorem integrable_of_finite_support {E : Type*} [NormedAddCommGroup E]
    (p : PMF α) (hp : p.support.Finite) (f : α → E) :
    Integrable f p.toMeasure := by
  have h : IntegrableOn f p.support p.toMeasure := IntegrableOn.of_finite hp
  simpa only [IntegrableOn, PMF.restrict_toMeasure_support] using h

theorem lintegral_eq_tsum (p : PMF α) (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂p.toMeasure = ∑' a, p a * f a := by
  calc
    ∫⁻ a, f a ∂p.toMeasure = ∫⁻ a in p.support, f a ∂p.toMeasure := by
      rw [PMF.restrict_toMeasure_support]
    _ = ∑' a : p.support, f a * p.toMeasure {(a : α)} :=
      lintegral_countable f p.support_countable
    _ = ∑' a : p.support, p a * f a := by
      apply tsum_congr
      intro a
      rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _), mul_comm]
    _ = ∑' a, p a * f a := by
      apply tsum_subtype_eq_of_support_subset (f := fun a : α ↦ p a * f a) (s := p.support)
      intro a ha
      by_contra hnot
      have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using hnot
      exact ha (by simp [hz])


/-- A family of PMFs whose associated measures vary measurably. -/
@[expose] noncomputable def toKernel (q : α → PMF β)
    (hq : Measurable (fun a ↦ (q a).toMeasure)) : Kernel α β := ⟨fun a ↦ (q a).toMeasure, hq⟩

theorem toKernel_comp (p : PMF α) (q : α → PMF β)
    (hq : Measurable (fun a ↦ (q a).toMeasure)) :
    toKernel q hq ∘ₘ p.toMeasure = (p.bind q).toMeasure := by
  ext s hs
  change ((fun a ↦ (q a).toMeasure) ∘ₘ p.toMeasure) s = _
  rw [Measure.bind_apply hs hq.aemeasurable, lintegral_eq_tsum,
    PMF.toMeasure_bind_apply p q s hs]

/-- The law of iterated expectation for PMF bind. In particular every real
observable is admissible when the composed PMF has finite support. -/
theorem integral_bind {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : PMF α) (q : α → PMF β)
    (hq : Measurable (fun a ↦ (q a).toMeasure)) (f : β → E)
    (hf : Integrable f (p.bind q).toMeasure) :
    ∫ b, f b ∂(p.bind q).toMeasure = ∫ a, ∫ b, f b ∂(q a).toMeasure ∂p.toMeasure := by
  rw [← toKernel_comp p q hq, Measure.comp_eq_comp_const_apply] at hf ⊢
  exact ProbabilityTheory.Kernel.integral_comp hf

theorem integral_bind_of_finite_support [MeasurableSingletonClass β]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : PMF α) (q : α → PMF β)
    (hq : Measurable (fun a ↦ (q a).toMeasure))
    (hp : p.support.Finite) (hqfinite : ∀ a ∈ p.support, (q a).support.Finite)
    (f : β → E) :
    ∫ b, f b ∂(p.bind q).toMeasure = ∫ a, ∫ b, f b ∂(q a).toMeasure ∂p.toMeasure :=
  integral_bind p q hq f (integrable_of_finite_support _ (finite_support_bind p q hp hqfinite) f)

end HeightPaper.FinitePMF
