module

public import HeightPaper.Probability.CorrectedCouplingFreshPairs
public import Mathlib.Probability.Independence.Integration

/-!
# Integrating a fresh binary update of a countable state
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

theorem integral_binary_of_indepFun
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → Bool) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ) (a : ℝ)
    (hfalse : μ.real {ω | Y ω = false} = a) (htrue : μ.real {ω | Y ω = true} = 1 - a)
    (f : α → Bool → ℝ) (hf : ∀ x b, 0 ≤ f x b ∧ f x b ≤ 1) :
    (∫ ω, f (X ω) (Y ω) ∂μ) =
      ∫ ω, (a * f (X ω) false + (1 - a) * f (X ω) true) ∂μ := by
  classical
  let g : Bool → Bool → ℝ := fun b y ↦ if y = b then 1 else 0
  have hfb (b : Bool) : Measurable (fun x ↦ f x b) := measurable_of_countable _
  have hgb (b : Bool) : Measurable (g b) := measurable_of_countable _
  have hint (b : Bool) : Integrable (fun ω ↦ f (X ω) b * g b (Y ω)) μ := by
    apply Integrable.of_bound (((hfb b).comp hX).mul ((hgb b).comp hY)).aestronglyMeasurable 1
    apply ae_of_all
    intro ω
    change ‖f (X ω) b * g b (Y ω)‖ ≤ 1
    by_cases h : Y ω = b
    · simp only [g, ite_eq_left h, mul_one, Real.norm_eq_abs, abs_of_nonneg (hf _ _).1]
      exact (hf _ _).2
    · simp only [g, ite_eq_right h, mul_zero, norm_zero, zero_le_one]
  have hfi (b : Bool) : Integrable (fun ω ↦ f (X ω) b) μ :=
    Integrable.of_bound ((hfb b).comp hX).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _ _).1] using (hf (X ω) b).2)
  have hgint (b : Bool) : (∫ ω, g b (Y ω) ∂μ) = μ.real {ω | Y ω = b} := by
    have hA : MeasurableSet {ω | Y ω = b} := by
      convert hY (measurableSet_singleton b) using 1
      ext ω
      simp
    have he : (fun ω ↦ g b (Y ω)) = Set.indicator {ω | Y ω = b} (fun _ ↦ (1 : ℝ)) := by
      funext ω
      simp [g, Set.indicator]
    rw [he, integral_indicator_const _ hA]
    simp
  have he (ω : Ω) : f (X ω) (Y ω) = f (X ω) false * g false (Y ω) + f (X ω) true * g true (Y ω) := by
    cases Y ω <;> simp [g]
  rw [integral_congr_ae (ae_of_all _ he), integral_add (hint false) (hint true),
    hXY.integral_fun_comp_mul_comp hX.aemeasurable hY.aemeasurable
      (hfb false).aestronglyMeasurable (hgb false).aestronglyMeasurable,
    hXY.integral_fun_comp_mul_comp hX.aemeasurable hY.aemeasurable
      (hfb true).aestronglyMeasurable (hgb true).aestronglyMeasurable,
    hgint false, hgint true, hfalse, htrue,
    integral_add ((hfi false).const_mul a) ((hfi true).const_mul (1 - a)),
    integral_const_mul, integral_const_mul]
  ring

end HeightPaper.CountCoupling
