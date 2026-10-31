module

public import HeightPaper.Probability.FinitePMF

/-! # Finite iteration of time-dependent probability kernels -/

@[expose] public section

open MeasureTheory

namespace HeightPaper.FinitePMF

variable {α : Type*}

/-- Marginal law after successive draws from time-dependent probability kernels. -/
noncomputable def kernelEvolve (initial : PMF α) (K : ℕ → α → PMF α) : ℕ → PMF α
  | 0 => initial
  | k + 1 => (kernelEvolve initial K k).bind (K k)

theorem kernelEvolve_support_finite (initial : PMF α) (K : ℕ → α → PMF α)
    (hi : initial.support.Finite) (hK : ∀ k s, (K k s).support.Finite) (k : ℕ) :
    (kernelEvolve initial K k).support.Finite := by
  induction k with
  | zero => exact hi
  | succ k ih => exact finite_support_bind _ _ ih (fun s _ ↦ hK k s)

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Any property valid on the support holds almost surely under a PMF. -/
theorem ae_of_forall_mem_support (μ : PMF α) {P : α → Prop}
    (hP : ∀ x ∈ μ.support, P x) : ∀ᵐ x ∂μ.toMeasure, P x := by
  rw [← PMF.restrict_toMeasure_support μ]
  exact (ae_restrict_mem μ.support_countable.measurableSet).mono (fun x hx ↦ hP x hx)

theorem kernelEvolve_integral_succ (initial : PMF α) (K : ℕ → α → PMF α)
    (hi : initial.support.Finite) (hK : ∀ k s, (K k s).support.Finite)
    (hm : ∀ k, Measurable (fun s ↦ (K k s).toMeasure)) (k : ℕ) (f : α → ℝ) :
    (∫ s, f s ∂(kernelEvolve initial K (k + 1)).toMeasure) =
      ∫ s, (∫ t, f t ∂(K k s).toMeasure) ∂(kernelEvolve initial K k).toMeasure :=
  integral_bind_of_finite_support _ _ (hm k)
    (kernelEvolve_support_finite initial K hi hK k) (fun s _ ↦ hK k s) f

end HeightPaper.FinitePMF
