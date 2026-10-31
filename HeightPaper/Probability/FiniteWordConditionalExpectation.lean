module

public import HeightPaper.Probability.ConditionalParentExpectation
public import HeightPaper.Probability.TreeUniformCoupling
public import HeightPaper.Probability.FiniteEventMeasurable

/-!
# Conditioning a finite-word observable on the full epidemic event word

An integrable parent observable whose parent integral only depends on a
finite birth prefix has the expected full-word conditional expectation.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper.CountCoupling

/-- Conditioning on all binary event choices agrees almost everywhere with
integrating the independent parent uniforms, provided that integral depends
only on the first `H` event choices. -/
theorem finiteWord_condExp_eventWord_eq_parent_integral
    (l : ℝ) (n H : ℕ)
    (F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hFmeas : Measurable F) (hFint : Integrable F birthParentLaw)
    (hprefix : ∀ u u' : ℕ → ℝ,
      (∀ i < H, finiteBirth l n u i = finiteBirth l n u' i) →
      (∫ v, F (u, v) ∂uniformLaw) = ∫ v, F (u', v) ∂uniformLaw) :
    (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦ ∫ v, F (r.1, v) ∂uniformLaw)
      =ᵐ[birthParentLaw]
        birthParentLaw[F |
          (inferInstance : MeasurableSpace (ℕ → Bool)).comap
            (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦ finiteBirth l n r.1)] := by
  let g : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun r ↦
    ∫ v, F (r.1, v) ∂uniformLaw
  let W : ((ℕ → ℝ) × (ℕ → ℝ)) → (ℕ → Bool) := fun r ↦ finiteBirth l n r.1
  let code : ((ℕ → ℝ) × (ℕ → ℝ)) → (Fin H → Bool) :=
    fun r i ↦ W r i
  have hW₀ : Measurable (finiteBirth l n) :=
    measurable_pi_iff.mpr (measurable_finiteBirth l n)
  have hW : Measurable W := hW₀.comp measurable_fst
  let mword : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (MeasurableSpace.pi : MeasurableSpace (ℕ → Bool)).comap W
  let mfst : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (MeasurableSpace.pi : MeasurableSpace (ℕ → ℝ)).comap Prod.fst
  have hwordfst : mword ≤ mfst := by
    have hh : Measurable[mfst] W := hW₀.comp (comap_measurable Prod.fst)
    exact hh.comap_le
  have hword₀ : mword ≤
      (Prod.instMeasurableSpace : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))) := by
    simpa only [mword] using hW.comap_le
  have hprefixMeas : Measurable (fun b : ℕ → Bool ↦ fun i : Fin H ↦ b i) :=
    Measurable.of_eval (fun i ↦ measurable_pi_apply (i : ℕ))
  have hcodeword :
      (inferInstance : MeasurableSpace (Fin H → Bool)).comap code ≤ mword := by
    have hh : Measurable[mword] code := hprefixMeas.comp (comap_measurable W)
    exact hh.comap_le
  have hgcongr (r s : (ℕ → ℝ) × (ℕ → ℝ)) (hc : code r = code s) :
      g r = g s :=
    hprefix r.1 s.1 (fun i hi ↦ congrFun hc ⟨i, hi⟩)
  have hgm : StronglyMeasurable[mword] g :=
    (stronglyMeasurable_comap_of_finite_code code g hgcongr).mono hcodeword
  have hgint : Integrable g birthParentLaw := by
    change Integrable (fun r : (ℕ → ℝ) × (ℕ → ℝ) ↦
      (fun u ↦ ∫ v, F (u, v) ∂uniformLaw) r.1) birthParentLaw
    exact hFint.integral_prod_left.comp_fst uniformLaw
  have hfst : g =ᵐ[birthParentLaw] birthParentLaw[F | mfst] :=
    Measure.condExp_fst_prod_ae_eq_integral uniformLaw uniformLaw F hFmeas hFint
  have hself : birthParentLaw[g | mword] = g :=
    condExp_of_stronglyMeasurable (μ := birthParentLaw) hword₀ hgm hgint
  have htower := condExp_condExp_of_le
    (μ := birthParentLaw) (f := F) hwordfst measurable_fst.comap_le
  have hcongr := condExp_congr_ae (m := mword) hfst.symm
  change g =ᵐ[birthParentLaw] birthParentLaw[F | mword]
  calc
    g =ᵐ[birthParentLaw] birthParentLaw[g | mword] := by rw [hself]
    _ =ᵐ[birthParentLaw] birthParentLaw[birthParentLaw[F | mfst] | mword] := hcongr.symm
    _ =ᵐ[birthParentLaw] birthParentLaw[F | mword] := htower

end HeightPaper.CountCoupling
