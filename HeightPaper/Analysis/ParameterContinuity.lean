module

public import HeightPaper.Analysis.Critical
public import Mathlib.Topology.Order.Compact

/-!
# Continuity of the height parameters

The unique roots are continuous by inversion on a compact interval. The
variational formula then proves continuity of the height coefficient across
the critical parameter. This does not assert the stronger differentiability
claims about the phase transition.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace HeightPaper

theorem continuousOn_offspringMean : ContinuousOn offspringMean (Ioi 1) := by
  let F : Icc (0 : ℝ) 1 → ℝ := fun x ↦ meanEquation x
  have hF : Continuous F := continuous_meanEquation.comp continuous_subtype_val
  have hi : Function.Injective F := by
    intro x y hxy
    exact Subtype.ext (meanEquation_strictMonoOn.injOn x.property y.property hxy)
  let M : Ioi (1 : ℝ) → Icc (0 : ℝ) 1 := fun l ↦
    ⟨offspringMean l, (offspringMean_spec l.property).1.1.le,
      (offspringMean_spec l.property).1.2.le⟩
  have hc : Continuous M := (hF.isClosedEmbedding hi).isEmbedding.continuous_iff.mpr (by
    have heq : F ∘ M = fun l : Ioi (1 : ℝ) ↦ meanEquation l := by
      funext l
      exact (offspringMean_spec l.property).2
    rw [heq]
    exact continuous_meanEquation.comp continuous_subtype_val)
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hc)

theorem continuousOn_profileRoot : ContinuousOn profileRoot (Ioi 1) := by
  let f : ℝ → ℝ := fun z ↦ (1 - z) * Real.exp z
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hanti : StrictAntiOn f (Icc 0 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hf.continuousOn
    intro z hz
    rw [interior_Icc, mem_Ioo] at hz
    have hd : HasDerivAt f (-z * Real.exp z) z := by
      convert (((hasDerivAt_id z).const_sub 1).mul (Real.hasDerivAt_exp z)) using 1
      · rfl
      · simp only [id_eq]; ring
    rw [hd.deriv]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hz.1) (Real.exp_pos z)
  let F : Icc (0 : ℝ) 1 → ℝ := fun x ↦ f x
  have hF : Continuous F := hf.comp continuous_subtype_val
  have hi : Function.Injective F := by
    intro x y hxy
    exact Subtype.ext (hanti.injOn x.property y.property hxy)
  let Z : Ioi (1 : ℝ) → Icc (0 : ℝ) 1 := fun l ↦
    ⟨profileRoot l, (profileRoot_pos l.property).le, (profileRoot_lt_one l.property).le⟩
  have hc : Continuous Z := (hF.isClosedEmbedding hi).isEmbedding.continuous_iff.mpr (by
    have heq : F ∘ Z = fun l : Ioi (1 : ℝ) ↦ 1 / (l : ℝ) := by
      funext l
      exact profileRoot_equation l.property
    rw [heq]
    exact continuous_const.div continuous_subtype_val
      (fun l ↦ ne_of_gt (lt_trans zero_lt_one l.property)))
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hc)

theorem continuousAt_offspringMean {l : ℝ} (hl : 1 < l) : ContinuousAt offspringMean l :=
  continuousOn_offspringMean.continuousAt (isOpen_Ioi.mem_nhds hl)

theorem continuousAt_profileRoot {l : ℝ} (hl : 1 < l) : ContinuousAt profileRoot l :=
  continuousOn_profileRoot.continuousAt (isOpen_Ioi.mem_nhds hl)

theorem continuousAt_outgrowthRate {l : ℝ} (hl : 1 < l) : ContinuousAt outgrowthRate l :=
  ((continuousAt_offspringMean hl).log (offspringMean_pos hl).ne').neg

theorem continuousAt_heightCoefficient {l : ℝ} (hl : 1 < l) :
    ContinuousAt heightCoefficient l := by
  have hg : ContinuousAt growthFactor l :=
    continuousAt_id.div (continuousAt_id.sub continuousAt_const) (sub_pos.mpr hl).ne'
  have hr := continuousAt_outgrowthRate hl
  have hz := (continuousAt_profileRoot hl).min hr
  have he : ContinuousAt (fun x ↦ Real.exp (min (profileRoot x) (outgrowthRate x))) l :=
    Real.continuous_exp.continuousAt.comp hz
  have hf : ContinuousAt (fun l ↦ profileExponent l
      (min (profileRoot l) (outgrowthRate l))) l :=
    continuousAt_const.add (hg.mul ((he.sub continuousAt_const).sub (hz.mul he)))
  exact (hg.mul he).add (hf.div hr (outgrowthRate_pos hl).ne')

/-- In particular there is no discontinuity in the coefficient at the critical
parameter; equality of the two branches follows from the variational formula. -/
theorem continuousOn_mainCoefficient : ContinuousOn mainCoefficient (Ioi 1) := by
  apply (show ContinuousOn heightCoefficient (Ioi 1) from
    fun l hl ↦ (continuousAt_heightCoefficient hl).continuousWithinAt).congr
  intro l hl
  exact mainCoefficient_eq_heightCoefficient hl

theorem continuousAt_mainCoefficient {l : ℝ} (hl : 1 < l) :
    ContinuousAt mainCoefficient l :=
  continuousOn_mainCoefficient.continuousAt (isOpen_Ioi.mem_nhds hl)

end HeightPaper
