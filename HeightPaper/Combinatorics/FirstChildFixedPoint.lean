module

public import HeightPaper.Combinatorics.GeometricBranching

/-!
Adapted from the generic Bienaymé-law utilities in the sibling `freezing1`
project, using the same pinned Lean and Mathlib 4.35.0.

# From the source conditional split to a genuine measure fixed point

The positive-degree conditional law is needed only when that event has
nonzero mass. The zero-mass case is handled by a zero restricted measure,
so the degenerate geometric parameter is retained.
-/

@[expose] public section

namespace HeightPaper.FirstChildStructure

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {T : Type*} [MeasurableSpace T]

theorem fixedPoint_of_conditional_split (D : FirstChildStructure T)
    (rest : T → T) (hrest : Measurable rest)
    (hzero : ∀ t, D.degree t = 0 → t = D.leaf)
    (hinverse : ∀ t, 0 < D.degree t → D.graft (D.child t 0, rest t) = t)
    (μ : Measure T) [IsProbabilityMeasure μ] (q r : ℝ≥0∞)
    (h0 : μ {t | D.degree t = 0} = q) (hp : μ {t | 0 < D.degree t} = r)
    (hsplit : r ≠ 0 →
      (ProbabilityTheory.cond μ {t | 0 < D.degree t}).map
        (fun t => (D.child t 0, rest t)) = μ.prod μ) :
    μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft := by
  let S : Set T := {t | 0 < D.degree t}
  let split : T → T × T := fun t => (D.child t 0, rest t)
  have hS : MeasurableSet S := D.measurable_degree (by trivial)
  have hsplitM : Measurable split := (D.measurable_child 0).prodMk hrest
  have hz : {t | D.degree t = 0} = {D.leaf} := by
    ext t
    constructor
    · exact fun ht => hzero t ht
    · rintro rfl
      exact D.degree_leaf
  have hzeroLaw : μ.restrict {t | D.degree t = 0} = q • Measure.dirac D.leaf := by
    rw [hz, Measure.restrict_singleton, ← h0, hz]
  have hsplitLaw : (μ.restrict S).map split = r • μ.prod μ := by
    by_cases hr : r = 0
    · have he : μ.restrict S = 0 := Measure.restrict_eq_zero.mpr (hp.trans hr)
      simp [he, hr]
    · have hrT : r ≠ ∞ := hp ▸ measure_ne_top μ S
      have hh := congrArg (fun ν : Measure (T × T) => r • ν) (hsplit hr)
      change r • (ProbabilityTheory.cond μ S).map split = _ at hh
      rw [ProbabilityTheory.cond, Measure.map_smul _ hsplitM.aemeasurable,
        smul_smul, hp, ENNReal.mul_inv_cancel hr hrT, one_smul] at hh
      exact hh
  have hpositiveLaw : μ.restrict S = r • (μ.prod μ).map D.graft := by
    calc
      μ.restrict S = (μ.restrict S).map (D.graft ∘ split) := by
        nth_rw 1 [← Measure.map_id (μ := μ.restrict S)]
        apply Measure.map_congr
        exact (ae_restrict_mem hS).mono fun t ht => (hinverse t ht).symm
      _ = ((μ.restrict S).map split).map D.graft :=
        (Measure.map_map D.measurable_graft hsplitM).symm
      _ = r • (μ.prod μ).map D.graft := by
        rw [hsplitLaw, Measure.map_smul _ D.measurable_graft.aemeasurable]
  have hcompl : {t | D.degree t = 0}ᶜ = S := by
    ext t
    simp [S, Nat.pos_iff_ne_zero]
  calc
    μ = μ.restrict {t | D.degree t = 0} + μ.restrict S := by
      rw [← hcompl]
      exact (Measure.restrict_add_restrict_compl (μ := μ)
        (show MeasurableSet {t | D.degree t = 0} from
          D.measurable_degree (measurableSet_singleton 0))).symm
    _ = _ := by rw [hzeroLaw, hpositiveLaw]

end HeightPaper.FirstChildStructure
