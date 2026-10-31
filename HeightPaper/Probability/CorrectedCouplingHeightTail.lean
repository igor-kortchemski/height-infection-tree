module

public import HeightPaper.Probability.CorrectedCouplingBoundingTreeLaw
public import HeightPaper.Combinatorics.FiniteShapeHeight
public import HeightPaper.Probability.GeometricComparison

/-!
# The coupled tree heights have the certified branching tails

The first-child fixed point gives the empty-level recursion directly. This
identifies the height tail without assuming an unproved generation marginal.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HeightPaper.CountCoupling

open PlaneForward
open scoped Classical

noncomputable def emptyLevelProbability (a : ℝ) (h : ℕ) : ℝ :=
  (oneRootShapeLaw a).real {t | belowLevel t h}

theorem emptyLevelProbability_zero (a : ℝ) : emptyLevelProbability a 0 = 0 := by
  simp [emptyLevelProbability, not_belowLevel_zero]

theorem emptyLevelProbability_succ {a : ℝ} (ha : 1 / 2 < a) (ha1 : a ≤ 1) (h : ℕ) :
    emptyLevelProbability a (h + 1) = a / (1 - (1 - a) * emptyLevelProbability a h) := by
  let E := fun k ↦ {t : FiniteShape | belowLevel t k}
  have hE (k : ℕ) : MeasurableSet (E k) := Set.to_countable _ |>.measurableSet
  have hpre : (fun z : FiniteShape × FiniteShape ↦ graftShapes z.1 z.2) ⁻¹' E (h + 1) =
      E h ×ˢ E (h + 1) := by
    ext z
    exact belowLevel_graft z.1 z.2 h
  have hm := congrArg (fun ν : Measure FiniteShape ↦ ν (E (h + 1))) (oneRootShapeLaw_fixedPoint ha ha1)
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    Measure.dirac_apply' _ (hE _),
    Set.indicator_of_mem (show leafShape ∈ E (h + 1) from belowLevel_leaf_succ h),
    Measure.map_apply (measurable_of_countable _) (hE _), hpre, Measure.prod_prod] at hm
  simp only [Pi.one_apply, mul_one] at hm
  have ha0 : 0 ≤ a := by linarith
  have hreal := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ha1)] at hreal
  change emptyLevelProbability a (h + 1) = a + (1 - a) *
    (emptyLevelProbability a h * emptyLevelProbability a (h + 1)) at hreal
  have he1 : emptyLevelProbability a h ≤ 1 := measureReal_le_one
  have hmul : (1 - a) * emptyLevelProbability a h ≤ 1 - a :=
    mul_le_of_le_one_right (sub_nonneg.mpr ha1) he1
  have hden : 0 < 1 - (1 - a) * emptyLevelProbability a h := by linarith
  apply (eq_div_iff hden.ne').mpr
  nlinarith [hreal]

theorem emptyLevelProbability_eq_extinctionProbability
    (a : unitInterval) (ha : 1 / 2 < (a : ℝ)) (h : ℕ) :
    emptyLevelProbability a h = Branching.extinctionProbability a h := by
  have ha0 : a ≠ 0 := by
    intro he
    have hz := congrArg (fun x : unitInterval ↦ (x : ℝ)) he
    change (a : ℝ) = 0 at hz
    linarith
  induction h with
  | zero => rw [emptyLevelProbability_zero, Branching.extinctionProbability_zero]
  | succ h ih =>
      rw [emptyLevelProbability_succ ha a.2.2, Branching.extinctionProbability_succ ha0, ih]

theorem oneRootShapeLaw_heightTail (a : unitInterval) (ha : 1 / 2 < (a : ℝ)) (h : ℕ) :
    (oneRootShapeLaw a).real {t | h ≤ t.height} = Branching.heightTail a h := by
  have hE : MeasurableSet {t : FiniteShape | belowLevel t h} := Set.to_countable _ |>.measurableSet
  have he : {t : FiniteShape | h ≤ t.height} = {t | belowLevel t h}ᶜ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, belowLevel_iff_height_lt, not_lt]
  rw [he, measureReal_compl hE]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
  change 1 - emptyLevelProbability a h = Branching.heightTail a h
  rw [emptyLevelProbability_eq_extinctionProbability a ha, Branching.heightTail_eq_one_sub]

theorem terminalBoundShape_heightTail
    (N : ℕ) (hN : 0 < N) (p q : unitInterval) (hp : 1 / 2 < (p : ℝ)) (hpq : p ≤ q)
    (r : List Bool → ℝ) (upper : Bool) (i : Fin N) (h : ℕ) :
    pairedUniformLaw.real {w | h ≤ (terminalBoundShape N p q r upper w i).height} =
      Branching.heightTail (boundForestParameter upper p q) h := by
  have hmeas : Measurable (fun w ↦ terminalBoundShape N p q r upper w i) :=
    (measurable_pi_apply i).comp (measurable_terminalBoundShape N p q r upper)
  have hE : MeasurableSet {t : FiniteShape | h ≤ t.height} := Set.to_countable _ |>.measurableSet
  have hmass := congrArg (fun ν : Measure FiniteShape ↦ ν.real {t | h ≤ t.height})
    (terminalBoundShape_component_law N hN hp hpq q.2.2 r upper i)
  rw [map_measureReal_apply hmeas hE] at hmass
  have hpqR : (p : ℝ) ≤ (q : ℝ) := hpq
  have ha : 1 / 2 < (boundForestParameter upper p q : ℝ) := by
    rw [coe_boundForestParameter]
    cases upper <;> dsimp [boundForestRate] <;> linarith
  rw [← coe_boundForestParameter, oneRootShapeLaw_heightTail _ ha] at hmass
  exact hmass

end HeightPaper.CountCoupling
