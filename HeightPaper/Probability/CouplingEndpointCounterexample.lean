module

public import HeightPaper.Probability.GeometricComparison

/-! # The missing terminal-step hypothesis in the printed tree coupling -/

@[expose] public section

open MeasureTheory

namespace HeightPaper.Branching

/-- A geometric offspring law with parameter below one cannot be realized by
a root that is almost surely childless. This is the one-step obstruction to
`lem:couplage` when the terminal recovery probability is unconstrained. -/
theorem no_geometric_offspring_of_ae_childless
    {q : unitInterval} (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (offspring : Ω → ℕ) (hm : Measurable offspring)
    (hlaw : μ.map offspring = (offspringLaw q).toMeasure)
    (hzero : ∀ᵐ ω ∂μ, offspring ω = 0) : False := by
  have hset : μ {ω | offspring ω = 0} = 1 := by
    have hh := (ae_iff_measure_eq
      ((hm (measurableSet_singleton 0)).nullMeasurableSet)).mp hzero
    simpa only [measure_univ, Set.mem_singleton_iff] using hh
  have hmass : offspringLaw q 0 = 1 := by
    have hh : (offspringLaw q).toMeasure ({0} : Set ℕ) = 1 := by
      rw [← hlaw, Measure.map_apply hm (measurableSet_singleton 0)]
      simpa only [Set.preimage, Set.mem_singleton_iff] using hset
    simpa only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton 0)] using hh
  have hqne : q ≠ 0 := by
    intro h
    have hh := congrArg Subtype.val h
    simpa using hq0.ne' hh
  rw [offspringLaw_apply hqne 0] at hmass
  have hreal := congrArg ENNReal.toReal hmass
  simp only [pow_zero, one_mul, ENNReal.toReal_ofReal q.property.1,
    ENNReal.toReal_one] at hreal
  linarith

end HeightPaper.Branching
