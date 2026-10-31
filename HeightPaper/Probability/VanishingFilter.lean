module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# A filter for vanishing exceptional probabilities

For varying finite measure spaces, sets in this filter have complements whose
probabilities tend to zero. Deterministic filter-limit arguments can therefore
be reused for convergence in probability, including after restriction to a
survival event. No joint coupling of the varying spaces is required.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace HeightPaper

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]

/-- The exceptional-probability filter on the disjoint union of the spaces. -/
noncomputable def vanishingProbabilityFilter : Filter (Sigma Ω) where
  sets := {A | Tendsto (fun n ↦ (μ n).real {ω | (⟨n, ω⟩ : Sigma Ω) ∉ A}) atTop (𝓝 0)}
  univ_sets := by simp
  sets_of_superset := by
    intro A B hA hAB
    apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hA
    intro n
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro ω hω hmem
    exact hω (hAB hmem)
  inter_sets := by
    intro A B hA hB
    have hlim := hA.add hB
    simp only [add_zero] at hlim
    apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hlim
    intro n
    have heq : {ω | (⟨n, ω⟩ : Sigma Ω) ∉ A ∩ B} =
        {ω | (⟨n, ω⟩ : Sigma Ω) ∉ A} ∪ {ω | (⟨n, ω⟩ : Sigma Ω) ∉ B} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, not_and_or, mem_union]
    rw [heq]
    exact measureReal_union_le _ _

/-- Membership is precisely convergence to zero of the exceptional probability. -/
theorem eventually_vanishingProbabilityFilter_iff (P : Sigma Ω → Prop) :
    (∀ᶠ i in vanishingProbabilityFilter μ, P i) ↔
      Tendsto (fun n ↦ (μ n).real {ω | ¬P ⟨n, ω⟩}) atTop (𝓝 0) := Iff.rfl

/-- The population index still tends to infinity in this filter. -/
theorem tendsto_index_vanishingProbabilityFilter :
    Tendsto (fun i : Sigma Ω ↦ i.1) (vanishingProbabilityFilter μ) atTop := by
  apply tendsto_atTop.mpr
  intro N
  rw [eventually_vanishingProbabilityFilter_iff]
  apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  simp [hn]

/-- Real convergence along the filter is ordinary convergence in probability,
expressed without requiring measurability or a common sample space. -/
theorem tendsto_vanishingProbabilityFilter_iff (X : Sigma Ω → ℝ) (c : ℝ) :
    Tendsto X (vanishingProbabilityFilter μ) (𝓝 c) ↔
      ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (μ n).real {ω | ε ≤ |X ⟨n, ω⟩ - c|})
        atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    have ht := (eventually_vanishingProbabilityFilter_iff μ _).mp (h ε hε)
    simpa only [Real.dist_eq, not_lt] using ht
  · intro h ε hε
    apply (eventually_vanishingProbabilityFilter_iff μ _).mpr
    simpa only [Real.dist_eq, not_lt] using h ε hε

end HeightPaper
