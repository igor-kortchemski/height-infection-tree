module

public import Mathlib.Probability.Independence.ZeroOne
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Simultaneous nonvanishing from a zero–one law for closed sets

A random closed set is almost surely empty if every point is almost surely
absent and hitting each member of a countable topological basis has probability
zero or one. This separates the topological step from the construction of the
independent parent choices and the proof of tail invariance.
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace

namespace HeightPaper

/-- A zero–one hit pattern makes a random closed set deterministic. Pointwise
almost-sure absence then rules out every point simultaneously. -/
theorem ae_closedSet_eq_empty_of_zero_one_hits
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [SecondCountableTopology X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (C : Ω → Set X)
    (hclosed : ∀ᵐ ω ∂μ, IsClosed (C ω))
    (hpoint : ∀ x, ∀ᵐ ω ∂μ, x ∉ C ω)
    (hmeas : ∀ U ∈ countableBasis X, NullMeasurableSet {ω | (U ∩ C ω).Nonempty} μ)
    (hzeroone : ∀ U ∈ countableBasis X,
      μ {ω | (U ∩ C ω).Nonempty} = 0 ∨ μ {ω | (U ∩ C ω).Nonempty} = 1) :
    ∀ᵐ ω ∂μ, C ω = ∅ := by
  have hpattern : ∀ᵐ ω ∂μ, ∀ U : countableBasis X,
      (U.val ∩ C ω).Nonempty ↔ μ {ω | (U.val ∩ C ω).Nonempty} = 1 := by
    apply ae_all_iff.mpr
    intro U
    rcases hzeroone U U.property with hzero | hone
    · have hnot : ∀ᵐ ω ∂μ, ¬(U.val ∩ C ω).Nonempty := by
        simpa only [ae_iff, not_not] using hzero
      filter_upwards [hnot] with ω hω
      simp only [hω, hzero, zero_ne_one]
    · have hyes : ∀ᵐ ω ∂μ, (U.val ∩ C ω).Nonempty :=
        (mem_ae_iff_prob_eq_one₀ (hmeas U U.property)).mpr hone
      filter_upwards [hyes] with ω hω
      simp only [hω, hone]
  filter_upwards [hpattern] with ω hω
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxin : ∀ᵐ ω' ∂μ, x ∈ C ω' := by
    filter_upwards [hpattern, hclosed] with ω' hω' hclosed'
    rw [← hclosed'.closure_eq, (isBasis_countableBasis X).mem_closure_iff]
    intro U hU hxU
    exact (hω' ⟨U, hU⟩).mpr ((hω ⟨U, hU⟩).mp ⟨x, hxU, hx⟩)
  have hfalse : ∀ᵐ ω' ∂μ, False := by
    filter_upwards [hxin, hpoint x] with ω' hin hout using hout hin
  exact hfalse.exists.elim (fun _ h ↦ h)

/-- Continuous random functions inherit simultaneous nonvanishing when their
zero-set hit events satisfy a zero–one law. -/
theorem ae_forall_ne_of_zero_one_zeroSet_hits
    {Ω X Y : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T1Space Y] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f : Ω → X → Y) (y : Y) (hcont : ∀ᵐ ω ∂μ, Continuous (f ω))
    (hpoint : ∀ x, ∀ᵐ ω ∂μ, f ω x ≠ y)
    (hmeas : ∀ U ∈ countableBasis X, NullMeasurableSet {ω | ∃ x ∈ U, f ω x = y} μ)
    (hzeroone : ∀ U ∈ countableBasis X,
      μ {ω | ∃ x ∈ U, f ω x = y} = 0 ∨ μ {ω | ∃ x ∈ U, f ω x = y} = 1) :
    ∀ᵐ ω ∂μ, ∀ x, f ω x ≠ y := by
  have hclosed : ∀ᵐ ω ∂μ, IsClosed {x | f ω x = y} := by
    filter_upwards [hcont] with ω hω using isClosed_singleton.preimage hω
  have hh := ae_closedSet_eq_empty_of_zero_one_hits (μ := μ) (fun ω ↦ {x | f ω x = y})
    hclosed hpoint hmeas hzeroone
  filter_upwards [hh] with ω hω
  simpa only [Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq] using hω

/-- Countable unions of zero–one events again have probability zero or one. -/
theorem measure_iUnion_eq_zero_or_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (E : ℕ → Set Ω)
    (hE : ∀ n, μ (E n) = 0 ∨ μ (E n) = 1) :
    μ (⋃ n, E n) = 0 ∨ μ (⋃ n, E n) = 1 := by
  by_cases h : ∀ n, μ (E n) = 0
  · exact Or.inl (measure_iUnion_null h)
  · push Not at h
    obtain ⟨n, hn⟩ := h
    have hone := (hE n).resolve_left hn
    exact Or.inr (le_antisymm prob_le_one (hone ▸ measure_mono (subset_iUnion E n)))

/-- In a locally compact second-countable space, compact hit events suffice:
each open set is a countable union of compact sets. Null measurability permits
identifying hit events using an almost-sure convergence theorem. -/
theorem ae_forall_ne_of_zero_one_compact_zeroSet_hits
    {Ω X Y : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [SecondCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [T1Space Y] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f : Ω → X → Y) (y : Y) (hcont : ∀ᵐ ω ∂μ, Continuous (f ω))
    (hpoint : ∀ x, ∀ᵐ ω ∂μ, f ω x ≠ y)
    (hmeas : ∀ K, IsCompact K → NullMeasurableSet {ω | ∃ x ∈ K, f ω x = y} μ)
    (hzeroone : ∀ K, IsCompact K →
      μ {ω | ∃ x ∈ K, f ω x = y} = 0 ∨ μ {ω | ∃ x ∈ K, f ω x = y} = 1) :
    ∀ᵐ ω ∂μ, ∀ x, f ω x ≠ y := by
  have hopen (U : Set X) (hU : IsOpen U) :
      NullMeasurableSet {ω | ∃ x ∈ U, f ω x = y} μ ∧
        (μ {ω | ∃ x ∈ U, f ω x = y} = 0 ∨
          μ {ω | ∃ x ∈ U, f ω x = y} = 1) := by
    let : LocallyCompactSpace U := hU.locallyCompactSpace
    have hs : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
    obtain ⟨K, hK, hKU⟩ := hs
    have heq : {ω | ∃ x ∈ U, f ω x = y} = ⋃ n, {ω | ∃ x ∈ K n, f ω x = y} := by
      rw [← hKU]
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion]
      exact ⟨fun ⟨x, ⟨n, hx⟩, hf⟩ => ⟨n, x, hx, hf⟩,
        fun ⟨n, x, hx, hf⟩ => ⟨x, ⟨n, hx⟩, hf⟩⟩
    rw [heq]
    exact ⟨NullMeasurableSet.iUnion (fun n => hmeas (K n) (hK n)),
      measure_iUnion_eq_zero_or_one _ (fun n => hzeroone (K n) (hK n))⟩
  exact ae_forall_ne_of_zero_one_zeroSet_hits f y hcont hpoint
    (fun U hU => (hopen U ((isBasis_countableBasis X).isOpen hU)).1)
    (fun U hU => (hopen U ((isBasis_countableBasis X).isOpen hU)).2)

end HeightPaper
