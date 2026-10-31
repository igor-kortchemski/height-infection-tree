module

public import HeightPaper.Probability.FiniteTreeCouplingLaw
public import HeightPaper.Probability.EarlyBranchJointLaw
public import HeightPaper.Probability.EventWordAveraging
public import HeightPaper.Model.CoupledPrescribedWalk
public import HeightPaper.Probability.FiniteEventMeasurable

/-!
# The positive finite event word on the original epidemic path

Before extinction, the binary birth word used by the two-uniform coupling is
read exactly from the active-count increments of the original tree history.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

/-- The active path in the coupled construction belongs to the cylinder of
its own birth word. -/
theorem coupledTreeHistory_mem_eventCylinder_of_survival
    (l : ℝ) (n H : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ))
    (hs : q.1 ∈ finiteSurvival l n H) :
    coupledTreeHistory l n H q ∈ eventCylinder (finiteBirth l n q.1) 1 H := by
  intro k hk
  have hwalk : ∀ j ≤ H, 0 < finiteWalk l n q.1 j := hs
  have heval : (coupledTreeHistory l n H q).eval k = coupledTreeState l n q k := by
    simp only [coupledTreeHistory, coupledTreeState, rankHistory,
      trajectoryPrefix_eval H _ k hk]
  have hc := counts_coupledTreeState l n q k
  have hcount : infectious (coupledTreeState l n q k) =
      (absorbedCounts l n q.1 k).2 := by
    simpa only [counts] using congrArg Prod.snd hc
  have habs := (absorbedCounts_eq_before_hit l n q.1 k
    (fun j hj ↦ hwalk j (hj.le.trans hk))).2
  have hpres := prescribedWalk_finite_cast hwalk hk
  rw [heval, hcount]
  omega

/-- On survival, every observed birth bit is the corresponding coupled bit. -/
theorem coupledTreeHistory_observedEventWord_of_survival
    (l : ℝ) (n H : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ))
    (hs : q.1 ∈ finiteSurvival l n H) :
    observedEventWord (coupledTreeHistory l n H q) =
      fun i : Fin H ↦ finiteBirth l n q.1 i := by
  let events := finiteBirth l n q.1
  have hcyl := coupledTreeHistory_mem_eventCylinder_of_survival l n H q hs
  have hpos : ∀ k ≤ H, 0 < prescribedWalk events 1 k :=
    fun k hk ↦ prescribedWalk_finite_pos hs hk
  funext i
  exact observedBirth_eq_of_eventCylinder hcyl hpos i.isLt

/-- Every finite-word event jointly with survival has exactly the same
probability under the birth-uniform coupling and the original epidemic path
law. This includes arbitrary subsets of the finite binary words. -/
theorem finiteSurvival_eventWord_probability_eq_pathMeasure
    (l : ℝ≥0) (n H : ℕ) (G : (Fin H → Bool) → Prop) :
    uniformLaw.real {u | u ∈ finiteSurvival l n H ∧
      G (fun i : Fin H ↦ finiteBirth l n u i)} =
    (pathMeasure (l / n) n H).real {p | p.last.active.Nonempty ∧
      G (observedEventWord p)} := by
  let E : Set (ℕ → ℝ) := {u | u ∈ finiteSurvival l n H ∧
    G (fun i : Fin H ↦ finiteBirth l n u i)}
  let B : Set (FinitePath H) := {p | p.last.active.Nonempty ∧
    G (observedEventWord p)}
  have hE : MeasurableSet E := by
    apply measurableSet_of_finiteBirth_prefix l n H
    intro u v he
    have hsurv : u ∈ finiteSurvival l n H ↔ v ∈ finiteSurvival l n H := by
      unfold finiteSurvival
      simp only [mem_ofPred_eq]
      constructor <;> intro hs i hi
      · rw [← finiteWalk_congr_birth_prefix he hi]
        exact hs i hi
      · rw [finiteWalk_congr_birth_prefix he hi]
        exact hs i hi
    have hcode : (fun i : Fin H ↦ finiteBirth l n u i) =
        (fun i : Fin H ↦ finiteBirth l n v i) := by
      funext i
      exact he i i.isLt
    simp only [E, mem_ofPred_eq, hsurv, hcode]
  have hB : MeasurableSet B := Set.to_countable B |>.measurableSet
  have hpre : (coupledTreeHistory l n H) ⁻¹' B =
      {q : (ℕ → ℝ) × (ℕ → ℝ) | q.1 ∈ E} := by
    ext q
    have hactive : (coupledTreeHistory l n H q).last.active.Nonempty ↔
        q.1 ∈ finiteSurvival l n H := by
      rw [finiteSurvival_iff_coupledTreeHistory_active]
      exact (Finset.card_pos).symm
    constructor
    · rintro ⟨ha, hg⟩
      exact ⟨hactive.mp ha,
        (coupledTreeHistory_observedEventWord_of_survival l n H q
          (hactive.mp ha)) ▸ hg⟩
    · rintro ⟨hs, hg⟩
      exact ⟨hactive.mpr hs,
        (coupledTreeHistory_observedEventWord_of_survival l n H q hs).symm ▸ hg⟩
  have hprob : birthParentLaw {q : (ℕ → ℝ) × (ℕ → ℝ) | q.1 ∈ E} =
      pathMeasure (l / n) n H B := by
    rw [← coupledTreeHistory_law l n H,
      Measure.map_apply (measurable_coupledTreeHistory l n H) hB, hpre]
  have hfst : birthParentLaw {q : (ℕ → ℝ) × (ℕ → ℝ) | q.1 ∈ E} =
      uniformLaw E := by
    change birthParentLaw (Prod.fst ⁻¹' E) = uniformLaw E
    rw [← birthParentLaw_map_fst, Measure.map_apply measurable_fst hE]
  change uniformLaw.real E = (pathMeasure (l / n) n H).real B
  rw [measureReal_def, measureReal_def, ← hfst, hprob]

/-- A birth-uniform event determined by the finite binary prefix transfers to
the original epidemic path, with the word read from active-count increments.
The existential representative is harmless by the prefix-invariance premise. -/
theorem finiteSurvival_prefixEvent_probability_eq_pathMeasure
    (l : ℝ≥0) (n H : ℕ) (Bad : (ℕ → ℝ) → Prop)
    (hBad : ∀ u v, (∀ i < H, finiteBirth l n u i = finiteBirth l n v i) →
      (Bad u ↔ Bad v)) :
    uniformLaw.real {u | u ∈ finiteSurvival l n H ∧ Bad u} =
    (pathMeasure (l / n) n H).real
      {p | p.last.active.Nonempty ∧ ∃ u : ℕ → ℝ,
        (fun i : Fin H ↦ finiteBirth l n u i) = observedEventWord p ∧ Bad u} := by
  let G : (Fin H → Bool) → Prop := fun w ↦
    ∃ u : ℕ → ℝ, (fun i : Fin H ↦ finiteBirth l n u i) = w ∧ Bad u
  have hpoint (u : ℕ → ℝ) :
      G (fun i : Fin H ↦ finiteBirth l n u i) ↔ Bad u := by
    constructor
    · rintro ⟨v, hv, hbad⟩
      exact (hBad v u (fun i hi ↦ congrFun hv ⟨i, hi⟩)).mp hbad
    · intro hu
      exact ⟨u, rfl, hu⟩
  simpa only [G, hpoint] using
    finiteSurvival_eventWord_probability_eq_pathMeasure l n H G

end HeightPaper.CountCoupling
