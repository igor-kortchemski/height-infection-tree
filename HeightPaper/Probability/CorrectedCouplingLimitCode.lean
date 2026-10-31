module

public import HeightPaper.Combinatorics.RootedForestEmbedding
public import HeightPaper.Probability.CorrectedCouplingMiddleLaw
public import HeightPaper.Probability.CorrectedCouplingStableRanks

/-!
# Measurable countable forest limits and their full joint source law

Vertices and parent edges are coded by countably many Boolean coordinates.
Infinite degree and infinite components are allowed. Thus the construction
also represents arbitrary source forests outside the favorable event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

abbrev ForestCode := (ℕ → Bool) × ((ℕ × ℕ) → Bool)

def forestOfCode (N : ℕ) (C : ForestCode) : RootedForest ℕ N where
  vertices := {x | C.1 x = true}
  edge := fun x y ↦ C.2 (x, y) = true
  root := Fin.val

noncomputable def trajectoryForestCode (N : ℕ) (T : ℕ → FiniteCouplingGenealogy) : ForestCode := by
  classical
  exact (fun x ↦ decide (∃ j, x ∈ (T j).1.carrier.vertices),
    fun e ↦ decide (∃ j, e.2 ∈ (T j).1.carrier.vertices ∧ e.2 ∉ Finset.range N ∧ (T j).1.parent e.2 = e.1))

noncomputable def trajectoryForest (N : ℕ) (T : ℕ → FiniteCouplingGenealogy) : RootedForest ℕ N :=
  forestOfCode N (trajectoryForestCode N T)

theorem trajectoryForest_vertex (N : ℕ) (T : ℕ → FiniteCouplingGenealogy) (x : ℕ) :
    x ∈ (trajectoryForest N T).vertices ↔ ∃ j, x ∈ (T j).1.carrier.vertices := by
  classical
  simp [trajectoryForest, forestOfCode, trajectoryForestCode]

theorem trajectoryForest_edge (N : ℕ) (T : ℕ → FiniteCouplingGenealogy) (x y : ℕ) :
    (trajectoryForest N T).edge x y ↔
      ∃ j, y ∈ (T j).1.carrier.vertices ∧ y ∉ Finset.range N ∧ (T j).1.parent y = x := by
  classical
  simp [trajectoryForest, forestOfCode, trajectoryForestCode]

theorem measurable_trajectoryForestCode (N : ℕ) : Measurable (trajectoryForestCode N) := by
  classical
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro x
    apply measurable_to_bool
    have hsets (j : ℕ) : MeasurableSet {T : ℕ → FiniteCouplingGenealogy | x ∈ (T j).1.carrier.vertices} :=
      (Set.to_countable {s : FiniteCouplingGenealogy | x ∈ s.1.carrier.vertices}).measurableSet.preimage
        (measurable_pi_apply j)
    convert MeasurableSet.iUnion hsets using 1
    ext T
    simp
  · apply measurable_pi_iff.mpr
    intro e
    apply measurable_to_bool
    have hsets (j : ℕ) : MeasurableSet {T : ℕ → FiniteCouplingGenealogy |
        e.2 ∈ (T j).1.carrier.vertices ∧ e.2 ∉ Finset.range N ∧ (T j).1.parent e.2 = e.1} :=
      (Set.to_countable {s : FiniteCouplingGenealogy |
        e.2 ∈ s.1.carrier.vertices ∧ e.2 ∉ Finset.range N ∧ s.1.parent e.2 = e.1}).measurableSet.preimage
          (measurable_pi_apply j)
    convert MeasurableSet.iUnion hsets using 1
    ext T
    simp

noncomputable def correctedMiddleLimitCode (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) : ForestCode := trajectoryForestCode N (sampledMiddleForest N p q r w)

theorem measurable_correctedMiddleLimitCode (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) :
    Measurable (correctedMiddleLimitCode N p q r) :=
  (measurable_trajectoryForestCode N).comp (measurable_sampledMiddleForest N p q r)

theorem correctedMiddleLimitCode_joint_law
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hp1 : p ≤ 1)
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (r : List Bool → ℝ) (hr : ∀ a, 0 ≤ r a ∧ r a ≤ 1)
    (hfactor : ∀ (k : ℕ) (a : List Bool) (b : Bool), a.length = k →
      μ {x | sourceCouplingPrefix x (k + 1) = a ++ [b]} =
        μ {x | sourceCouplingPrefix x k = a} * adaptiveStepMass (r a) b) :
    pairedUniformLaw.map (fun w ↦
      (correctedCouplingEmittedWord (Finset.range N) p q r w, correctedMiddleLimitCode N p q r w)) =
      (μ.prod uniformLaw).map (fun z ↦ (z.1, trajectoryForestCode N (sourceForestTrajectory N z.1 z.2))) := by
  let F : ((ℕ → Bool) × (ℕ → FiniteCouplingGenealogy)) → (ℕ → Bool) × ForestCode :=
    fun z ↦ (z.1, trajectoryForestCode N z.2)
  have hF : Measurable F := measurable_fst.prodMk ((measurable_trajectoryForestCode N).comp measurable_snd)
  have hactual : Measurable (fun w ↦
      (correctedCouplingEmittedWord (Finset.range N) p q r w, sampledMiddleForest N p q r w)) :=
    (measurable_correctedCouplingEmittedWord _ p q r).prodMk (measurable_sampledMiddleForest N p q r)
  have hsource : Measurable (fun z : (ℕ → Bool) × (ℕ → ℝ) ↦ (z.1, sourceForestTrajectory N z.1 z.2)) :=
    measurable_fst.prodMk (measurable_sourceForestTrajectory N)
  change pairedUniformLaw.map (F ∘ fun w ↦
      (correctedCouplingEmittedWord (Finset.range N) p q r w, sampledMiddleForest N p q r w)) =
    (μ.prod uniformLaw).map (F ∘ fun z ↦ (z.1, sourceForestTrajectory N z.1 z.2))
  rw [← Measure.map_map hF hactual, ← Measure.map_map hF hsource,
    correctedCouplingMiddle_source_joint_law N hN hp hpq hp1 μ r hr hfactor]

end HeightPaper.CountCoupling
