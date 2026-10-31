module

public import HeightPaper.Probability.CorrectedCouplingPlaneEmbedding
public import HeightPaper.Probability.CorrectedCouplingTerminalShape
public import HeightPaper.Probability.CorrectedCouplingBoundingTreeLaw
public import HeightPaper.Probability.CorrectedCouplingActiveWord

/-!
# Rooted embeddings for the actual corrected coupling

The physical shared-label inclusions are composed with explicit plane-shape
and chronological-label isomorphisms. All roots and parent edges are
preserved; the resulting embeddings are componentwise by indexed root.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

noncomputable def physicalMiddleTrajectory (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) : ℕ → FiniteCouplingGenealogy :=
  fun j ↦ (finiteCouplingStage roots p q r w j).middle

theorem physicalMiddleTrajectory_val (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) :
    (physicalMiddleTrajectory roots p q r w j).1 = (correctedCouplingStage roots p q r w j).trees.middle :=
  congrArg (fun s : CorrectedCouplingState ↦ s.trees.middle) (finiteCouplingStage_toState roots p q r w j)

theorem physicalMiddleTrajectory_chronoLE (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (i j : ℕ) (hij : i ≤ j) :
    (physicalMiddleTrajectory roots p q r w i).1.ChronoLE (physicalMiddleTrajectory roots p q r w j).1 := by
  rw [physicalMiddleTrajectory_val, physicalMiddleTrajectory_val]
  exact correctedCouplingStage_middle_chronoLE roots p q r w hij

theorem physicalMiddleTrajectory_valid (N : ℕ) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (j : ℕ) :
    (physicalMiddleTrajectory (Finset.range N) p q r w j).1.Valid (Finset.range N) := by
  rw [physicalMiddleTrajectory_val]
  exact (correctedCouplingStage_valid (Finset.range N) hpq r w j).2.1

noncomputable def physicalMiddleToSampledEmbedding
    (N : ℕ) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hu : ∀ k, ∃ j, k < correctedCouplingClock (Finset.range N) p q r w j) :
    RootedForest.Embedding (trajectoryForest N (physicalMiddleTrajectory (Finset.range N) p q r w))
      (forestOfCode N (correctedMiddleLimitCode N p q r w)) := by
  exact cofinalChronologicalEmbedding N (physicalMiddleTrajectory (Finset.range N) p q r w)
    (physicalMiddleTrajectory_chronoLE _ p q r w) (physicalMiddleTrajectory_valid N hpq r w)
    (couplingLogicalTime (Finset.range N) p q r w)
    (fun j ↦ ⟨j, couplingLogicalTime_ge (Finset.range N) p q r w hu j⟩)

noncomputable def sampledMiddleToPhysicalEmbedding
    (N : ℕ) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hu : ∀ k, ∃ j, k < correctedCouplingClock (Finset.range N) p q r w j) :
    RootedForest.Embedding (forestOfCode N (correctedMiddleLimitCode N p q r w))
      (trajectoryForest N (physicalMiddleTrajectory (Finset.range N) p q r w)) := by
  exact cofinalChronologicalInverseEmbedding N (physicalMiddleTrajectory (Finset.range N) p q r w)
    (physicalMiddleTrajectory_chronoLE _ p q r w) (physicalMiddleTrajectory_valid N hpq r w)
    (couplingLogicalTime (Finset.range N) p q r w)
    (fun j ↦ ⟨j, couplingLogicalTime_ge (Finset.range N) p q r w hu j⟩)

noncomputable def terminalBoundGenealogy (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (upper : Bool) (w : (Fin 2 × ℕ) → ℝ) : CouplingGenealogy :=
  (correctedCouplingStage (Finset.range N) p q r w
    (couplingExtinctionTime (Finset.range N) p q r w)).boundForest upper

theorem terminalBoundGenealogy_valid (N : ℕ) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ)
    (upper : Bool) (w : (Fin 2 × ℕ) → ℝ) :
    (terminalBoundGenealogy N p q r upper w).Valid (Finset.range N) := by
  have h := correctedCouplingStage_valid (Finset.range N) hpq r w
    (couplingExtinctionTime (Finset.range N) p q r w)
  cases upper
  · exact h.1
  · exact h.2.2

noncomputable def lowerTerminalToPhysicalMiddleEmbedding
    (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hu : ∀ k, ∃ j, k < correctedCouplingClock (Finset.range N) p q r w j)
    (hg : sourceCorrectedGood N p q r (correctedCouplingEmittedWord (Finset.range N) p q r w)) :
    RootedForest.Embedding (finiteGenealogyForest N (terminalBoundGenealogy N p q r false w))
      (trajectoryForest N (physicalMiddleTrajectory (Finset.range N) p q r w)) := by
  let k := couplingExtinctionTime (Finset.range N) p q r w
  have ho := (correctedCouplingStage_ordered_of_sourceGood N p q r w hu hg k).1
  apply RootedForest.Embedding.of_inclusion
  · intro x hx
    apply (trajectoryForest_vertex N _ x).mpr
    refine ⟨k, ?_⟩
    rw [physicalMiddleTrajectory_val]
    exact ho.1.1 hx
  · intro x y he
    obtain ⟨hy, hyN, hp⟩ := he
    apply (trajectoryForest_edge N _ x y).mpr
    refine ⟨k, ?_, hyN, ?_⟩
    · rw [physicalMiddleTrajectory_val]
      exact ho.1.1 hy
    · rw [physicalMiddleTrajectory_val]
      exact (ho.2 y hy).symm.trans hp
  · rfl

theorem upper_treeLE_terminal (N : ℕ) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ)
    (hex : ∃ j, (correctedCouplingStage (Finset.range N) p q r w j).trees.upper.carrier.active = ∅) (j : ℕ) :
    (correctedCouplingStage (Finset.range N) p q r w j).trees.upper.TreeLE
      (terminalBoundGenealogy N p q r true w) := by
  let k := couplingExtinctionTime (Finset.range N) p q r w
  have he := couplingExtinctionTime_spec (Finset.range N) p q r w hex
  by_cases hjk : j ≤ k
  · exact (correctedCouplingStage_treeLE_of_le (Finset.range N) hpq r w hjk).2.2
  · have heq := correctedCouplingStage_bound_eq_of_upper_empty (Finset.range N) hpq r w
      (show k ≤ j by omega) true he
    change (correctedCouplingStage (Finset.range N) p q r w j).trees.upper =
      terminalBoundGenealogy N p q r true w at heq
    rw [heq]
    exact CouplingGenealogy.treeLE_refl _

noncomputable def physicalMiddleToUpperTerminalEmbedding
    (N : ℕ) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hu : ∀ k, ∃ j, k < correctedCouplingClock (Finset.range N) p q r w j)
    (hg : sourceCorrectedGood N p q r (correctedCouplingEmittedWord (Finset.range N) p q r w))
    (hex : ∃ j, (correctedCouplingStage (Finset.range N) p q r w j).trees.upper.carrier.active = ∅) :
    RootedForest.Embedding (trajectoryForest N (physicalMiddleTrajectory (Finset.range N) p q r w))
      (finiteGenealogyForest N (terminalBoundGenealogy N p q r true w)) := by
  apply RootedForest.Embedding.of_inclusion
  · intro x hx
    obtain ⟨j, hj⟩ := (trajectoryForest_vertex N _ x).mp hx
    rw [physicalMiddleTrajectory_val] at hj
    have ho := (correctedCouplingStage_ordered_of_sourceGood N p q r w hu hg j).2
    exact (upper_treeLE_terminal N hpq r w hex j).1 (ho.1.1 hj)
  · intro x y he
    obtain ⟨j, hy, hyN, hp⟩ := (trajectoryForest_edge N _ x y).mp he
    rw [physicalMiddleTrajectory_val] at hy hp
    have ho := (correctedCouplingStage_ordered_of_sourceGood N p q r w hu hg j).2
    have hyU := ho.1.1 hy
    have hterm := upper_treeLE_terminal N hpq r w hex j
    exact ⟨hterm.1 hyU, hyN, (hterm.2 y hyU).symm.trans ((ho.2 y hy).symm.trans hp)⟩
  · rfl

noncomputable def correctedLowerEmbedding
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hu : ∀ k, ∃ j, k < correctedCouplingClock (Finset.range N) p q r w j)
    (hg : sourceCorrectedGood N p q r (correctedCouplingEmittedWord (Finset.range N) p q r w)) :
    RootedForest.Embedding (planeForest (terminalBoundTree N p q r false w))
      (forestOfCode N (correctedMiddleLimitCode N p q r w)) :=
  ((genealogyPlaneInverseEmbedding N hN (terminalBoundGenealogy N p q r false w)
      (terminalBoundGenealogy_valid N hpq r false w)).trans
    (lowerTerminalToPhysicalMiddleEmbedding N p q r w hu hg)).trans
      (physicalMiddleToSampledEmbedding N hpq r w hu)

noncomputable def correctedUpperEmbedding
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hu : ∀ k, ∃ j, k < correctedCouplingClock (Finset.range N) p q r w j)
    (hg : sourceCorrectedGood N p q r (correctedCouplingEmittedWord (Finset.range N) p q r w))
    (hex : ∃ j, (correctedCouplingStage (Finset.range N) p q r w j).trees.upper.carrier.active = ∅) :
    RootedForest.Embedding (forestOfCode N (correctedMiddleLimitCode N p q r w))
      (planeForest (terminalBoundTree N p q r true w)) :=
  ((sampledMiddleToPhysicalEmbedding N hpq r w hu).trans
    (physicalMiddleToUpperTerminalEmbedding N hpq r w hu hg hex)).trans
      (genealogyPlaneEmbedding N hN (terminalBoundGenealogy N p q r true w)
        (terminalBoundGenealogy_valid N hpq r true w))

theorem correctedCoupling_rooted_sandwich_ae
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hq1 : q ≤ 1)
    (r : List Bool → ℝ) :
    ∀ᵐ w ∂pairedUniformLaw, sourceCorrectedGood N p q r
      (correctedCouplingEmittedWord (Finset.range N) p q r w) →
      Nonempty (RootedForest.Embedding (planeForest (terminalBoundTree N p q r false w))
        (forestOfCode N (correctedMiddleLimitCode N p q r w))) ∧
      Nonempty (RootedForest.Embedding (forestOfCode N (correctedMiddleLimitCode N p q r w))
        (planeForest (terminalBoundTree N p q r true w))) := by
  have hp1 : p ≤ 1 := hpq.trans hq1
  filter_upwards [correctedCouplingClock_ae_unbounded N hN hp hp1 q r,
    correctedCouplingStage_upper_ae_eventually_empty N hN hp hp1 q r] with w hu he
  intro hg
  exact ⟨⟨correctedLowerEmbedding N hN hpq r w hu hg⟩,
    ⟨correctedUpperEmbedding N hN hpq r w hu hg he⟩⟩

end HeightPaper.CountCoupling
