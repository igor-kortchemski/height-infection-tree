module

public import HeightPaper.Probability.CorrectedCouplingActiveWord

/-!
# Component limits of the concrete corrected coupling

The pathwise sandwich is proved for the source good event on the actual
emitted word. This does not assert the unproved middle joint law or the
Bienaymé laws of the two bounding families.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

def genealogyComponentVertices (G : ℕ → CouplingGenealogy) (roots : Finset ℕ)
    (root : ℕ) : Set ℕ := {x | ∃ j, x ∈ (G j).component roots root}

def genealogyComponentEdges (G : ℕ → CouplingGenealogy) (roots : Finset ℕ)
    (root : ℕ) : Set (ℕ × ℕ) :=
  {e | e.2 ∉ roots ∧ ∃ j, e.2 ∈ (G j).component roots root ∧ (G j).parent e.2 = e.1}

theorem genealogyComponentLimits_mono
    (a b : ℕ → CouplingGenealogy) (roots : Finset ℕ)
    (hle : ∀ j, (a j).LE (b j)) (hvalid : ∀ j, (a j).Valid roots) (root : ℕ) :
    genealogyComponentVertices a roots root ⊆ genealogyComponentVertices b roots root ∧
      genealogyComponentEdges a roots root ⊆ genealogyComponentEdges b roots root := by
  constructor
  · rintro x ⟨j, hx⟩
    exact ⟨j, CouplingGenealogy.component_subset_of_LE (hle j) (hvalid j) root hx⟩
  · rintro e ⟨hr, j, hx, hp⟩
    exact ⟨hr, j, CouplingGenealogy.component_subset_of_LE (hle j) (hvalid j) root hx,
      ((hle j).2 e.2 (Finset.mem_filter.mp hx).1).symm.trans hp⟩

theorem correctedCoupling_limit_lower_upper
    (roots : Finset ℕ) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (root : ℕ) :
    genealogyComponentVertices (fun j ↦ (correctedCouplingStage roots p q r w j).trees.lower) roots root ⊆
      genealogyComponentVertices (fun j ↦ (correctedCouplingStage roots p q r w j).trees.upper) roots root ∧
    genealogyComponentEdges (fun j ↦ (correctedCouplingStage roots p q r w j).trees.lower) roots root ⊆
      genealogyComponentEdges (fun j ↦ (correctedCouplingStage roots p q r w j).trees.upper) roots root :=
  genealogyComponentLimits_mono _ _ roots
    (correctedCouplingStage_lower_upper roots hpq r w)
    (fun j ↦ (correctedCouplingStage_valid roots hpq r w j).1) root

theorem correctedCoupling_limit_sandwich_of_sourceGood
    (N : ℕ) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ k, ∃ j, k < correctedCouplingClock (Finset.range N) p q r w j)
    (hgood : sourceCorrectedGood N p q r
      (correctedCouplingEmittedWord (Finset.range N) p q r w)) (root : ℕ) :
    let G := fun j ↦ (correctedCouplingStage (Finset.range N) p q r w j).trees
    (genealogyComponentVertices (fun j ↦ (G j).lower) (Finset.range N) root ⊆
      genealogyComponentVertices (fun j ↦ (G j).middle) (Finset.range N) root ∧
    genealogyComponentEdges (fun j ↦ (G j).lower) (Finset.range N) root ⊆
      genealogyComponentEdges (fun j ↦ (G j).middle) (Finset.range N) root) ∧
    (genealogyComponentVertices (fun j ↦ (G j).middle) (Finset.range N) root ⊆
      genealogyComponentVertices (fun j ↦ (G j).upper) (Finset.range N) root ∧
    genealogyComponentEdges (fun j ↦ (G j).middle) (Finset.range N) root ⊆
      genealogyComponentEdges (fun j ↦ (G j).upper) (Finset.range N) root) := by
  have ho := correctedCouplingStage_ordered_of_sourceGood N p q r w hunbounded hgood
  exact ⟨genealogyComponentLimits_mono _ _ _ (fun j ↦ (ho j).1)
      (fun j ↦ (correctedCouplingStage_valid _ hpq r w j).1) root,
    genealogyComponentLimits_mono _ _ _ (fun j ↦ (ho j).2)
      (fun j ↦ (correctedCouplingStage_valid _ hpq r w j).2.1) root⟩

theorem correctedCouplingStage_upper_eq_of_empty
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    {i j : ℕ} (hij : i ≤ j)
    (hi : (correctedCouplingStage roots p q r w i).trees.upper.carrier.active = ∅) :
    (correctedCouplingStage roots p q r w j).trees.upper =
      (correctedCouplingStage roots p q r w i).trees.upper := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j _ ih =>
      change ((correctedCouplingStage roots p q r w j).step p q r
        (w (0, j)) (w (1, j))).trees.upper = _
      rw [CorrectedCouplingState.step_upper]
      simp [ih, hi]

/-- Both bounding component vertex sets are finite almost surely, even off
the source good event. Their geometric branching laws are not asserted here. -/
theorem correctedCoupling_components_ae_finite
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (hpq : p ≤ q) (r : List Bool → ℝ) :
    ∀ᵐ w ∂pairedUniformLaw, ∀ root,
      (genealogyComponentVertices
        (fun j ↦ (correctedCouplingStage (Finset.range N) p q r w j).trees.lower)
        (Finset.range N) root).Finite ∧
      (genealogyComponentVertices
        (fun j ↦ (correctedCouplingStage (Finset.range N) p q r w j).trees.upper)
        (Finset.range N) root).Finite := by
  filter_upwards [correctedCouplingStage_upper_ae_eventually_empty N hN hp hp1 q r] with w hw
  obtain ⟨i, hi⟩ := hw
  have hsub (root : ℕ) : genealogyComponentVertices
      (fun j ↦ (correctedCouplingStage (Finset.range N) p q r w j).trees.upper)
      (Finset.range N) root ⊆
      ((correctedCouplingStage (Finset.range N) p q r w i).trees.upper.carrier.vertices : Set ℕ) := by
    rintro x ⟨j, hx⟩
    have hv := (Finset.mem_filter.mp hx).1
    by_cases hj : j ≤ i
    · exact (correctedCouplingStage_treeLE_of_le _ hpq r w hj).2.2.1 hv
    · have heq := correctedCouplingStage_upper_eq_of_empty _ p q r w (le_of_not_ge hj) hi
      change x ∈ (correctedCouplingStage (Finset.range N) p q r w j).trees.upper.carrier.vertices at hv
      rwa [heq] at hv
  intro root
  have hupper := (correctedCouplingStage (Finset.range N) p q r w i).trees.upper.carrier.vertices.finite_toSet.subset
    (hsub root)
  exact ⟨hupper.subset (correctedCoupling_limit_lower_upper _ hpq r w root).1, hupper⟩

end HeightPaper.CountCoupling
