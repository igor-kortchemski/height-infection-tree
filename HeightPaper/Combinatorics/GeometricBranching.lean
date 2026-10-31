module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.ConditionalProbability

/-!
Adapted from the generic Bienaymé-law utilities in the sibling `freezing1`
project, using the same pinned Lean and Mathlib 4.35.0.

# Geometric branching from the first-child decomposition

This finite-dimensional argument is independent of a particular encoding
of plane trees. The structural interface records the actual first-child
operation: grafting adds the first child and shifts the old children by one.
A measure fixed point then gives every offspring mass and the joint law of
its finitely many children, without division by zero-probability events.
-/

@[expose] public section

namespace HeightPaper

open MeasureTheory
open scoped ENNReal BigOperators Classical

/-- Structural identities of the plane first-child / remaining-children
 decomposition. Children are numbered from zero in this interface. -/
structure FirstChildStructure (T : Type*) [MeasurableSpace T] where
  leaf : T
  degree : T → ℕ
  child : T → ℕ → T
  graft : T × T → T
  measurable_degree : Measurable degree
  measurable_child : ∀ i, Measurable (fun t => child t i)
  measurable_graft : Measurable graft
  degree_leaf : degree leaf = 0
  degree_graft : ∀ a b, degree (graft (a, b)) = degree b + 1
  child_graft_zero : ∀ a b, child (graft (a, b)) 0 = a
  child_graft_succ : ∀ a b i, child (graft (a, b)) (i + 1) = child b i

namespace FirstChildStructure

variable {T : Type*} [MeasurableSpace T]

/-- Exact offspring count together with a rectangle for all its children. -/
def childrenEvent (D : FirstChildStructure T) (k : ℕ) (E : Fin k → Set T) : Set T :=
  {t | D.degree t = k ∧ ∀ i : Fin k, D.child t i.val ∈ E i}

theorem measurableSet_childrenEvent (D : FirstChildStructure T) (k : ℕ)
    (E : Fin k → Set T) (hE : ∀ i, MeasurableSet (E i)) :
    MeasurableSet (D.childrenEvent k E) := by
  apply MeasurableSet.inter
  · exact D.measurable_degree (measurableSet_singleton k)
  · have he : {t | ∀ i : Fin k, D.child t i.val ∈ E i} =
        ⋂ i : Fin k, (fun t => D.child t i.val) ⁻¹' E i := by
      ext t
      simp
    change MeasurableSet {t | ∀ i : Fin k, D.child t i.val ∈ E i}
    rw [he]
    exact MeasurableSet.iInter (fun i => (hE i).preimage (D.measurable_child i.val))

theorem graft_preimage_childrenEvent_succ (D : FirstChildStructure T) (k : ℕ)
    (E : Fin (k + 1) → Set T) :
    D.graft ⁻¹' D.childrenEvent (k + 1) E =
      E 0 ×ˢ D.childrenEvent k (fun i => E i.succ) := by
  ext ab
  rcases ab with ⟨a, b⟩
  simp only [Set.mem_preimage, childrenEvent, Set.mem_ofPred_eq,
    D.degree_graft, Nat.add_right_cancel_iff, Fin.forall_fin_succ,
    Fin.val_zero, D.child_graft_zero, Fin.val_succ, D.child_graft_succ,
    Set.mem_prod]
  tauto

/-- The exact finite-dimensional branching factorization. The two weights
are arbitrary; later applications take `q = 1-p` and `r = p`. -/
theorem childrenEvent_measure_of_fixedPoint (D : FirstChildStructure T)
    (μ : Measure T) [IsProbabilityMeasure μ] (q r : ℝ≥0∞)
    (hμ : μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft)
    (k : ℕ) (E : Fin k → Set T) (hE : ∀ i, MeasurableSet (E i)) :
    μ (D.childrenEvent k E) = q * r ^ k * ∏ i : Fin k, μ (E i) := by
  induction k with
  | zero =>
      have hleaf : D.leaf ∈ D.childrenEvent 0 E := by
        simp [childrenEvent, D.degree_leaf]
      have hpre : D.graft ⁻¹' D.childrenEvent 0 E = ∅ := by
        ext ab
        simp [childrenEvent, D.degree_graft]
      conv_lhs => rw [hμ]
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        Measure.dirac_apply' _ (D.measurableSet_childrenEvent 0 E hE),
        Set.indicator_of_mem hleaf, Pi.one_apply,
        Measure.map_apply D.measurable_graft (D.measurableSet_childrenEvent 0 E hE), hpre]
      simp
  | succ k ih =>
      have hleaf : D.leaf ∉ D.childrenEvent (k + 1) E := by
        simp [childrenEvent, D.degree_leaf]
      conv_lhs => rw [hμ]
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        Measure.dirac_apply' _ (D.measurableSet_childrenEvent (k + 1) E hE),
        Set.indicator_of_notMem hleaf,
        Measure.map_apply D.measurable_graft (D.measurableSet_childrenEvent (k + 1) E hE),
        D.graft_preimage_childrenEvent_succ, Measure.prod_prod]
      simp only [smul_eq_mul, mul_zero, zero_add]
      rw [ih (fun i => E i.succ) (fun i => hE i.succ), pow_succ, Fin.prod_univ_succ]
      ring

theorem degree_measure_of_fixedPoint (D : FirstChildStructure T)
    (μ : Measure T) [IsProbabilityMeasure μ] (q r : ℝ≥0∞)
    (hμ : μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft) (k : ℕ) :
    μ {t | D.degree t = k} = q * r ^ k := by
  simpa [childrenEvent] using
    D.childrenEvent_measure_of_fixedPoint μ q r hμ k (fun _ => Set.univ)
      (fun _ => MeasurableSet.univ)

/-- Conditional on any offspring count with positive probability, the
entire finite family of child trees has exactly the product law. -/
theorem conditional_childrenLaw_of_fixedPoint (D : FirstChildStructure T)
    (μ : Measure T) [IsProbabilityMeasure μ] (q r : ℝ≥0∞)
    (hμ : μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft)
    (k : ℕ) (hk : μ {t | D.degree t = k} ≠ 0) :
    (ProbabilityTheory.cond μ {t | D.degree t = k}).map
        (fun t (i : Fin k) => D.child t i.val) = Measure.pi (fun _ : Fin k => μ) := by
  symm
  apply Measure.pi_eq
  intro E hE
  have hdeg : MeasurableSet {t | D.degree t = k} :=
    D.measurable_degree (measurableSet_singleton k)
  rw [Measure.map_apply (Measurable.of_eval fun i => D.measurable_child i.val)
    (MeasurableSet.univ_pi hE), ProbabilityTheory.cond_apply hdeg]
  have he : {t | D.degree t = k} ∩
      (fun t (i : Fin k) => D.child t i.val) ⁻¹' Set.pi Set.univ E =
      D.childrenEvent k E := by
    ext t
    simp [childrenEvent]
  rw [he, D.childrenEvent_measure_of_fixedPoint μ q r hμ k E hE,
    ← D.degree_measure_of_fixedPoint μ q r hμ k, ← mul_assoc,
    ENNReal.inv_mul_cancel hk (measure_ne_top _ _), one_mul]

end FirstChildStructure
end HeightPaper
