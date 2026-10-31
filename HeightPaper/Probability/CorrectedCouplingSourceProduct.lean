module

public import HeightPaper.Probability.CorrectedCouplingInfiniteWord
public import HeightPaper.Probability.TreeUniformCoupling

/-!
# The source word and its independent parent uniforms

The adaptive common-uniform word has the entire prescribed source law.
Giving it an independent second sequence of uniforms therefore reproduces
the joint source law used to draw the uniform-attachment forest.  This does
not yet identify that forest with the time-changed middle genealogy.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

/-- The common-uniform realization of a source word together with a fresh,
independent sequence of parent-choice uniforms. -/
noncomputable def adaptiveSourceParentLaw (r : List Bool → ℝ) :
    Measure ((ℕ → Bool) × (ℕ → ℝ)) :=
  birthParentLaw.map (Prod.map (adaptiveCouplingProcess r) id)

/-- The joint law is the product of the source process and independent parent
uniforms.  The conditional-cylinder hypothesis is the source definition of
the recovery probabilities in totalized form. -/
theorem adaptiveSourceParentLaw_eq_prod
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (r : List Bool → ℝ) (hr : ∀ w, 0 ≤ r w ∧ r w ≤ 1)
    (hfactor : ∀ (k : ℕ) (w : List Bool) (b : Bool), w.length = k →
      μ {x : ℕ → Bool | sourceCouplingPrefix x (k + 1) = w ++ [b]} =
        μ {x : ℕ → Bool | sourceCouplingPrefix x k = w} *
          adaptiveStepMass (r w) b) :
    adaptiveSourceParentLaw r = μ.prod uniformLaw := by
  rw [adaptiveSourceParentLaw, birthParentLaw]
  rw [← Measure.map_prod_map uniformLaw uniformLaw
    (measurable_adaptiveCouplingProcess r) measurable_id]
  rw [← sourceCouplingProcess_law_of_cylinder_factors μ r hr hfactor]
  simp

/-- The entire prescribed uniform-attachment trajectory, jointly with its
event word, has the source law on the common-uniform realization. -/
theorem adaptiveSourceTreeTrajectory_law
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (r : List Bool → ℝ) (hr : ∀ w, 0 ≤ r w ∧ r w ≤ 1)
    (hfactor : ∀ (k : ℕ) (w : List Bool) (b : Bool), w.length = k →
      μ {x : ℕ → Bool | sourceCouplingPrefix x (k + 1) = w ++ [b]} =
        μ {x : ℕ → Bool | sourceCouplingPrefix x k = w} *
          adaptiveStepMass (r w) b)
    (s₀ : Model.State) :
    birthParentLaw.map (fun q ↦
      (adaptiveCouplingProcess r q.1,
        Model.rankState (adaptiveCouplingProcess r q.1) s₀ q.2)) =
      (μ.prod uniformLaw).map (fun q ↦
        (q.1, Model.rankState q.1 s₀ q.2)) := by
  let F : ((ℕ → Bool) × (ℕ → ℝ)) →
      ((ℕ → Bool) × (ℕ → Model.State)) :=
    fun q ↦ (q.1, Model.rankState q.1 s₀ q.2)
  have hmF : Measurable F :=
    measurable_fst.prodMk (Model.measurable_rankTrajectory_joint s₀)
  have hmP : Measurable
      (Prod.map (adaptiveCouplingProcess r) id :
        ((ℕ → ℝ) × (ℕ → ℝ)) → ((ℕ → Bool) × (ℕ → ℝ))) :=
    (measurable_adaptiveCouplingProcess r).prodMap measurable_id
  change birthParentLaw.map (F ∘ Prod.map (adaptiveCouplingProcess r) id) =
    (μ.prod uniformLaw).map F
  rw [← Measure.map_map hmF hmP,
    ← adaptiveSourceParentLaw_eq_prod μ r hr hfactor]
  rfl

end HeightPaper.CountCoupling
