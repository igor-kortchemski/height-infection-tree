module

public import HeightPaper.Probability.CorrectedCouplingShapeBranching

/-!
# The actual bounding families are iid geometric Bienaymé trees

The statement concerns the same terminal shapes used in the coupled
construction, now represented as genuine locally finite plane trees.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

open PlaneForward PlaneTree

noncomputable def terminalBoundTree (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) (upper : Bool)
    (w : (Fin 2 × ℕ) → ℝ) (i : Fin N) : Tree :=
  (terminalBoundShape N p q r upper w i).tree

theorem measurable_terminalBoundTree (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) (upper : Bool) :
    Measurable (terminalBoundTree N p q r upper) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_finiteShape_tree.comp
    ((measurable_pi_apply i).comp (measurable_terminalBoundShape N p q r upper))

def boundForestParameter (upper : Bool) (p q : unitInterval) : unitInterval := if upper then p else q

theorem coe_boundForestParameter (upper : Bool) (p q : unitInterval) :
    (boundForestParameter upper p q : ℝ) = boundForestRate upper p q := by cases upper <;> rfl

theorem terminalBoundTree_law_eq_pi
    (N : ℕ) (hN : 0 < N) (p q : unitInterval) (hp : 1 / 2 < (p : ℝ)) (hpq : p ≤ q)
    (r : List Bool → ℝ) (upper : Bool) :
    pairedUniformLaw.map (terminalBoundTree N p q r upper) =
      Measure.pi (fun _ : Fin N ↦ bienaymeLaw (geometricMeasure (boundForestParameter upper p q))) := by
  let F : (Fin N → FiniteShape) → Fin N → Tree := fun f i ↦ (f i).tree
  have hF : Measurable F := measurable_pi_iff.mpr
    (fun i ↦ measurable_finiteShape_tree.comp (measurable_pi_apply i))
  have hpqR : (p : ℝ) ≤ (q : ℝ) := hpq
  have ha : 1 / 2 < (boundForestParameter upper p q : ℝ) := by
    rw [coe_boundForestParameter]
    cases upper <;> dsimp [boundForestRate] <;> linarith
  change pairedUniformLaw.map (F ∘ terminalBoundShape N p q r upper) = _
  rw [← Measure.map_map hF (measurable_terminalBoundShape N p q r upper),
    terminalBoundShape_law_eq_pi N hN hp hpq q.2.2 r upper]
  have he : (Measure.pi (fun _ : Fin N ↦ oneRootShapeLaw (boundForestRate upper p q))).map F =
      Measure.pi (fun _ : Fin N ↦ oneRootPlaneLaw (boundForestRate upper p q)) :=
    Measure.pi_map_pi (fun _ ↦ measurable_finiteShape_tree.aemeasurable)
  rw [he, ← coe_boundForestParameter, oneRootPlaneLaw_eq_bienaymeLaw _ ha]

theorem terminalBoundTree_component_law
    (N : ℕ) (hN : 0 < N) (p q : unitInterval) (hp : 1 / 2 < (p : ℝ)) (hpq : p ≤ q)
    (r : List Bool → ℝ) (upper : Bool) (i : Fin N) :
    pairedUniformLaw.map (fun w ↦ terminalBoundTree N p q r upper w i) =
      bienaymeLaw (geometricMeasure (boundForestParameter upper p q)) := by
  change pairedUniformLaw.map ((fun f : Fin N → Tree ↦ f i) ∘ terminalBoundTree N p q r upper) = _
  rw [← Measure.map_map (measurable_pi_apply i) (measurable_terminalBoundTree N p q r upper),
    terminalBoundTree_law_eq_pi N hN p q hp hpq r upper, Measure.pi_map_eval]
  simp

theorem terminalBoundTree_independent
    (N : ℕ) (hN : 0 < N) (p q : unitInterval) (hp : 1 / 2 < (p : ℝ)) (hpq : p ≤ q)
    (r : List Bool → ℝ) (upper : Bool) :
    iIndepFun (fun i : Fin N ↦ fun w ↦ terminalBoundTree N p q r upper w i) pairedUniformLaw := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i ↦ ((measurable_pi_apply i).comp (measurable_terminalBoundTree N p q r upper)).aemeasurable)).mpr
  change pairedUniformLaw.map (terminalBoundTree N p q r upper) =
    Measure.pi (fun i ↦ pairedUniformLaw.map (fun w ↦ terminalBoundTree N p q r upper w i))
  rw [terminalBoundTree_law_eq_pi N hN p q hp hpq r upper]
  congr 1
  funext i
  exact (terminalBoundTree_component_law N hN p q hp hpq r upper i).symm

end HeightPaper.CountCoupling
