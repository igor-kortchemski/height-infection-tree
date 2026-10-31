module

public import HeightPaper.Probability.CorrectedCouplingTerminalMass

/-!
# Full product law of the finite bounding component shapes

The one-root law is normalized by the actual terminating construction.
The whole-forest atom formula then proves the product law for arbitrary N.
Its geometric Bienaymé branching characterization is a separate theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace HeightPaper.CountCoupling

noncomputable def oneRootShapeLaw (a : ℝ) : Measure PlaneForward.FiniteShape :=
  pairedUniformLaw.map (fun w ↦ terminalBoundShape 1 a a (fun _ ↦ a) true w 0)

theorem measurable_oneRootShape (a : ℝ) :
    Measurable (fun w ↦ terminalBoundShape 1 a a (fun _ ↦ a) true w 0) :=
  (measurable_pi_apply (0 : Fin 1)).comp (measurable_terminalBoundShape 1 a a (fun _ ↦ a) true)

instance (a : ℝ) : IsProbabilityMeasure (oneRootShapeLaw a) := by
  unfold oneRootShapeLaw
  infer_instance

theorem oneRootShapeLaw_atom {a : ℝ} (ha : 1 / 2 < a) (ha1 : a ≤ 1) (t : PlaneForward.FiniteShape) :
    oneRootShapeLaw a {t} = ENNReal.ofReal (a ^ t.size * (1 - a) ^ (t.size - 1)) := by
  rw [oneRootShapeLaw, Measure.map_apply (measurable_oneRootShape a) (measurableSet_singleton t)]
  have he : (fun w ↦ terminalBoundShape 1 a a (fun _ ↦ a) true w 0) ⁻¹' {t} =
      {w | terminalBoundShape 1 a a (fun _ ↦ a) true w = fun _ ↦ t} := by
    ext w
    change (terminalBoundShape 1 a a (fun _ ↦ a) true w 0 = t) ↔ _
    constructor
    · intro ht
      funext i
      have hi : i = 0 := Fin.eq_zero i
      simpa only [hi] using ht
    · intro ht
      exact congrFun ht 0
  rw [he, terminalBoundShape_mass 1 (by norm_num) ha le_rfl ha1]
  simp only [boundForestRate, ↓reduceIte, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]

theorem terminalBoundShape_law_eq_pi
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hq1 : q ≤ 1)
    (r : List Bool → ℝ) (upper : Bool) :
    pairedUniformLaw.map (terminalBoundShape N p q r upper) =
      Measure.pi (fun _ : Fin N ↦ oneRootShapeLaw (boundForestRate upper p q)) := by
  have ha : 1 / 2 < boundForestRate upper p q := by cases upper <;> dsimp [boundForestRate] <;> linarith
  have ha1 : boundForestRate upper p q ≤ 1 := by cases upper <;> dsimp [boundForestRate] <;> linarith
  apply Measure.ext_of_singleton
  intro t
  rw [Measure.map_apply (measurable_terminalBoundShape N p q r upper) (measurableSet_singleton t),
    Measure.pi_singleton]
  change pairedUniformLaw {w | terminalBoundShape N p q r upper w = t} = _
  rw [terminalBoundShape_mass N hN hp hpq hq1 r t upper]
  simp_rw [oneRootShapeLaw_atom ha ha1]
  rw [ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (sub_nonneg.mpr ha1) _)

theorem terminalBoundShape_component_law
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hq1 : q ≤ 1)
    (r : List Bool → ℝ) (upper : Bool) (i : Fin N) :
    pairedUniformLaw.map (fun w ↦ terminalBoundShape N p q r upper w i) =
      oneRootShapeLaw (boundForestRate upper p q) := by
  change pairedUniformLaw.map ((fun f : Fin N → PlaneForward.FiniteShape ↦ f i) ∘
    terminalBoundShape N p q r upper) = _
  rw [← Measure.map_map (measurable_pi_apply i) (measurable_terminalBoundShape N p q r upper),
    terminalBoundShape_law_eq_pi N hN hp hpq hq1 r upper, Measure.pi_map_eval]
  simp

theorem terminalBoundShape_independent
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hq1 : q ≤ 1)
    (r : List Bool → ℝ) (upper : Bool) :
    iIndepFun (fun i : Fin N ↦ fun w ↦ terminalBoundShape N p q r upper w i) pairedUniformLaw := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i ↦ ((measurable_pi_apply i).comp (measurable_terminalBoundShape N p q r upper)).aemeasurable)).mpr
  change pairedUniformLaw.map (terminalBoundShape N p q r upper) =
    Measure.pi (fun i ↦ pairedUniformLaw.map (fun w ↦ terminalBoundShape N p q r upper w i))
  rw [terminalBoundShape_law_eq_pi N hN hp hpq hq1 r upper]
  congr 1
  funext i
  exact (terminalBoundShape_component_law N hN hp hpq hq1 r upper i).symm

end HeightPaper.CountCoupling
