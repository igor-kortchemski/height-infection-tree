module

public import HeightPaper.Probability.CorrectedCouplingTerminalShape

/-!
# Exact masses of both terminal ordered forests

Constant expectation and bounded convergence identify the probability of
every complete finite forest. The lower forest uses the same upper-clock
extinction time, with no unproved lower-parent marginal law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace HeightPaper.CountCoupling

theorem measurable_boundForestPotential (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (t : Fin N → PlaneForward.FiniteShape) (a : ℝ) (upper : Bool) (j : ℕ) :
    Measurable (fun w ↦ forestCompletionPotential N t a
      ((correctedCouplingStage (Finset.range N) p q r w j).boundForest upper)) := by
  have hf : Measurable (fun s : FiniteCouplingState ↦
      forestCompletionPotential N t a (s.toState.boundForest upper)) := measurable_of_countable _
  have hm := hf.comp (measurable_finiteCouplingStage (Finset.range N) p q r j)
  simpa only [Function.comp_def, finiteCouplingStage_toState] using hm

theorem forestCompletionPotential_integral
    (N : ℕ) {p q : ℝ} (hpq : p ≤ q) (hp0 : 0 ≤ p) (hq1 : q ≤ 1)
    (r : List Bool → ℝ) (t : Fin N → PlaneForward.FiniteShape) (upper : Bool) (j : ℕ) :
    (∫ w, forestCompletionPotential N t (boundForestRate upper p q)
      ((correctedCouplingStage (Finset.range N) p q r w j).boundForest upper) ∂pairedUniformLaw) =
        ∏ i, (boundForestRate upper p q) ^ (t i).size *
          (1 - boundForestRate upper p q) ^ ((t i).size - 1) := by
  induction j with
  | zero =>
      have he (w : (Fin 2 × ℕ) → ℝ) :
          (correctedCouplingStage (Finset.range N) p q r w 0).boundForest upper =
            CouplingGenealogy.initial (Finset.range N) := by cases upper <;> rfl
      simp [he, forestCompletionPotential_initial, integral_const]
  | succ j ih => rw [forestCompletionPotential_integral_succ N hpq hp0 hq1 r t upper j, ih]

theorem terminalBoundShape_real_mass
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hq1 : q ≤ 1)
    (r : List Bool → ℝ) (t : Fin N → PlaneForward.FiniteShape) (upper : Bool) :
    pairedUniformLaw.real {w | terminalBoundShape N p q r upper w = t} =
      ∏ i, (boundForestRate upper p q) ^ (t i).size *
        (1 - boundForestRate upper p q) ^ ((t i).size - 1) := by
  classical
  let a := boundForestRate upper p q
  have hp0 : 0 ≤ p := by linarith
  have hp1 : p ≤ 1 := hpq.trans hq1
  have ha0 : 0 ≤ a := by cases upper <;> dsimp [a, boundForestRate] <;> linarith
  have ha1 : a ≤ 1 := by cases upper <;> dsimp [a, boundForestRate] <;> linarith
  let F : ℕ → ((Fin 2 × ℕ) → ℝ) → ℝ := fun j w ↦ forestCompletionPotential N t a
    ((correctedCouplingStage (Finset.range N) p q r w j).boundForest upper)
  let G : ((Fin 2 × ℕ) → ℝ) → ℝ := fun w ↦ if terminalBoundShape N p q r upper w = t then 1 else 0
  have hlim : ∀ᵐ w ∂pairedUniformLaw, Tendsto (fun j ↦ F j w) atTop (𝓝 (G w)) := by
    filter_upwards [correctedCouplingStage_upper_ae_eventually_empty N hN hp hp1 q r] with w hw
    have he := forestCompletionPotential_eventually_terminal N hpq r t a upper w hw
    have heq : (fun j ↦ F j w) =ᶠ[atTop] (fun _ ↦ G w) := he
    exact tendsto_const_nhds.congr' heq.symm
  have hDCT := tendsto_integral_of_dominated_convergence (μ := pairedUniformLaw)
    (F := F) (f := G) (fun _ ↦ (1 : ℝ))
    (fun j ↦ (measurable_boundForestPotential N p q r t a upper j).aestronglyMeasurable)
    (integrable_const _) (fun j ↦ ?_) hlim
  · have hconst : Tendsto (fun j ↦ ∫ w, F j w ∂pairedUniformLaw) atTop
        (𝓝 (∏ i, a ^ (t i).size * (1 - a) ^ ((t i).size - 1))) := by
      simpa only [F, a, forestCompletionPotential_integral N hpq hp0 hq1 r t upper] using
        (tendsto_const_nhds : Tendsto
          (fun _ : ℕ ↦ ∏ i, a ^ (t i).size * (1 - a) ^ ((t i).size - 1)) atTop (𝓝 _))
    have heq := tendsto_nhds_unique hDCT hconst
    have hA : MeasurableSet {w | terminalBoundShape N p q r upper w = t} := by
      convert (measurable_terminalBoundShape N p q r upper) (measurableSet_singleton t) using 1
      ext w
      simp
    have hG : G = Set.indicator {w | terminalBoundShape N p q r upper w = t} (fun _ ↦ (1 : ℝ)) := by
      funext w
      simp [G, Set.indicator]
    rw [hG, integral_indicator_const _ hA] at heq
    simpa only [smul_eq_mul, mul_one, a] using heq
  · apply ae_of_all
    intro w
    change ‖forestCompletionPotential N t a
      ((correctedCouplingStage (Finset.range N) p q r w j).boundForest upper)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (forestCompletionPotential_nonneg N t ha0 ha1 _)]
    exact forestCompletionPotential_le_one N t ha0 ha1 _

theorem terminalBoundShape_mass
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hq1 : q ≤ 1)
    (r : List Bool → ℝ) (t : Fin N → PlaneForward.FiniteShape) (upper : Bool) :
    pairedUniformLaw {w | terminalBoundShape N p q r upper w = t} =
      ENNReal.ofReal (∏ i, (boundForestRate upper p q) ^ (t i).size *
        (1 - boundForestRate upper p q) ^ ((t i).size - 1)) := by
  rw [← ofReal_measureReal (measure_ne_top pairedUniformLaw _),
    terminalBoundShape_real_mass N hN hp hpq hq1 r t upper]

end HeightPaper.CountCoupling
