module

public import HeightPaper.Probability.CorrectedCouplingProcessLaw
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Data.List.GetD

/-!
# Equality of the complete adaptive binary-process laws

Finite-prefix equality determines the law of a complete binary process.  This
closes the infinite-word part of the corrected coupling; the time-changed
genealogy and branching marginals are separate obligations.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

/-- The binary process read from the coherent adaptive finite words. -/
noncomputable def adaptiveCouplingProcess (r : List Bool → ℝ)
    (u : ℕ → ℝ) (k : ℕ) : Bool :=
  recoveryThresholdBirth (r (adaptiveCouplingWord r u k)) (u k)

theorem sourceCouplingPrefix_adaptiveCouplingProcess
    (r : List Bool → ℝ) (u : ℕ → ℝ) (k : ℕ) :
    sourceCouplingPrefix (adaptiveCouplingProcess r u) k =
      adaptiveCouplingWord r u k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sourceCouplingPrefix_succ, adaptiveCouplingWord_succ, ih]
      rfl

theorem measurable_adaptiveCouplingProcess (r : List Bool → ℝ) :
    Measurable (adaptiveCouplingProcess r) := by
  apply measurable_pi_iff.mpr
  intro k
  have hs : MeasurableSet {u : ℕ → ℝ |
      r (adaptiveCouplingWord r u k) ≤ u k} :=
    measurableSet_le
      ((measurable_of_countable r).comp (measurable_adaptiveCouplingWord r k))
      (measurable_pi_apply k)
  simpa [adaptiveCouplingProcess, recoveryThresholdBirth, decide_eq_true_eq] using
    (measurable_const.ite hs measurable_const :
      Measurable (fun u : ℕ → ℝ ↦
        if r (adaptiveCouplingWord r u k) ≤ u k then true else false))

/-- On binary path space, finite initial-word laws determine the full law. -/
theorem measure_eq_of_prefix_laws
    (μ ν : Measure (ℕ → Bool)) [IsFiniteMeasure μ]
    (h : ∀ k : ℕ,
      μ.map (fun x ↦ sourceCouplingPrefix x k) =
        ν.map (fun x ↦ sourceCouplingPrefix x k)) : μ = ν := by
  classical
  refine ext_of_generate_finite
    (measurableCylinders (fun _ : ℕ ↦ Bool))
    generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders ?_ ?_
  · intro C hC
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hC
    let k := I.sup id + 1
    let f : List Bool → (∀ i : I, Bool) :=
      fun w i ↦ w.getD i.val false
    have hf (x : ℕ → Bool) :
        f (sourceCouplingPrefix x k) = Finset.restrict I x := by
      funext i
      have hi : i.val < k := by
        have hle : i.val ≤ I.sup id := Finset.le_sup (f := id) i.property
        exact Nat.lt_succ_of_le hle
      change (sourceCouplingPrefix x k).getD i.val false = x i.val
      rw [List.getD_eq_getElem _ _ (by
        simpa only [sourceCouplingPrefix, List.length_ofFn] using hi)]
      change (List.ofFn (fun j : Fin k ↦ x j.val))[i.val]'(by
        simp only [List.length_ofFn]
        exact hi) = x i.val
      simp only [List.getElem_ofFn]
    have hmap : μ.map (Finset.restrict I) =
        ν.map (Finset.restrict I) := by
      have hm : Measurable f := measurable_of_countable f
      have heq : (Finset.restrict I : (ℕ → Bool) → (∀ i : I, Bool)) =
          f ∘ (fun x ↦ sourceCouplingPrefix x k) := by
        funext x
        exact (hf x).symm
      rw [heq, ← Measure.map_map hm (measurable_sourceCouplingPrefix k),
        ← Measure.map_map hm (measurable_sourceCouplingPrefix k), h k]
    change μ ((Finset.restrict I) ⁻¹' S) =
      ν ((Finset.restrict I) ⁻¹' S)
    have hmI : Measurable (Finset.restrict I : (ℕ → Bool) → (∀ i : I, Bool)) :=
      Measurable.of_eval (fun _ ↦ measurable_pi_apply _)
    have hmeasure := congrArg (fun ρ : Measure (∀ i : I, Bool) ↦ ρ S) hmap
    simpa only [Measure.map_apply hmI hS] using hmeasure
  · have h0 := congrArg (fun ρ : Measure (List Bool) ↦ ρ Set.univ) (h 0)
    simpa [Measure.map_apply (measurable_sourceCouplingPrefix 0)] using h0

/-- The full law of any source process with the prescribed conditional
cylinder factors equals that of the common-uniform adaptive process. -/
theorem sourceCouplingProcess_law_of_cylinder_factors
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (r : List Bool → ℝ) (hr : ∀ w, 0 ≤ r w ∧ r w ≤ 1)
    (hfactor : ∀ (k : ℕ) (w : List Bool) (b : Bool), w.length = k →
      μ {x : ℕ → Bool | sourceCouplingPrefix x (k + 1) = w ++ [b]} =
        μ {x : ℕ → Bool | sourceCouplingPrefix x k = w} *
          adaptiveStepMass (r w) b) :
    μ = uniformLaw.map (adaptiveCouplingProcess r) := by
  apply measure_eq_of_prefix_laws
  intro k
  rw [sourceCouplingPrefix_law_of_cylinder_factors μ r hr hfactor k]
  rw [Measure.map_map (measurable_sourceCouplingPrefix k)
    (measurable_adaptiveCouplingProcess r)]
  congr 1
  funext u
  exact (sourceCouplingPrefix_adaptiveCouplingProcess r u k).symm

end HeightPaper.CountCoupling
