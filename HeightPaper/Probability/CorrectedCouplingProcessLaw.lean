module

public import HeightPaper.Probability.CorrectedCouplingCylinder

/-!
# Uniqueness of the adaptive word law from conditional cylinder factors

A binary process whose finite cylinders have the same conditional recovery
factors as the common-uniform construction has the same finite-word laws.
The hypothesis is the elementary cylinder form of the paper's conditional
probability definition, including zero-mass prefixes after totalization.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

def sourceCouplingPrefix (x : ℕ → Bool) (k : ℕ) : List Bool :=
  List.ofFn (fun i : Fin k ↦ x i)

@[simp] theorem sourceCouplingPrefix_zero (x : ℕ → Bool) :
    sourceCouplingPrefix x 0 = [] := by simp [sourceCouplingPrefix]

theorem sourceCouplingPrefix_length (x : ℕ → Bool) (k : ℕ) :
    (sourceCouplingPrefix x k).length = k := by
  simp [sourceCouplingPrefix]

theorem sourceCouplingPrefix_succ (x : ℕ → Bool) (k : ℕ) :
    sourceCouplingPrefix x (k + 1) = sourceCouplingPrefix x k ++ [x k] := by
  unfold sourceCouplingPrefix
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

theorem measurable_sourceCouplingPrefix (k : ℕ) :
    Measurable (fun x : ℕ → Bool ↦ sourceCouplingPrefix x k) := by
  have hm : Measurable (fun x : ℕ → Bool ↦
      (fun i : Fin k ↦ x i.val)) :=
    measurable_pi_iff.mpr (fun i ↦ measurable_pi_apply i.val)
  exact (measurable_of_countable (fun f : Fin k → Bool ↦ List.ofFn f)).comp hm

private theorem source_cylinder_wrong_length (μ : Measure (ℕ → Bool))
    (k : ℕ) (w : List Bool) (hw : w.length ≠ k) :
    μ {x : ℕ → Bool | sourceCouplingPrefix x k = w} = 0 := by
  have heq : {x : ℕ → Bool | sourceCouplingPrefix x k = w} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro he
    exact hw ((congrArg List.length he).symm.trans (sourceCouplingPrefix_length x k))
  rw [heq, measure_empty]

private theorem adaptive_cylinder_wrong_length (r : List Bool → ℝ)
    (k : ℕ) (w : List Bool) (hw : w.length ≠ k) :
    uniformLaw {u : ℕ → ℝ | adaptiveCouplingWord r u k = w} = 0 := by
  have heq : {u : ℕ → ℝ | adaptiveCouplingWord r u k = w} = ∅ := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro he
    exact hw ((congrArg List.length he).symm.trans (adaptiveCouplingWord_length r u k))
  rw [heq, measure_empty]

/-- Uniqueness of every finite-dimensional law from the same conditional
event probabilities.  This statement does not assume independence of the
source process. -/
theorem sourceCouplingPrefix_law_of_cylinder_factors
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (r : List Bool → ℝ) (hr : ∀ w, 0 ≤ r w ∧ r w ≤ 1)
    (hfactor : ∀ (k : ℕ) (w : List Bool) (b : Bool), w.length = k →
      μ {x : ℕ → Bool | sourceCouplingPrefix x (k + 1) = w ++ [b]} =
        μ {x : ℕ → Bool | sourceCouplingPrefix x k = w} *
          adaptiveStepMass (r w) b) (k : ℕ) :
    μ.map (fun x ↦ sourceCouplingPrefix x k) =
      uniformLaw.map (fun u ↦ adaptiveCouplingWord r u k) := by
  have hcyl : ∀ k : ℕ, ∀ w : List Bool,
      μ {x : ℕ → Bool | sourceCouplingPrefix x k = w} =
        uniformLaw {u : ℕ → ℝ | adaptiveCouplingWord r u k = w} := by
    intro j
    induction j with
    | zero =>
        intro w
        by_cases hw : w = []
        · subst w
          simp [sourceCouplingPrefix_zero, adaptiveCouplingWord_zero]
        · have hlen : w.length ≠ 0 := by
            intro he
            exact hw (List.length_eq_zero_iff.mp he)
          rw [source_cylinder_wrong_length μ 0 w hlen,
            adaptive_cylinder_wrong_length r 0 w hlen]
    | succ j ih =>
        intro w
        induction w using List.reverseRecOn with
        | nil =>
            have hlen : ([] : List Bool).length ≠ j + 1 := by simp
            rw [source_cylinder_wrong_length μ (j + 1) [] hlen,
              adaptive_cylinder_wrong_length r (j + 1) [] hlen]
        | append_singleton w b _ =>
            by_cases hw : w.length = j
            · rw [hfactor j w b hw,
                adaptiveCouplingWord_cylinder_succ r hr j w b hw,
                ih w]
            · have hlen : (w ++ [b]).length ≠ j + 1 := by
                simpa using hw
              rw [source_cylinder_wrong_length μ (j + 1) (w ++ [b]) hlen,
                adaptive_cylinder_wrong_length r (j + 1) (w ++ [b]) hlen]
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.map_apply (measurable_sourceCouplingPrefix k)
      (measurableSet_singleton w),
    Measure.map_apply (measurable_adaptiveCouplingWord r k)
      (measurableSet_singleton w)]
  exact hcyl k w

end HeightPaper.CountCoupling
