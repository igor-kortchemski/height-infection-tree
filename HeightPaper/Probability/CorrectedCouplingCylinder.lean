module

public import HeightPaper.Probability.CorrectedCouplingWordLaw

/-!
# Cylinder probabilities of the adaptive count word

The next event factorizes into the previous word probability and its
conditional recovery/birth mass.  This is the finite-dimensional law bridge
needed to replace an arbitrary given binary process by the common-uniform
construction in the corrected coupling.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HeightPaper.CountCoupling

theorem adaptiveCouplingWord_length (r : List Bool → ℝ) (u : ℕ → ℝ)
    (k : ℕ) : (adaptiveCouplingWord r u k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [adaptiveCouplingWord_succ, ih]

theorem adaptiveCouplingWord_succ_eq_iff (r : List Bool → ℝ)
    (u : ℕ → ℝ) (k : ℕ) (w : List Bool) (b : Bool)
    (hw : w.length = k) :
    adaptiveCouplingWord r u (k + 1) = w ++ [b] ↔
      adaptiveCouplingWord r u k = w ∧
        recoveryThresholdBirth (r w) (u k) = b := by
  rw [adaptiveCouplingWord_succ]
  constructor
  · intro h
    obtain ⟨hp, ht⟩ := List.append_inj h
      (by rw [adaptiveCouplingWord_length, hw])
    refine ⟨hp, ?_⟩
    simpa [hp] using ht
  · rintro ⟨hp, ht⟩
    rw [hp, ht]

def adaptiveStepMass (t : ℝ) (b : Bool) : ℝ≥0∞ :=
  if b then ENNReal.ofReal (1 - t) else ENNReal.ofReal t

theorem uniformLaw_recoveryThresholdBirth_probability
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (k : ℕ) (b : Bool) :
    uniformLaw {u : ℕ → ℝ | recoveryThresholdBirth t (u k) = b} =
      adaptiveStepMass t b := by
  cases b
  · have heq : {u : ℕ → ℝ | recoveryThresholdBirth t (u k) = false} =
        (fun u : ℕ → ℝ ↦ u k) ⁻¹' {x : ℝ | x < t} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      by_cases h : t ≤ u k
      · simp [recoveryThresholdBirth, h]
      · simp [recoveryThresholdBirth, h, lt_of_not_ge h]
    rw [heq]
    change uniformLaw ((fun u : ℕ → ℝ ↦ u k) ⁻¹' Set.Iio t) = _
    rw [← Measure.map_apply (measurable_pi_apply k)
      measurableSet_Iio, uniformLaw_map_eval]
    change unitUniform {x : ℝ | x < t} = _
    rw [unitUniform_lt_of_unit ht0 ht1]
    simp [adaptiveStepMass]
  · have heq : {u : ℕ → ℝ | recoveryThresholdBirth t (u k) = true} =
        (fun u : ℕ → ℝ ↦ u k) ⁻¹' {x : ℝ | t ≤ x} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      by_cases h : t ≤ u k <;> simp [recoveryThresholdBirth, h]
    rw [heq]
    change uniformLaw ((fun u : ℕ → ℝ ↦ u k) ⁻¹' Set.Ici t) = _
    rw [← Measure.map_apply (measurable_pi_apply k)
      measurableSet_Ici, uniformLaw_map_eval]
    change unitUniform {x : ℝ | t ≤ x} = _
    rw [unitUniform_ge_of_unit ht0 ht1]
    simp [adaptiveStepMass]

/-- Exact finite-cylinder chain rule for the uniform realization. -/
theorem adaptiveCouplingWord_cylinder_succ
    (r : List Bool → ℝ) (hr : ∀ w, 0 ≤ r w ∧ r w ≤ 1)
    (k : ℕ) (w : List Bool) (b : Bool) (hw : w.length = k) :
    uniformLaw {u : ℕ → ℝ |
      adaptiveCouplingWord r u (k + 1) = w ++ [b]} =
      uniformLaw {u : ℕ → ℝ | adaptiveCouplingWord r u k = w} *
        adaptiveStepMass (r w) b := by
  have heq : {u : ℕ → ℝ |
      adaptiveCouplingWord r u (k + 1) = w ++ [b]} =
      (fun u : ℕ → ℝ ↦ adaptiveCouplingWord r u k) ⁻¹' {w} ∩
        (fun u : ℕ → ℝ ↦ u k) ⁻¹'
          {x : ℝ | recoveryThresholdBirth (r w) x = b} := by
    ext u
    exact adaptiveCouplingWord_succ_eq_iff r u k w b hw
  rw [heq]
  have hm : MeasurableSet {x : ℝ | recoveryThresholdBirth (r w) x = b} :=
    (measurable_recoveryThresholdBirth (r w)) (measurableSet_singleton b)
  rw [(adaptiveCouplingWord_indep_next r k).measure_inter_preimage_eq_mul
    {w} {x : ℝ | recoveryThresholdBirth (r w) x = b}
    (measurableSet_singleton w) hm]
  change uniformLaw {u : ℕ → ℝ | adaptiveCouplingWord r u k = w} *
      uniformLaw {u : ℕ → ℝ | recoveryThresholdBirth (r w) (u k) = b} = _
  rw [uniformLaw_recoveryThresholdBirth_probability (hr w).1 (hr w).2]

end HeightPaper.CountCoupling
