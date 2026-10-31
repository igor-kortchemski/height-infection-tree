module

public import HeightPaper.Model.HeightPotential
public import HeightPaper.Model.ProfileMoments
public import HeightPaper.Model.PathExpectation
public import HeightPaper.Probability.KernelIteration

/-! # Height-CDF potentials integrated against the actual SIR kernel -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace HeightPaper.Model

theorem eventChoice_integral_real (rate : ℝ≥0) (susceptible : ℕ) (f : Bool → ℝ) :
    (∫ b, f b ∂(eventChoice rate susceptible).toMeasure) =
      (infectionProbability rate susceptible : ℝ) * f true +
        (1 - (infectionProbability rate susceptible : ℝ)) * f false := by
  rw [PMF.integral_eq_sum, Fintype.sum_bool]
  have hp : (infectionProbability rate susceptible : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast infectionProbability_le_one rate susceptible
  simp [eventChoice_true, eventChoice_false, ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top,
    smul_eq_mul]

theorem stepDraw_integral_real (rate : ℝ≥0) (s : State) (h : s.active.Nonempty)
    (f : Fin s.vertices → Bool → ℝ) :
    (∫ vb, f vb.1 vb.2 ∂(stepDraw rate s h).toMeasure) =
      ∫ v, (∫ b, f v b ∂(eventChoice rate s.susceptible).toMeasure)
        ∂(uniformActive s h).toMeasure := by
  simp only [PMF.integral_eq_sum, Fintype.sum_prod_type, stepDraw_apply,
    ENNReal.toReal_mul, mul_smul, Finset.smul_sum]

/-- Every real state observable has the expected finite parent/event average.
The zero-susceptible infection weight is zero, so the formula remains valid at
that boundary without imposing a positive susceptible count. -/
theorem step_integral_real (rate : ℝ≥0) (s : State) (ha : s.active.Nonempty)
    (f : State → ℝ) :
    (∫ t, f t ∂(step rate s).toMeasure) =
      (∑ v ∈ s.active,
        ((1 - (infectionProbability rate s.susceptible : ℝ)) * f (recover s v) +
          (infectionProbability rate s.susceptible : ℝ) * f (infect s v))) /
            (infectious s : ℝ) := by
  rw [step_eq_map_stepDraw rate s ha, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    integral_map_of_stronglyMeasurable (measurable_of_finite _)
      (measurable_state f).stronglyMeasurable,
    stepDraw_integral_real rate s ha (fun v b ↦
      f (if b = true ∧ 0 < s.susceptible then infect s v else recover s v)),
    uniformActive_integral_real]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [eventChoice_integral_real]
  by_cases hs : 0 < s.susceptible
  · simp [hs, add_comm]
  · have hz : s.susceptible = 0 := by omega
    simp [hz, infectionProbability_zero]

/-- A lower bound on recovery probability gives a lower bound on the next
expected CDF potential, for the actual SIR transition including absorption. -/
theorem freshHeightPotential_step_subharmonic (p : unitInterval) (hp : 0 < (p : ℝ))
    (rate : ℝ≥0) (cutoff : ℕ) (hcutoff : 0 < cutoff) (roots : Finset ℕ) (h : ℕ)
    (s : State) (hcut : cutoff ≤ s.vertices)
    (hpr : (p : ℝ) ≤ 1 - (infectionProbability rate s.susceptible : ℝ)) :
    freshHeightPotential p cutoff hcutoff roots h s ≤
      ∫ t, freshHeightPotential p cutoff hcutoff roots h t ∂(step rate s).toMeasure := by
  by_cases ha : s.active.Nonempty
  · rw [step_integral_real rate s ha]
    have hi : 0 < (infectious s : ℝ) := by exact_mod_cast ha.card_pos
    apply (le_div_iff₀ hi).mpr
    calc
      _ = ∑ v ∈ s.active, freshHeightPotential p cutoff hcutoff roots h s := by
        simp [infectious, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v hv ↦ by
        simpa only [sub_sub_cancel] using
          freshHeightPotential_subharmonic p hp cutoff hcutoff roots h s v hv hcut hpr
  · rw [step_absorbed rate (Finset.not_nonempty_iff_eq_empty.mp ha), PMF.toMeasure_pure,
      integral_dirac]

/-- The analogous upper bound from an upper bound on recovery probability. -/
theorem freshHeightPotential_step_superharmonic (p : unitInterval) (hp : 0 < (p : ℝ))
    (rate : ℝ≥0) (cutoff : ℕ) (hcutoff : 0 < cutoff) (roots : Finset ℕ) (h : ℕ)
    (s : State) (hcut : cutoff ≤ s.vertices)
    (hrp : 1 - (infectionProbability rate s.susceptible : ℝ) ≤ (p : ℝ)) :
    (∫ t, freshHeightPotential p cutoff hcutoff roots h t ∂(step rate s).toMeasure) ≤
      freshHeightPotential p cutoff hcutoff roots h s := by
  by_cases ha : s.active.Nonempty
  · rw [step_integral_real rate s ha]
    have hi : 0 < (infectious s : ℝ) := by exact_mod_cast ha.card_pos
    apply (div_le_iff₀ hi).mpr
    calc
      _ ≤ ∑ v ∈ s.active, freshHeightPotential p cutoff hcutoff roots h s :=
        Finset.sum_le_sum fun v hv ↦ by
          simpa only [sub_sub_cancel] using
            freshHeightPotential_superharmonic p hp cutoff hcutoff roots h s v hv hcut hrp
      _ = _ := by simp [infectious, mul_comm]
  · rw [step_absorbed rate (Finset.not_nonempty_iff_eq_empty.mp ha), PMF.toMeasure_pure,
      integral_dirac]

end HeightPaper.Model
