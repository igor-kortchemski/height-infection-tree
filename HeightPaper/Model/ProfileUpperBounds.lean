module

public import HeightPaper.Model.TotalProfile
public import HeightPaper.Model.ProfileTilt

/-!
# Finite first-moment bounds for positive real profiles

All estimates here concern the exact prescribed history law on a positive
count word. They are uniform whenever the final product normalizer has a
specified upper bound, which permits averaging over the epidemic event words.
-/

public section

open MeasureTheory

namespace HeightPaper.Model

/-- Markov's inequality for the normalized active profile. -/
theorem prescribedPath_normalizedProfile_tail_le {w A : ℝ} (hw : 0 ≤ w) (hA : 0 < A)
    (events : ℕ → Bool) (n N : ℕ)
    (hpos : ∀ k ≤ N, 0 < prescribedWalk events 1 k) :
    (kernelPathMeasure (fun k ↦ prescribedStep (events k)) (initial n) N).real
      {p | A ≤ activeWeight w p.last / (infectious p.last : ℝ)} ≤
        realNormalizer w events 1 N / A := by
  have hi := integrable_kernelPathMeasure (fun k ↦ prescribedStep (events k))
    (fun k s ↦ finite_support_prescribedStep (events k) s) (initial n) N
    (fun p ↦ activeWeight w p.last / (infectious p.last : ℝ))
  have hn (p : FinitePath N) : 0 ≤ activeWeight w p.last / (infectious p.last : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun _ _ ↦ pow_nonneg hw _) (Nat.cast_nonneg _)
  have hb := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hn) hi A
  rw [prescribedPath_realProfile_integral w events (initial n) N (by simpa using hpos)] at hb
  simp only [normalizedActiveWeight, activeWeight_initial, infectious_initial,
    Nat.cast_one, div_one, one_mul, prescribedNormalizer_ofReal, Complex.ofReal_re] at hb
  exact (le_div_iff₀ hA).mpr (by simpa only [mul_comm] using hb)

/-- A real height threshold avoids rounding losses in logarithmic scaling. -/
theorem prescribedPath_real_height_tail_le {x H : ℝ} (hx : 0 ≤ x)
    (events : ℕ → Bool) (n N : ℕ)
    (hpos : ∀ k ≤ N, 0 < prescribedWalk events 1 k) :
    (kernelPathMeasure (fun k ↦ prescribedStep (events k)) (initial n) N).real
      {p | H ≤ (height p.last : ℝ)} ≤
        (1 + Real.exp x * N * realNormalizer (Real.exp x) events 1 N) /
          Real.exp (x * H) := by
  have hi := integrable_kernelPathMeasure (fun k ↦ prescribedStep (events k))
    (fun k s ↦ finite_support_prescribedStep (events k) s) (initial n) N
    (fun p ↦ totalWeight (Real.exp x) p.last)
  have hb := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun p : FinitePath N ↦
      totalWeight_nonneg (Real.exp_nonneg x) p.last) hi (Real.exp (x * H))
  have hu := prescribedPath_totalWeight_integral_le (Real.exp x)
    (Real.one_le_exp_iff.mpr hx) events n N hpos
  calc
    _ ≤ (kernelPathMeasure (fun k ↦ prescribedStep (events k)) (initial n) N).real
        {p | Real.exp (x * H) ≤ totalWeight (Real.exp x) p.last} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro p hp
      calc
        _ ≤ Real.exp (x * (height p.last : ℝ)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp hx)
        _ = (Real.exp x) ^ height p.last := by rw [mul_comm, Real.exp_nat_mul]
        _ ≤ _ := pow_height_le_totalWeight (Real.exp_nonneg x) p.last
    _ ≤ _ := (le_div_iff₀ (Real.exp_pos _)).mpr (by
      simpa only [mul_comm] using hb.trans hu)

end HeightPaper.Model
