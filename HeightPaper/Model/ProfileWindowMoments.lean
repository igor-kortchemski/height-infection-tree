module

public import HeightPaper.Model.ProfileMomentBounds

/-!
# Profile martingale differences on a macroscopic time window

Monotonicity of the positive normalizers reduces the hypotheses to two endpoint
product bounds and a lower active-count bound throughout the window. This form
allows every cutoff in a finite tilt bootstrap to remain macroscopic.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.Model

theorem prescribedPath_profile_moment_window_le {w p A B c : ℝ}
    (hw : 1 ≤ w) (hp : 1 < p) (hp2 : p ≤ 2) (hA : 0 < A) (hB : 0 ≤ B)
    (hc : 0 < c) (events : ℕ → Bool) (n N j : ℕ) (hjN : j ≤ N)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events 1 i)
    (hClower : A ≤ realNormalizer w events 1 j)
    (hCupper : realNormalizer (w ^ p) events 1 N ≤ B)
    (hcount : ∀ k ∈ Finset.Ico j N, c ≤ (prescribedWalk events 1 (k + 1) : ℝ)) :
    (∫ q, ‖normalizedActiveWeight (w : ℂ) q.last /
          prescribedNormalizer (w : ℂ) events 1 N -
        normalizedActiveWeight (w : ℂ) (q.eval j) /
          prescribedNormalizer (w : ℂ) events 1 j‖ ^ p
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N) ≤
      (4 * (2 : ℝ) ^ p) * (N - j : ℕ) *
        ((w / (A * c)) ^ p * (2 : ℝ) ^ p * B) := by
  have hp0 : 0 ≤ p := by linarith
  have hwp : 1 ≤ w ^ p := Real.one_le_rpow hw hp0
  have hC : prescribedNormalizer (w : ℂ) events 1 N ≠ 0 := by
    rw [prescribedNormalizer_ofReal, ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_realNormalizer hw events 1 N))
  have hmoment := prescribedPath_profile_moment_sub_le (w : ℂ) events (initial n) N j
    hjN hp hp2 (by simpa only [infectious_initial] using hpos)
    (by simpa only [infectious_initial] using hC)
  simp only [infectious_initial] at hmoment
  refine hmoment.trans ?_
  calc
    _ ≤ (4 * (2 : ℝ) ^ p) *
        ∑ k ∈ Finset.Ico j N, ((w / (A * c)) ^ p * (2 : ℝ) ^ p * B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      apply (prescribedShiftedMomentBound_real_le hw hp0 events n k
        (hpos (k + 1) (by omega))).trans
      have hlow : A ≤ realNormalizer w events 1 (k + 1) :=
        hClower.trans (realNormalizer_mono hw events 1 (by omega))
      have hupp : realNormalizer (w ^ p) events 1 k ≤ B :=
        (realNormalizer_mono hwp events 1 hk'.2.le).trans hCupper
      simpa only [Real.one_rpow, mul_one] using
        profile_moment_ratio_le (a := 0) (b := 0) (t := 1)
          (zero_le_one.trans hw) hp0 hA hB hc zero_lt_one
          (zero_le_one.trans (one_le_realNormalizer hwp events 1 k))
          (by simpa using hlow) (by simpa using hcount k hk) (by simpa using hupp)
    _ = _ := by simp [mul_assoc]

/-- Markov's inequality for the exact finite-window profile difference. -/
theorem prescribedPath_profile_deviation_le_of_moment (w : ℂ) (events : ℕ → Bool)
    (n N j : ℕ) {p D δ : ℝ} (hp : 0 < p) (hδ : 0 < δ)
    (hmoment :
      (∫ q, ‖normalizedActiveWeight w q.last / prescribedNormalizer w events 1 N -
          normalizedActiveWeight w (q.eval j) / prescribedNormalizer w events 1 j‖ ^ p
        ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N) ≤ D) :
    (kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N).real
      {q | δ ≤ ‖normalizedActiveWeight w q.last / prescribedNormalizer w events 1 N -
        normalizedActiveWeight w (q.eval j) / prescribedNormalizer w events 1 j‖} ≤ D / δ ^ p := by
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N)
    (f := fun q ↦ ‖normalizedActiveWeight w q.last / prescribedNormalizer w events 1 N -
      normalizedActiveWeight w (q.eval j) / prescribedNormalizer w events 1 j‖ ^ p)
    (Filter.Eventually.of_forall (fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _))
    (integrable_kernelPathMeasure _ (fun i s ↦ finite_support_prescribedStep (events i) s)
      (initial n) N _) (δ ^ p)
  have hevent : {q : FinitePath N | δ ^ p ≤
      ‖normalizedActiveWeight w q.last / prescribedNormalizer w events 1 N -
        normalizedActiveWeight w (q.eval j) / prescribedNormalizer w events 1 j‖ ^ p} =
      {q | δ ≤ ‖normalizedActiveWeight w q.last / prescribedNormalizer w events 1 N -
        normalizedActiveWeight w (q.eval j) / prescribedNormalizer w events 1 j‖} := by
    ext q
    exact Real.rpow_le_rpow_iff hδ.le (norm_nonneg _) hp
  rw [hevent] at hmark
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ _)).mpr
  simpa only [mul_comm] using hmark.trans hmoment

end HeightPaper.Model
