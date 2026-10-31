module

public import HeightPaper.Model.ProfileMomentDecay

/-!
# Complex profile moments along prescribed event words

These are finite, exact versions of the Jensen and increment estimates in the
paper's complex-martingale route. A normalizing product may begin at a cutoff
before the two times being compared. Polynomial bounds are explicit hypotheses
on the count word, not assumed stochastic conclusions.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.Model

/-- The paper's Jensen moment estimate, averaged over the actual prescribed
tree history. The initial positive profile is retained exactly. -/
theorem prescribedPath_shifted_normalized_moment_le (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N J : ℕ) {p : ℝ} (hp : 1 ≤ p)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizerFrom w events (infectious s₀) J N ≠ 0) :
    (∫ q, ‖normalizedActiveWeight w q.last /
      prescribedNormalizerFrom w events (infectious s₀) J N‖ ^ p
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N) ≤
      (normalizedActiveWeight ((‖w‖ ^ p : ℝ) : ℂ) s₀ *
        prescribedNormalizer ((‖w‖ ^ p : ℝ) : ℂ) events (infectious s₀) N).re /
          ‖prescribedNormalizerFrom w events (infectious s₀) J N‖ ^ p := by
  simp_rw [norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [integral_div]
  apply div_le_div_of_nonneg_right _ (Real.rpow_pos_of_pos (norm_pos_iff.mpr hC) p).le
  rw [← prescribedPath_realProfile_integral (‖w‖ ^ p) events s₀ N hpos]
  apply integral_mono_ae
    (integrable_kernelPathMeasure _ (fun i s ↦ finite_support_prescribedStep (events i) s) s₀ N _)
    (integrable_kernelPathMeasure _ (fun i s ↦ finite_support_prescribedStep (events i) s) s₀ N _)
  filter_upwards [ae_mem_support_kernelPathLaw (fun i ↦ prescribedStep (events i)) s₀ N]
    with q hq
  apply norm_normalizedActiveWeight_rpow_le w q.last _ hp
  apply Finset.card_pos.mp
  change 0 < infectious q.last
  rw [infectious_kernelPathLaw_prescribed events s₀ N
    (fun i hi ↦ hpos i hi.le) q hq]
  exact hpos N le_rfl

/-- Compare any two times after the normalizer's starting cutoff, on the
original full-history space. Earlier vanishing factors are harmless. -/
theorem prescribedPath_complex_moment_sub_le (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N J j : ℕ) (hJj : J ≤ j) (hjN : j ≤ N)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizerFrom w events (infectious s₀) J N ≠ 0) :
    (∫ q, ‖normalizedActiveWeight w q.last /
          prescribedNormalizerFrom w events (infectious s₀) J N -
        normalizedActiveWeight w (q.eval j) /
          prescribedNormalizerFrom w events (infectious s₀) J j‖ ^ p
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N) ≤
      (4 * (2 : ℝ) ^ p) *
        ∑ k ∈ Finset.Ico j N, prescribedShiftedMomentBound w events s₀ J p k := by
  let F : ℕ → State → ℂ := fun k s ↦ normalizedActiveWeight w s /
    prescribedNormalizerFrom w events (infectious s₀) J k
  have hmean : ∀ k, j ≤ k → k < N →
      ∀ q ∈ (kernelPathLaw (fun i ↦ prescribedStep (events i)) s₀ k).support,
      (∫ t, F (k + 1) t ∂(prescribedStep (events k) q.last).toMeasure) = F k q.last := by
    intro k hjk hk q hq
    have hc := infectious_kernelPathLaw_prescribed events s₀ k
      (fun i hi ↦ hpos i (by omega)) q hq
    have hactive : q.last.active.Nonempty := by
      apply Finset.card_pos.mp
      change 0 < infectious q.last
      rw [hc]
      exact hpos k hk.le
    have hnext : 0 < prescribedActiveCount (events k) (infectious q.last) := by
      rw [hc]
      exact hpos (k + 1) (by omega)
    have hfactor : prescribedProfileFactor w (events k)
        (prescribedWalk events (infectious s₀) k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hC k (Finset.mem_Ico.mpr ⟨hJj.trans hjk, hk⟩)
    dsimp only [F]
    rw [integral_div, prescribedStep_normalized_integral w (events k) q.last hactive hnext,
      prescribedNormalizerFrom_succ w events (infectious s₀) (hJj.trans hjk), hc]
    exact mul_div_mul_right _ _ hfactor
  exact kernelPath_norm_rpow_sub_le_integrated
    (fun i ↦ prescribedStep (events i)) (fun i s ↦ finite_support_prescribedStep (events i) s)
    s₀ F (prescribedShiftedMomentBound w events s₀ J p) hp hp2 N j hjN hmean
    (fun k hjk hk ↦ prescribedPath_shifted_increment_moment_le w events s₀ N J k
      (hJj.trans hjk) hk hp.le hpos hC)

theorem prescribedPath_complex_moment_sub_le_one (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N J j : ℕ) (hJj : J ≤ j) (hjN : j ≤ N)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizerFrom w events (infectious s₀) J N ≠ 0) :
    (∫ q, ‖normalizedActiveWeight w q.last /
          prescribedNormalizerFrom w events (infectious s₀) J N -
        normalizedActiveWeight w (q.eval j) /
          prescribedNormalizerFrom w events (infectious s₀) J j‖
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N) ≤
      ∑ k ∈ Finset.Ico j N, prescribedShiftedMomentBound w events s₀ J 1 k := by
  let F : ℕ → State → ℂ := fun k s ↦ normalizedActiveWeight w s /
    prescribedNormalizerFrom w events (infectious s₀) J k
  exact kernelPath_norm_sub_le_integrated
    (fun i ↦ prescribedStep (events i))
    (fun i s ↦ finite_support_prescribedStep (events i) s)
    s₀ F (prescribedShiftedMomentBound w events s₀ J 1) N j hjN
    (fun k hjk hk ↦ by
      simpa only [F, Real.rpow_one] using
        prescribedPath_shifted_increment_moment_le w events s₀ N J k
          (hJj.trans hjk) hk (show (1 : ℝ) ≤ 1 by norm_num) hpos hC)

theorem norm_prescribedIncrementCoeff_complex_le (w : ℂ) (hw : 1 ≤ ‖w‖)
    (events : ℕ → Bool) (i₀ J k : ℕ) (hJk : J ≤ k)
    (hi : 0 < prescribedWalk events i₀ (k + 1)) :
    ‖prescribedIncrementCoeff w (prescribedNormalizerFrom w events i₀ J k)
      (events k) (prescribedWalk events i₀ k)‖ ≤
      ‖w‖ / (‖prescribedNormalizerFrom w events i₀ J (k + 1)‖ *
        (prescribedWalk events i₀ (k + 1) : ℝ)) := by
  rw [prescribedIncrementCoeff_eq_next _ _ _ _ hi,
    ← prescribedNormalizerFrom_succ w events i₀ hJk]
  rw [norm_div, norm_mul, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  cases events k <;> simp [hw]

theorem prescribedShiftedMomentBound_complex_le (w : ℂ) (hw : 1 ≤ ‖w‖)
    {p : ℝ} (hp : 0 ≤ p) (events : ℕ → Bool) (n J k : ℕ) (hJk : J ≤ k)
    (hi : 0 < prescribedWalk events 1 (k + 1)) :
    prescribedShiftedMomentBound w events (initial n) J p k ≤
      ((‖w‖ / (‖prescribedNormalizerFrom w events 1 J (k + 1)‖ *
        (prescribedWalk events 1 (k + 1) : ℝ))) ^ p * (2 : ℝ) ^ p) *
        realNormalizer (‖w‖ ^ p) events 1 k := by
  have hwp : 1 ≤ ‖w‖ ^ p := Real.one_le_rpow hw hp
  simp only [prescribedShiftedMomentBound, infectious_initial,
    normalizedActiveWeight_initial, one_mul, prescribedNormalizer_ofReal, Complex.ofReal_re]
  apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (one_le_realNormalizer hwp events 1 k))
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
  exact Real.rpow_le_rpow (norm_nonneg _)
    (norm_prescribedIncrementCoeff_complex_le w hw events 1 J k hJk hi) hp

/-- Complex moment differences decay uniformly in the terminal horizon once
the explicit count and product bounds have a strictly summable exponent. -/
theorem prescribedPath_complex_moment_polynomial_le {w : ℂ} {p A B c a b : ℝ}
    (hw : 1 ≤ ‖w‖) (hp : 1 < p) (hp2 : p ≤ 2) (hA : 0 < A) (hB : 0 ≤ B)
    (hc : 0 < c) (hexp : b - p * (a + 1) < -1)
    (events : ℕ → Bool) (n N J j : ℕ) (hJj : J ≤ j) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events 1 i)
    (hC : prescribedNormalizerFrom w events 1 J N ≠ 0)
    (hClower : ∀ k ∈ Finset.Ico j N,
      A * ((k + 1 : ℕ) : ℝ) ^ a ≤ ‖prescribedNormalizerFrom w events 1 J (k + 1)‖)
    (hCupper : ∀ k ∈ Finset.Ico j N,
      realNormalizer (‖w‖ ^ p) events 1 k ≤ B * ((k + 1 : ℕ) : ℝ) ^ b)
    (hcount : ∀ k ∈ Finset.Ico j N,
      c * (k + 1 : ℕ) ≤ (prescribedWalk events 1 (k + 1) : ℝ)) :
    (∫ q, ‖normalizedActiveWeight w q.last /
          prescribedNormalizerFrom w events 1 J N -
        normalizedActiveWeight w (q.eval j) /
          prescribedNormalizerFrom w events 1 J j‖ ^ p
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N) ≤
      (4 * (2 : ℝ) ^ p) * ((‖w‖ / (A * c)) ^ p * (2 : ℝ) ^ p * B) *
        ((j : ℝ) ^ (b - p * (a + 1) + 1) / (-(b - p * (a + 1)) - 1)) := by
  have hp0 : 0 ≤ p := by linarith
  have hwp : 1 ≤ ‖w‖ ^ p := Real.one_le_rpow hw hp0
  have hm := prescribedPath_complex_moment_sub_le w events (initial n) N J j hJj hjN
    hp hp2 (by simpa only [infectious_initial] using hpos)
    (by simpa only [infectious_initial] using hC)
  simp only [infectious_initial] at hm
  refine hm.trans ?_
  have hconstant : 0 ≤ (‖w‖ / (A * c)) ^ p * (2 : ℝ) ^ p * B := by positivity
  calc
    _ ≤ (4 * (2 : ℝ) ^ p) *
        ∑ k ∈ Finset.Ico j N,
          ((‖w‖ / (A * c)) ^ p * (2 : ℝ) ^ p * B) *
            ((k + 1 : ℕ) : ℝ) ^ (b - p * (a + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k hk
      apply (prescribedShiftedMomentBound_complex_le w hw hp0 events n J k
        (hJj.trans (Finset.mem_Ico.mp hk).1)
        (hpos (k + 1) (by have := (Finset.mem_Ico.mp hk).2; omega))).trans
      exact profile_moment_ratio_le (norm_nonneg w) hp0 hA hB hc
        (by positivity) (zero_le_one.trans (one_le_realNormalizer hwp events 1 k))
        (hClower k hk) (hcount k hk) (hCupper k hk)
    _ = (4 * (2 : ℝ) ^ p) * ((‖w‖ / (A * c)) ^ p * (2 : ℝ) ^ p * B) *
        ∑ k ∈ Finset.Ico j N, ((k + 1 : ℕ) : ℝ) ^ (b - p * (a + 1)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Ico_succ_rpow_le hexp hj hjN)
      (mul_nonneg (by positivity) hconstant)

end HeightPaper.Model
