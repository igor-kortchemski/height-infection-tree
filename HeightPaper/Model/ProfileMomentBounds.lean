module

public import HeightPaper.Model.ProfileShiftedMoments
public import HeightPaper.Model.RealNormalizer

/-!
# Real profile moment bounds with an unshifted normalizer

The cutoff in a moment difference is independent of the beginning of the
normalizing product. This is the form needed to compare the martingale at a
growing intermediate time with its value at the final time.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.Model

@[simp] theorem prescribedNormalizerFrom_zero (w : ℂ) (events : ℕ → Bool)
    (i₀ k : ℕ) :
    prescribedNormalizerFrom w events i₀ 0 k = prescribedNormalizer w events i₀ k := by
  induction k with
  | zero => simp [prescribedNormalizer]
  | succ k ih =>
      rw [prescribedNormalizerFrom_succ w events i₀ (Nat.zero_le k), ih,
        prescribedNormalizer]

theorem prescribedPath_profile_moment_sub_le (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N j : ℕ) (hj : j ≤ N) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizer w events (infectious s₀) N ≠ 0) :
    (∫ q, ‖normalizedActiveWeight w q.last /
          prescribedNormalizer w events (infectious s₀) N -
        normalizedActiveWeight w (q.eval j) /
          prescribedNormalizer w events (infectious s₀) j‖ ^ p
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N) ≤
      (4 * (2 : ℝ) ^ p) *
        ∑ k ∈ Finset.Ico j N, prescribedShiftedMomentBound w events s₀ 0 p k := by
  let F : ℕ → State → ℂ := fun k s ↦ normalizedActiveWeight w s /
    prescribedNormalizer w events (infectious s₀) k
  have hC' : prescribedNormalizerFrom w events (infectious s₀) 0 N ≠ 0 := by
    simpa only [prescribedNormalizerFrom_zero] using hC
  have hmean : ∀ k, j ≤ k → k < N →
      ∀ q ∈ (kernelPathLaw (fun i ↦ prescribedStep (events i)) s₀ k).support,
      (∫ t, F (k + 1) t ∂(prescribedStep (events k) q.last).toMeasure) = F k q.last := by
    intro k _ hk q hq
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
      Finset.prod_ne_zero_iff.mp hC' k (Finset.mem_Ico.mpr ⟨Nat.zero_le k, hk⟩)
    dsimp only [F]
    rw [integral_div, prescribedStep_normalized_integral w (events k) q.last hactive hnext,
      prescribedNormalizer, hc]
    exact mul_div_mul_right _ _ hfactor
  apply kernelPath_norm_rpow_sub_le_integrated
    (fun i ↦ prescribedStep (events i)) (fun i s ↦ finite_support_prescribedStep (events i) s)
    s₀ F (prescribedShiftedMomentBound w events s₀ 0 p) hp hp2 N j hj hmean
  intro k _ hk
  simpa only [F, prescribedNormalizerFrom_zero] using
    prescribedPath_shifted_increment_moment_le w events s₀ N 0 k (Nat.zero_le k) hk hp.le hpos hC'

/-- For a real tilt at least one, both event types have numerator bounded by
the tilt and denominator equal to the next normalizer times the next count. -/
theorem norm_prescribedIncrementCoeff_le {w : ℝ} (hw : 1 ≤ w)
    (events : ℕ → Bool) (k : ℕ) (hi : 0 < prescribedWalk events 1 (k + 1)) :
    ‖prescribedIncrementCoeff (w : ℂ) (prescribedNormalizer (w : ℂ) events 1 k)
      (events k) (prescribedWalk events 1 k)‖ ≤
      w / (realNormalizer w events 1 (k + 1) * (prescribedWalk events 1 (k + 1) : ℝ)) := by
  rw [prescribedIncrementCoeff_eq_next _ _ _ _ hi]
  have hn : prescribedNormalizer (w : ℂ) events 1 k *
      prescribedProfileFactor (w : ℂ) (events k) (prescribedWalk events 1 k) =
      (realNormalizer w events 1 (k + 1) : ℂ) :=
    prescribedNormalizer_ofReal w events 1 (k + 1)
  rw [hn]
  change ‖(if events k then (w : ℂ) else -1) /
    ((realNormalizer w events 1 (k + 1) : ℂ) *
      (prescribedWalk events 1 (k + 1) : ℂ))‖ ≤ _
  rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_real,
    Real.norm_of_nonneg (zero_le_one.trans (one_le_realNormalizer hw events 1 (k + 1)))]
  apply div_le_div_of_nonneg_right _
    (mul_nonneg (zero_le_one.trans (one_le_realNormalizer hw events 1 (k + 1)))
      (Nat.cast_nonneg _))
  cases events k <;> simp [Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans hw), hw]

theorem prescribedShiftedMomentBound_real_le {w p : ℝ} (hw : 1 ≤ w) (hp : 0 ≤ p)
    (events : ℕ → Bool) (n k : ℕ) (hi : 0 < prescribedWalk events 1 (k + 1)) :
    prescribedShiftedMomentBound (w : ℂ) events (initial n) 0 p k ≤
      ((w / (realNormalizer w events 1 (k + 1) *
        (prescribedWalk events 1 (k + 1) : ℝ))) ^ p * (2 : ℝ) ^ p) *
        realNormalizer (w ^ p) events 1 k := by
  have hwp : 1 ≤ w ^ p := Real.one_le_rpow hw hp
  simp only [prescribedShiftedMomentBound, infectious_initial, prescribedNormalizerFrom_zero,
    normalizedActiveWeight_initial, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (zero_le_one.trans hw), prescribedNormalizer_ofReal, Complex.ofReal_re]
  apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (one_le_realNormalizer hwp events 1 k))
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
  apply Real.rpow_le_rpow (norm_nonneg _) _ hp
  simpa only [prescribedNormalizer_ofReal] using norm_prescribedIncrementCoeff_le hw events k hi

/-- Polynomial lower bounds for the denominator and an upper bound for the
positive profile turn the exact increment formula into a summable power. -/
theorem profile_moment_ratio_le {w p A B c t a b C D I : ℝ}
    (hw : 0 ≤ w) (hp : 0 ≤ p) (hA : 0 < A) (_hB : 0 ≤ B)
    (hc : 0 < c) (ht : 0 < t) (hD : 0 ≤ D)
    (hC : A * t ^ a ≤ C) (hI : c * t ≤ I) (hupper : D ≤ B * t ^ b) :
    ((w / (C * I)) ^ p * (2 : ℝ) ^ p) * D ≤
      ((w / (A * c)) ^ p * (2 : ℝ) ^ p * B) * t ^ (b - p * (a + 1)) := by
  have hCa : 0 < A * t ^ a := mul_pos hA (Real.rpow_pos_of_pos ht _)
  have hct : 0 < c * t := mul_pos hc ht
  have hden : (A * t ^ a) * (c * t) ≤ C * I :=
    mul_le_mul hC hI hct.le (hCa.le.trans hC)
  calc
    _ ≤ ((w / ((A * t ^ a) * (c * t))) ^ p * (2 : ℝ) ^ p) * (B * t ^ b) := by
      apply mul_le_mul _ hupper hD
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by norm_num) _))
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
      apply Real.rpow_le_rpow (div_nonneg hw (mul_nonneg (hCa.le.trans hC) (hct.le.trans hI))) _ hp
      exact div_le_div_of_nonneg_left hw (mul_pos hCa hct) hden
    _ = _ := by
      have hdeneq : (A * t ^ a) * (c * t) = (A * c) * t ^ (a + 1) := by
        rw [Real.rpow_add_one ht.ne']
        ring
      rw [hdeneq, div_mul_eq_div_div, Real.div_rpow (div_nonneg hw (mul_pos hA hc).le)
        (Real.rpow_nonneg ht.le _) p, ← Real.rpow_mul ht.le]
      rw [show (a + 1) * p = p * (a + 1) by ring,
        Real.rpow_sub ht]
      ring

end HeightPaper.Model
