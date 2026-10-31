module

public import HeightPaper.Model.PrescribedShifted
public import HeightPaper.Model.ProfilePathMoments
public import HeightPaper.Model.KernelPathMoments

/-!
# Finite p-th moment differences for the prescribed profile martingale

The coefficient and positive-profile product are explicit. Earlier factors may
vanish: all denominators start at the chosen cutoff. The result concerns the
actual whole-history probability law, including the random tree at the cutoff.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.Model

/-- The centered increment coefficient uses the updated normalizer and the
post-event active count, the denominator in the paper's moment estimate. -/
theorem prescribedIncrementCoeff_eq_next (w C : ℂ) (birth : Bool) (i : ℕ)
    (hi : 0 < prescribedActiveCount birth i) :
    prescribedIncrementCoeff w C birth i =
      (if birth then w else -1) /
        ((C * prescribedProfileFactor w birth i) * (prescribedActiveCount birth i : ℂ)) := by
  cases birth with
  | false =>
      have hI : 1 ≤ i := by
        simp only [prescribedActiveCount, Bool.false_eq_true, ↓reduceIte] at hi
        omega
      simp [prescribedIncrementCoeff, prescribedProfileFactor, prescribedActiveCount,
        Nat.cast_sub hI]
  | true =>
      have hip : (i : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
      simp only [prescribedIncrementCoeff, prescribedProfileFactor, prescribedActiveCount,
        ↓reduceIte, Nat.cast_add, Nat.cast_one]
      congr 1
      field_simp
      ring

theorem prescribedNormalizerFrom_ne_zero_of_le (w : ℂ) (events : ℕ → Bool) (i₀ : ℕ)
    {j k N : ℕ} (hk : k ≤ N) (hC : prescribedNormalizerFrom w events i₀ j N ≠ 0) :
    prescribedNormalizerFrom w events i₀ j k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact Finset.prod_ne_zero_iff.mp hC i
    (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hi).1, (Finset.mem_Ico.mp hi).2.trans_le hk⟩)

/-- The explicit deterministic bound on the averaged p-th increment moment. -/
noncomputable def prescribedShiftedMomentBound (w : ℂ) (events : ℕ → Bool) (s₀ : State)
    (j : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (‖prescribedIncrementCoeff w (prescribedNormalizerFrom w events (infectious s₀) j k)
    (events k) (prescribedWalk events (infectious s₀) k)‖ ^ p * (2 : ℝ) ^ p) *
      (normalizedActiveWeight ((‖w‖ ^ p : ℝ) : ℂ) s₀ *
        prescribedNormalizer ((‖w‖ ^ p : ℝ) : ℂ) events (infectious s₀) k).re

/-- The averaged increment estimate for a product beginning at an arbitrary
cutoff. Only factors after that cutoff are required to be nonzero. -/
theorem prescribedPath_shifted_increment_moment_le (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N j k : ℕ) (hjk : j ≤ k) (hk : k < N) {p : ℝ} (hp : 1 ≤ p)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizerFrom w events (infectious s₀) j N ≠ 0) :
    (∫ q, ∫ t,
      ‖normalizedActiveWeight w t / prescribedNormalizerFrom w events (infectious s₀) j (k + 1) -
        normalizedActiveWeight w q.last / prescribedNormalizerFrom w events (infectious s₀) j k‖ ^ p
        ∂(prescribedStep (events k) q.last).toMeasure
        ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ k) ≤
      prescribedShiftedMomentBound w events s₀ j p k := by
  have hCk := prescribedNormalizerFrom_ne_zero_of_le w events (infectious s₀) hk.le hC
  have hfactor : prescribedProfileFactor w (events k)
      (prescribedWalk events (infectious s₀) k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hC k (Finset.mem_Ico.mpr ⟨hjk, hk⟩)
  calc
    _ ≤ ∫ q,
        (‖prescribedIncrementCoeff w (prescribedNormalizerFrom w events (infectious s₀) j k)
          (events k) (prescribedWalk events (infectious s₀) k)‖ ^ p * (2 : ℝ) ^ p) *
          (activeWeight (‖w‖ ^ p) q.last / (infectious q.last : ℝ))
        ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ k := by
      apply integral_mono_ae
        (integrable_kernelPathMeasure _ (fun i s ↦ finite_support_prescribedStep (events i) s) s₀ k _)
        (integrable_kernelPathMeasure _ (fun i s ↦ finite_support_prescribedStep (events i) s) s₀ k _)
      filter_upwards [ae_mem_support_kernelPathLaw (fun i ↦ prescribedStep (events i)) s₀ k]
        with q hq
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
      have hb := prescribedStep_profile_increment_moment_le w
        (prescribedNormalizerFrom w events (infectious s₀) j k) (events k) q.last hactive hp
        hnext hCk (by simpa only [hc] using hfactor)
      simpa only [prescribedNormalizerFrom_succ w events (infectious s₀) hjk, hc, mul_assoc] using hb
    _ = _ := by
      rw [integral_const_mul, prescribedPath_realProfile_integral (‖w‖ ^ p) events s₀ k
        (fun i hi ↦ hpos i (by omega))]
      rfl

/-- A complete finite moment-difference bound for the actual complex profile
martingale. The earlier profile is random and belongs to the same history;
the sum contains only the explicit products and active-count walk. -/
theorem prescribedPath_shifted_profile_moment_le (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N j : ℕ) (hj : j ≤ N) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizerFrom w events (infectious s₀) j N ≠ 0) :
    (∫ q, ‖normalizedActiveWeight w q.last /
          prescribedNormalizerFrom w events (infectious s₀) j N -
        normalizedActiveWeight w (q.eval j)‖ ^ p
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N) ≤
      (4 * (2 : ℝ) ^ p) *
        ∑ k ∈ Finset.Ico j N, prescribedShiftedMomentBound w events s₀ j p k := by
  let F : ℕ → State → ℂ := fun k s ↦ normalizedActiveWeight w s /
    prescribedNormalizerFrom w events (infectious s₀) j k
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
      Finset.prod_ne_zero_iff.mp hC k (Finset.mem_Ico.mpr ⟨hjk, hk⟩)
    dsimp only [F]
    rw [integral_div, prescribedStep_normalized_integral w (events k) q.last hactive hnext,
      prescribedNormalizerFrom_succ w events (infectious s₀) hjk, hc]
    exact mul_div_mul_right _ _ hfactor
  have hh := kernelPath_norm_rpow_sub_le_integrated
    (fun i ↦ prescribedStep (events i)) (fun i s ↦ finite_support_prescribedStep (events i) s)
    s₀ F (prescribedShiftedMomentBound w events s₀ j p) hp hp2 N j hj hmean
    (fun k hjk hk ↦ prescribedPath_shifted_increment_moment_le w events s₀ N j k hjk hk hp.le hpos hC)
  simpa only [F, prescribedNormalizerFrom_self, div_one] using hh

/-- The endpoint first moment follows by summing ordinary triangle bounds. -/
theorem prescribedPath_shifted_profile_moment_le_one (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N j : ℕ) (hj : j ≤ N)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizerFrom w events (infectious s₀) j N ≠ 0) :
    (∫ q, ‖normalizedActiveWeight w q.last /
          prescribedNormalizerFrom w events (infectious s₀) j N -
        normalizedActiveWeight w (q.eval j)‖
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N) ≤
      ∑ k ∈ Finset.Ico j N, prescribedShiftedMomentBound w events s₀ j 1 k := by
  let F : ℕ → State → ℂ := fun k s ↦ normalizedActiveWeight w s /
    prescribedNormalizerFrom w events (infectious s₀) j k
  have hh := kernelPath_norm_sub_le_integrated
    (fun i ↦ prescribedStep (events i))
    (fun i s ↦ finite_support_prescribedStep (events i) s)
    s₀ F (prescribedShiftedMomentBound w events s₀ j 1) N j hj
    (fun k hjk hk ↦ by
      simpa only [F, Real.rpow_one] using
        prescribedPath_shifted_increment_moment_le w events s₀ N j k hjk hk
          (show (1 : ℝ) ≤ 1 by norm_num) hpos hC)
  simpa only [F, prescribedNormalizerFrom_self, div_one] using hh

end HeightPaper.Model
