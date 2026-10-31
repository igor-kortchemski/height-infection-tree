module

public import HeightPaper.Model.KernelPath
public import HeightPaper.Probability.ComplexMartingaleMoments

/-!
# Moment differences on the actual finite history law

The earlier value in a martingale difference remains random. During each next
kernel integral it is fixed by the complete preceding history, so the scalar
remainder's linear term cancels without assuming a deterministic value at the
starting time.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.Model

/-- At the endpoint `p = 1`, the triangle inequality gives the same
finite-history increment sum without using centering. -/
theorem kernelPath_norm_sub_le_integrated (K : ℕ → State → PMF State)
    (hK : ∀ k s, (K k s).support.Finite) (s₀ : State) (F : ℕ → State → ℂ)
    (B : ℕ → ℝ) (N j : ℕ) (hj : j ≤ N)
    (hincrement : ∀ k, j ≤ k → k < N →
      (∫ q, ∫ t, ‖F (k + 1) t - F k q.last‖ ∂(K k q.last).toMeasure
        ∂kernelPathMeasure K s₀ k) ≤ B k) :
    (∫ q, ‖F N q.last - F j (q.eval j)‖ ∂kernelPathMeasure K s₀ N) ≤
      ∑ k ∈ Finset.Ico j N, B k := by
  induction N, hj using Nat.le_induction with
  | base => simp
  | succ n hjn ih =>
      have ih' := ih (fun k hjk hkn ↦ hincrement k hjk (by omega))
      rw [kernelPathMeasure_integral_succ K hK s₀ n]
      simp only [FinitePath.append_last, FinitePath.append_eval_of_le _ _ hjn]
      have hpoint (q : FinitePath n) (t : State) :
          ‖F (n + 1) t - F j (q.eval j)‖ ≤
            ‖F n q.last - F j (q.eval j)‖ + ‖F (n + 1) t - F n q.last‖ := by
        have hh := norm_add_le (F (n + 1) t - F n q.last)
          (F n q.last - F j (q.eval j))
        convert hh using 1 <;> abel
      calc
        _ ≤ ∫ q, (‖F n q.last - F j (q.eval j)‖ +
            ∫ t, ‖F (n + 1) t - F n q.last‖ ∂(K n q.last).toMeasure)
              ∂kernelPathMeasure K s₀ n := by
          apply integral_mono (integrable_kernelPathMeasure K hK s₀ n _)
            (integrable_kernelPathMeasure K hK s₀ n _)
          intro q
          calc
            _ ≤ ∫ t, (‖F n q.last - F j (q.eval j)‖ +
                ‖F (n + 1) t - F n q.last‖) ∂(K n q.last).toMeasure :=
              integral_mono
                (FinitePMF.integrable_of_finite_support _ (hK n q.last) _)
                (FinitePMF.integrable_of_finite_support _ (hK n q.last) _)
                (hpoint q)
            _ = _ := by
              rw [integral_add
                (FinitePMF.integrable_of_finite_support _ (hK n q.last) _)
                (FinitePMF.integrable_of_finite_support _ (hK n q.last) _),
                integral_const]
              simp
        _ = (∫ q, ‖F n q.last - F j (q.eval j)‖ ∂kernelPathMeasure K s₀ n) +
            ∫ q, ∫ t, ‖F (n + 1) t - F n q.last‖ ∂(K n q.last).toMeasure
              ∂kernelPathMeasure K s₀ n := by
          rw [integral_add (integrable_kernelPathMeasure K hK s₀ n _)
            (integrable_kernelPathMeasure K hK s₀ n _)]
        _ ≤ _ := by
          rw [Finset.sum_Ico_succ_top hjn]
          linarith [hincrement n hjn (by omega)]

/-- Finite-time scalar martingale differences, with averaged conditional
increments and no assumption that the earlier observation is deterministic. -/
theorem kernelPath_abs_rpow_sub_le_integrated (K : ℕ → State → PMF State)
    (hK : ∀ k s, (K k s).support.Finite) (s₀ : State) (F : ℕ → State → ℝ)
    (B : ℕ → ℝ) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (N j : ℕ) (hj : j ≤ N)
    (hmean : ∀ k, j ≤ k → k < N → ∀ q ∈ (kernelPathLaw K s₀ k).support,
      (∫ t, F (k + 1) t ∂(K k q.last).toMeasure) = F k q.last)
    (hincrement : ∀ k, j ≤ k → k < N →
      (∫ q, ∫ t, |F (k + 1) t - F k q.last| ^ p ∂(K k q.last).toMeasure
        ∂kernelPathMeasure K s₀ k) ≤ B k) :
    (∫ q, |F N q.last - F j (q.eval j)| ^ p ∂kernelPathMeasure K s₀ N) ≤
      4 * ∑ k ∈ Finset.Ico j N, B k := by
  induction N, hj using Nat.le_induction with
  | base =>
      simp only [FinitePath.eval_last, sub_self, abs_zero,
        Real.zero_rpow (by linarith : p ≠ 0), integral_zero, Finset.Ico_self,
        Finset.sum_empty, mul_zero, le_refl]
  | succ n hjn ih =>
      have ih' := ih (fun k hjk hkn ↦ hmean k hjk (by omega))
        (fun k hjk hkn ↦ hincrement k hjk (by omega))
      rw [kernelPathMeasure_integral_succ K hK s₀ n]
      simp only [FinitePath.append_last, FinitePath.append_eval_of_le _ _ hjn]
      calc
        _ ≤ ∫ q, |F n q.last - F j (q.eval j)| ^ p +
            4 * ∫ t, |F (n + 1) t - F n q.last| ^ p ∂(K n q.last).toMeasure
              ∂kernelPathMeasure K s₀ n := by
          apply integral_mono_ae (integrable_kernelPathMeasure K hK s₀ n _)
            (integrable_kernelPathMeasure K hK s₀ n _)
          filter_upwards [ae_mem_support_kernelPathLaw K s₀ n] with q hq
          exact FinitePMF.integral_abs_rpow_sub_le_of_mean (K n q.last) (hK n q.last)
            (F (n + 1)) hp hp2 (F j (q.eval j)) (hmean n hjn (by omega) q hq)
        _ = (∫ q, |F n q.last - F j (q.eval j)| ^ p ∂kernelPathMeasure K s₀ n) +
            4 * ∫ q, ∫ t, |F (n + 1) t - F n q.last| ^ p ∂(K n q.last).toMeasure
              ∂kernelPathMeasure K s₀ n := by
          rw [integral_add (integrable_kernelPathMeasure K hK s₀ n _)
            (integrable_kernelPathMeasure K hK s₀ n _), integral_const_mul]
        _ ≤ _ := by
          rw [Finset.sum_Ico_succ_top hjn]
          linarith [hincrement n hjn (by omega)]

/-- The corresponding complex moment-difference estimate. Its explicit factor
`4 * 2^p` is uniform over the source's range `1 < p ≤ 2`. -/
theorem kernelPath_norm_rpow_sub_le_integrated (K : ℕ → State → PMF State)
    (hK : ∀ k s, (K k s).support.Finite) (s₀ : State) (F : ℕ → State → ℂ)
    (B : ℕ → ℝ) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (N j : ℕ) (hj : j ≤ N)
    (hmean : ∀ k, j ≤ k → k < N → ∀ q ∈ (kernelPathLaw K s₀ k).support,
      (∫ t, F (k + 1) t ∂(K k q.last).toMeasure) = F k q.last)
    (hincrement : ∀ k, j ≤ k → k < N →
      (∫ q, ∫ t, ‖F (k + 1) t - F k q.last‖ ^ p ∂(K k q.last).toMeasure
        ∂kernelPathMeasure K s₀ k) ≤ B k) :
    (∫ q, ‖F N q.last - F j (q.eval j)‖ ^ p ∂kernelPathMeasure K s₀ N) ≤
      (4 * (2 : ℝ) ^ p) * ∑ k ∈ Finset.Ico j N, B k := by
  have hnonneg : 0 ≤ p := by linarith
  have hcoord (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, |L z| ≤ ‖z‖) :
      (∫ q, |L (F N q.last) - L (F j (q.eval j))| ^ p ∂kernelPathMeasure K s₀ N) ≤
        4 * ∑ k ∈ Finset.Ico j N, B k := by
    apply kernelPath_abs_rpow_sub_le_integrated K hK s₀ (fun k s ↦ L (F k s)) B hp hp2 N j hj
    · intro k hjk hk q hq
      rw [L.integral_comp_comm (FinitePMF.integrable_of_finite_support _ (hK k q.last) _),
        hmean k hjk hk q hq]
    · intro k hjk hk
      refine le_trans ?_ (hincrement k hjk hk)
      apply integral_mono (integrable_kernelPathMeasure K hK s₀ k _)
        (integrable_kernelPathMeasure K hK s₀ k _)
      intro q
      apply integral_mono (FinitePMF.integrable_of_finite_support _ (hK k q.last) _)
        (FinitePMF.integrable_of_finite_support _ (hK k q.last) _)
      intro t
      change |L (F (k + 1) t) - L (F k q.last)| ^ p ≤ ‖F (k + 1) t - F k q.last‖ ^ p
      rw [← map_sub]
      exact Real.rpow_le_rpow (abs_nonneg _) (hL _) hnonneg
  have hre := hcoord RCLike.reCLM RCLike.abs_re_le_norm
  have him := hcoord RCLike.imCLM RCLike.abs_im_le_norm
  have hC : 0 ≤ (2 : ℝ) ^ (p - 1) := Real.rpow_nonneg (by norm_num) _
  have htwo : (2 : ℝ) ^ (p - 1) * 2 = (2 : ℝ) ^ p := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring
  calc
    _ ≤ ∫ q, (2 : ℝ) ^ (p - 1) *
        (|RCLike.re (F N q.last - F j (q.eval j))| ^ p +
          |RCLike.im (F N q.last - F j (q.eval j))| ^ p) ∂kernelPathMeasure K s₀ N :=
      integral_mono (integrable_kernelPathMeasure K hK s₀ N _)
        (integrable_kernelPathMeasure K hK s₀ N _)
        (fun q ↦ FinitePMF.complex_norm_rpow_le_parts _ hp.le)
    _ = (2 : ℝ) ^ (p - 1) *
        ((∫ q, |RCLike.re (F N q.last) - RCLike.re (F j (q.eval j))| ^ p
            ∂kernelPathMeasure K s₀ N) +
          ∫ q, |RCLike.im (F N q.last) - RCLike.im (F j (q.eval j))| ^ p
            ∂kernelPathMeasure K s₀ N) := by
      simp_rw [map_sub]
      rw [integral_const_mul, integral_add (integrable_kernelPathMeasure K hK s₀ N _)
        (integrable_kernelPathMeasure K hK s₀ N _)]
    _ ≤ (2 : ℝ) ^ (p - 1) * (2 * (4 * ∑ k ∈ Finset.Ico j N, B k)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [RCLike.reCLM_apply, RCLike.imCLM_apply, two_mul] using add_le_add hre him
    _ = _ := by rw [← mul_assoc, htwo]; ring

end HeightPaper.Model
