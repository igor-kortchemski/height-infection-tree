module

public import HeightPaper.Model.ContinuousProfileMartingale
public import HeightPaper.Probability.MartingaleSubsequence

/-!
# Full-time almost-sure analytic profile convergence

Scalar convergence of distances to countably many anchors upgrades the
existing dyadic uniform convergence. Boundary moment estimates supply
uniform L1 bounds for each fixed anchor on the actual history law.
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology

namespace HeightPaper.Model

theorem continuousProfile_integral_norm_sub_le
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) (c : ℂ) (r R : ℝ)
    (hr : 0 ≤ r) (hrR : r < R)
    (hCr : ∀ k ≥ J, ∀ z ∈ closedBall c r,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0)
    (hCR : ∀ k ≥ J, ∀ z ∈ closedBall c R,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0)
    (j N : ℕ) (hJj : J ≤ j) (hjN : j ≤ N)
    (p : ℝ) (hp : 1 ≤ p) (B : ℝ) (_hB : 0 ≤ B)
    (hbound : ∀ z ∈ sphere c R,
      (∫ ω, ‖prescribedNormalizedProfile (Complex.exp z) events s₀ J N (ω N) -
        prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)‖ ^ p
          ∂prescribedTrajectoryMeasure events s₀) ≤ B) :
    (∫ ω, ‖continuousPrescribedProfile events s₀ J c r hCr N (ω N) -
      continuousPrescribedProfile events s₀ J c r hCr j (ω j)‖
        ∂prescribedTrajectoryMeasure events s₀) ≤
      (R / (2 * Real.pi * (R - r))) * (2 * Real.pi * B ^ p⁻¹) := by
  let K := fun k ↦ prescribedStep (events k)
  let μ := prescribedTrajectoryMeasure events s₀
  let G := continuousPrescribedProfile events s₀ J c r hCr
  let H (ω : ℕ → State) (z : ℂ) :=
    prescribedNormalizedProfile (Complex.exp z) events s₀ J N (ω N) -
      prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)
  let Q (q : FinitePath N) (z : ℂ) :=
    prescribedNormalizedProfile (Complex.exp z) events s₀ J N q.last -
      prescribedNormalizedProfile (Complex.exp z) events s₀ J j (q.eval j)
  have hR : 0 < R := hr.trans_lt hrR
  have hQ (ω : ℕ → State) : Q (trajectoryPrefix N ω) = H ω := by
    funext z
    simp only [Q, H, trajectoryPrefix_last, trajectoryPrefix_eval _ _ _ hjN]
  have hd (s t : State) : DifferentiableOn ℂ
      (fun z ↦ prescribedNormalizedProfile (Complex.exp z) events s₀ J N s -
        prescribedNormalizedProfile (Complex.exp z) events s₀ J j t) (closedBall c R) :=
    (differentiableOn_prescribedNormalizedProfile_exp events s₀ s J N
      (hCR N (hJj.trans hjN))).sub
      (differentiableOn_prescribedNormalizedProfile_exp events s₀ t J j (hCR j hJj))
  have hi : Integrable (fun ω ↦ circleL1 c R (H ω)) μ := by
    have ht := kernelTrajectory_integrable_prefix K
      (fun k s ↦ finite_support_prescribedStep (events k) s) s₀ N
      (fun q ↦ circleL1 c R (Q q))
    simpa only [hQ, μ, prescribedTrajectoryMeasure, K] using ht
  have hmean : (∫ ω, circleL1 c R (H ω) ∂μ) ≤ 2 * Real.pi * B ^ p⁻¹ := by
    have ht := kernelTrajectory_integral_prefix K s₀ N (fun q ↦ circleL1 c R (Q q))
    simp only [hQ] at ht
    change (∫ ω, circleL1 c R (H ω)
      ∂FinitePMF.kernelTrajectoryMeasure K (fun _ ↦ measurable_state _) s₀) ≤ _
    rw [ht]
    apply finitePMF_integral_circleL1_le _
      (finite_support_kernelPathLaw K (fun k s ↦ finite_support_prescribedStep (events k) s) s₀ N)
      c R Q
    · intro q _
      rw [abs_of_pos hR]
      exact (hd q.last (q.eval j)).continuousOn.mono sphere_subset_closedBall
    · intro z hz
      have ht' := kernelTrajectory_integral_prefix K s₀ N (fun q ↦ ‖Q q z‖)
      simp only [hQ] at ht'
      change (∫ q, ‖Q q z‖ ∂kernelPathMeasure K s₀ N) ≤ _
      rw [← ht']
      have hLp (k : ℕ) (hk : J ≤ k) : MemLp
          (fun ω ↦ prescribedNormalizedProfile (Complex.exp z) events s₀ J k (ω k))
          (ENNReal.ofReal p) μ := by
        have ht'' := prescribedTrajectory_profile_memLp (Complex.exp z) events s₀ J
          (k - J) (lt_of_lt_of_le zero_lt_one hp)
        simpa only [Nat.add_sub_of_le hk, μ] using ht''
      exact (integral_norm_le_moment_root μ hp
        ((hLp N (hJj.trans hjN)).sub (hLp j hJj))).trans
        (Real.rpow_le_rpow (integral_nonneg (fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _))
          (hbound z (by simpa only [abs_of_pos hR] using hz))
          (inv_nonneg.mpr (zero_le_one.trans hp)))
  let A := R / (2 * Real.pi * (R - r))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hnorm (ω : ℕ → State) : ‖G N (ω N) - G j (ω j)‖ ≤ A * circleL1 c R (H ω) := by
    apply (ContinuousMap.norm_le _ (mul_nonneg hA (circleL1_nonneg _ _ _))).mpr
    intro z
    exact norm_le_circleL1 hr hrR (hd (ω N) (ω j)) z.property
  have hiG : Integrable (fun ω ↦ ‖G N (ω N) - G j (ω j)‖) μ := by
    have ht := kernelTrajectory_integrable_prefix K
      (fun k s ↦ finite_support_prescribedStep (events k) s) s₀ N
      (fun q ↦ ‖G N q.last - G j (q.eval j)‖)
    simpa only [trajectoryPrefix_last, trajectoryPrefix_eval _ _ _ hjN,
      μ, prescribedTrajectoryMeasure, K] using ht
  exact (integral_mono hiG (hi.const_mul A) hnorm).trans
    (by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hmean hA)

theorem prescribedTrajectory_ae_full_time_of_dyadic
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) (c : ℂ) (r R : ℝ)
    (hr : 0 ≤ r) (hrR : r < R)
    (hCr : ∀ k ≥ J, ∀ z ∈ closedBall c r,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0)
    (hCR : ∀ k ≥ J, ∀ z ∈ closedBall c R,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0)
    (hpos : ∀ i, 0 < prescribedWalk events (infectious s₀) i)
    (p : ℝ) (hp : 1 ≤ p) (D η : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ z ∈ sphere c R, ∀ j N : ℕ, J ≤ j → 1 ≤ j → j ≤ N →
      (∫ ω, ‖prescribedNormalizedProfile (Complex.exp z) events s₀ J N (ω N) -
        prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)‖ ^ p
          ∂prescribedTrajectoryMeasure events s₀) ≤ D * (j : ℝ) ^ (-η)) :
    ∀ᵐ ω ∂prescribedTrajectoryMeasure events s₀,
      ∀ L : C(↥(closedBall c r), ℂ),
        Tendsto (fun m ↦ continuousPrescribedProfile events s₀ J c r hCr
          (J + 2 ^ m) (ω (J + 2 ^ m))) atTop (𝓝 L) →
        Tendsto (fun k ↦ continuousPrescribedProfile events s₀ J c r hCr
          (J + k) (ω (J + k))) atTop (𝓝 L) := by
  let G := continuousPrescribedProfile events s₀ J c r hCr
  let μ := prescribedTrajectoryMeasure events s₀
  have hdist (m : ℕ) : ∀ᵐ ω ∂μ, ∃ b : ℝ,
      Tendsto (fun k ↦ dist (G (J + k) (ω (J + k)))
        (G (J + 2 ^ m) (ω (J + 2 ^ m)))) atTop (𝓝 b) := by
    let j := J + 2 ^ m
    have hj : J ≤ j := Nat.le_add_right _ _
    have hj1 : 1 ≤ j := by
      dsimp [j]
      have := pow_pos (by omega : (0 : ℕ) < 2) m
      omega
    let B := (R / (2 * Real.pi * (R - r))) *
      (2 * Real.pi * (D * (j : ℝ) ^ (-η)) ^ p⁻¹)
    have hm := continuousPrescribedProfile_martingale events s₀ J c r hCr hpos j hj
    have hb (k : ℕ) : (∫ ω, ‖G (j + k) (ω (j + k)) - G j (ω j)‖ ∂μ) ≤ B := by
      apply continuousProfile_integral_norm_sub_le events s₀ J c r R hr hrR hCr hCR
        j (j + k) hj (Nat.le_add_right _ _) p hp (D * (j : ℝ) ^ (-η))
        (mul_nonneg hD (Real.rpow_nonneg (by positivity) _))
      intro z hz
      exact hbound z hz j (j + k) hj hj1 (Nat.le_add_right _ _)
    filter_upwards [martingale_ae_exists_norm_sub_initial_limit μ
      (FinitePMF.trajectoryFiltrationFrom j)
      (fun k ω ↦ G (j + k) (ω (j + k))) hm B (by simpa using hb)] with ω hω
    obtain ⟨b, hb⟩ := hω
    refine ⟨b, ?_⟩
    apply (tendsto_add_atTop_iff_nat (2 ^ m)).mp
    simpa only [dist_eq_norm, j, Nat.add_zero, Nat.zero_add, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hb
  exact ae_tendsto_of_subsequence_of_dist_limits μ
    (fun k ω ↦ G (J + k) (ω (J + k))) (fun m ↦ 2 ^ m)
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)) hdist

end HeightPaper.Model
