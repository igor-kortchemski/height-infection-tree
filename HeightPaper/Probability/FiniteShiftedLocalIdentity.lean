module

public import HeightPaper.Probability.FiniteShiftedProfileMovingModulus
public import HeightPaper.Probability.FiniteLocalProfileMovingTime
public import HeightPaper.Probability.FiniteNormalizerPrefixModulus
public import HeightPaper.Probability.ProfileCouplingComparison

/-!
# Exact finite-to-local identity for shifted analytic profiles

When the coupled event words and cutoff agree through the observation time,
the finite and local shifted normalizers have the same prefix factor. Their
remaining difference is the unshifted profile difference.
-/

@[expose] public section

open MeasureTheory Set

namespace HeightPaper.CountCoupling

open Model

theorem finiteShiftedRankProfile_eq_unshifted_mul_prefix
    (l : ℝ) (n H : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ))
    (k : ℕ) (z : ℂ)
    (hJk : finiteSafeCutoff l n H q.1 ≤ k)
    (hz : 1 ≤ (Complex.exp z).re) :
    finiteShiftedRankProfile l n H q k z =
      finiteUnshiftedRankProfile l n q k z *
        prescribedNormalizer (Complex.exp z) (finiteBirth l n q.1) 1
          (finiteSafeCutoff l n H q.1) := by
  exact prescribedNormalizedProfile_eq_unshifted_mul_prefix hz
    (finiteBirth l n q.1) (initial n)
    (rankState (finiteBirth l n q.1) (initial n) q.2 k) hJk

theorem localRankProfileLimit_eq_unshifted_mul_prefix
    (l : ℝ) (q : (ℕ → ℝ) × (ℕ → ℝ)) (z : ℂ)
    (hz : 1 ≤ (Complex.exp z).re) :
    localRankProfileLimit l 0 q z =
      localUnshiftedRankProfileLimit l 0 q z *
        localProfilePrefixNormalizer l q.1 z := by
  have hp : localProfilePrefixNormalizer l q.1 z ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt (zero_lt_one.trans_le
      (one_le_norm_prescribedNormalizer hz (localBirth l q.1) 1
        (localSafeCutoff l q.1)))
  unfold localUnshiftedRankProfileLimit
  exact (div_mul_cancel₀ _ hp).symm

theorem finite_local_profilePrefixNormalizer_eq
    (l : ℝ) (n H : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ)) (z : ℂ)
    (hJ : finiteSafeCutoff l n H q.1 = localSafeCutoff l q.1)
    (hwalk : ∀ k ≤ localSafeCutoff l q.1,
      finiteWalk l n q.1 k = localWalk l q.1 k) :
    prescribedNormalizer (Complex.exp z) (finiteBirth l n q.1) 1
      (finiteSafeCutoff l n H q.1) =
        localProfilePrefixNormalizer l q.1 z := by
  rw [hJ]
  unfold localProfilePrefixNormalizer
  have he := finiteBirth_eq_localBirth_of_walk_prefix hwalk
  simpa only [prescribedNormalizerFrom_zero] using
    prescribedNormalizerFrom_congr_prefix (Complex.exp z) 1 0 he le_rfl

/-- On the exact word/cutoff coupling event, the shifted finite-to-local
error is the unshifted error multiplied by one common prefix product. -/
theorem finiteShiftedRankProfile_sub_localLimit_eq_unshifted_sub_mul_prefix
    (l : ℝ) (n H : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ))
    (k : ℕ) (z : ℂ)
    (hJk : finiteSafeCutoff l n H q.1 ≤ k)
    (hJ : finiteSafeCutoff l n H q.1 = localSafeCutoff l q.1)
    (hwalk : ∀ i ≤ localSafeCutoff l q.1,
      finiteWalk l n q.1 i = localWalk l q.1 i)
    (hz : 1 ≤ (Complex.exp z).re) :
    finiteShiftedRankProfile l n H q k z - localRankProfileLimit l 0 q z =
      (finiteUnshiftedRankProfile l n q k z -
        localUnshiftedRankProfileLimit l 0 q z) *
          localProfilePrefixNormalizer l q.1 z := by
  rw [finiteShiftedRankProfile_eq_unshifted_mul_prefix l n H q k z hJk hz,
    localRankProfileLimit_eq_unshifted_mul_prefix l q z hz,
    finite_local_profilePrefixNormalizer_eq l n H q z hJ hwalk]
  ring

/-- A bounded cutoff turns unshifted convergence into shifted convergence
with an explicit deterministic multiplier at a positive real tilt. -/
theorem finiteShiftedRankProfile_sub_localLimit_norm_le
    (l : ℝ) (n H : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ))
    (k K : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hJk : finiteSafeCutoff l n H q.1 ≤ k)
    (hJK : localSafeCutoff l q.1 ≤ K)
    (hJ : finiteSafeCutoff l n H q.1 = localSafeCutoff l q.1)
    (hwalk : ∀ i ≤ localSafeCutoff l q.1,
      finiteWalk l n q.1 i = localWalk l q.1 i) :
    ‖finiteShiftedRankProfile l n H q k (x : ℂ) -
      localRankProfileLimit l 0 q (x : ℂ)‖ ≤
      (2 + Real.exp x) ^ K *
        ‖finiteUnshiftedRankProfile l n q k (x : ℂ) -
          localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ := by
  have hxexp : 1 ≤ (Complex.exp (x : ℂ)).re := by
    simpa only [Complex.exp_ofReal_re] using Real.one_le_exp hx
  rw [finiteShiftedRankProfile_sub_localLimit_eq_unshifted_sub_mul_prefix
    l n H q k (x : ℂ) hJk hJ hwalk hxexp, norm_mul]
  have hP : ‖localProfilePrefixNormalizer l q.1 (x : ℂ)‖ ≤
      (2 + Real.exp x) ^ K := by
    unfold localProfilePrefixNormalizer
    calc
      _ ≤ (2 + ‖Complex.exp (x : ℂ)‖) ^ localSafeCutoff l q.1 :=
        norm_prescribedNormalizer_le _ _ _ _
      _ = (2 + Real.exp x) ^ localSafeCutoff l q.1 := by
        rw [Complex.norm_exp]
        simp
      _ ≤ (2 + Real.exp x) ^ K :=
        pow_le_pow_right₀ (by linarith [Real.exp_pos x]) hJK
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hP
    (norm_nonneg (finiteUnshiftedRankProfile l n q k (x : ℂ) -
      localUnshiftedRankProfileLimit l 0 q (x : ℂ)))

end HeightPaper.CountCoupling
