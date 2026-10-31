module

public import HeightPaper.Probability.LocalProfileMoments
public import HeightPaper.Model.ProfileCutoffMoment

/-!
# Nonnegative local profile limits with positive mean

At a nonnegative real tilt, the finite normalized profiles are real and
nonnegative. Their mean is exactly the positive normalizer of the retained
cutoff prefix. Lp convergence preserves this mean under the actual prescribed
trajectory law.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace HeightPaper.Model

/-- Real positive weights give a real nonnegative normalized profile, including
on states with no active vertices under the totalized division convention. -/
theorem prescribedNormalizedProfile_ofReal_nonneg {v : ℝ} (hv : 1 ≤ v)
    (events : ℕ → Bool) (s₀ : State) (J k : ℕ) (s : State) :
    (prescribedNormalizedProfile (v : ℂ) events s₀ J k s).im = 0 ∧
      0 ≤ (prescribedNormalizedProfile (v : ℂ) events s₀ J k s).re := by
  have hnonneg : 0 ≤ activeWeight v s := by
    unfold activeWeight
    exact Finset.sum_nonneg (fun _ _ ↦ pow_nonneg (zero_le_one.trans hv) _)
  rw [prescribedNormalizedProfile, normalizedActiveWeight_ofReal, prescribedNormalizerFrom_ofReal,
    ← Complex.ofReal_div]
  refine ⟨Complex.ofReal_im _, ?_⟩
  simpa only [Complex.ofReal_re] using
    (div_nonneg (div_nonneg hnonneg (Nat.cast_nonneg _))
      (realNormalizerFrom_pos hv events (infectious s₀) J k).le)

/-- The exact finite expectation retains the normalizer before the cutoff. -/
theorem prescribedTrajectory_profile_integral_ofReal {v : ℝ} (hv : 1 ≤ v)
    (events : ℕ → Bool) (n J k : ℕ) (hJk : J ≤ k)
    (hpos : ∀ i ≤ k, 0 < prescribedWalk events 1 i) :
    (∫ ω, prescribedNormalizedProfile (v : ℂ) events (initial n) J k (ω k)
      ∂prescribedTrajectoryMeasure events (initial n)) = (realNormalizer v events 1 J : ℂ) := by
  have heq := kernelTrajectory_integral_prefix (fun i ↦ prescribedStep (events i)) (initial n) k
    (fun q ↦ prescribedNormalizedProfile (v : ℂ) events (initial n) J k q.last)
  simp only [trajectoryPrefix_last] at heq
  rw [prescribedTrajectoryMeasure, heq]
  simp only [prescribedNormalizedProfile, infectious_initial]
  rw [integral_div, prescribedPath_normalized_integral (v : ℂ) events (initial n) k
    (by simpa only [infectious_initial] using hpos), normalizedActiveWeight_initial, one_mul,
    prescribedNormalizer_ofReal, infectious_initial, prescribedNormalizerFrom_ofReal,
    realNormalizer_split v events 1 hJk,
    Complex.ofReal_mul]
  exact mul_div_cancel_right₀ _ (by exact_mod_cast (realNormalizerFrom_pos hv events 1 J k).ne')

/-- Any almost-sure and Lp limit has the exact positive finite-prefix mean;
nonnegativity follows from the real finite-time profiles. -/
theorem prescribedTrajectory_profile_limit_nonneg_mean {v p : ℝ} (hv : 1 ≤ v) (hp : 1 ≤ p)
    (events : ℕ → Bool) (n J : ℕ)
    (hpos : ∀ i, 0 < prescribedWalk events 1 i)
    (F : (ℕ → State) → ℂ)
    (hlim : ∀ᵐ ω ∂prescribedTrajectoryMeasure events (initial n),
      Tendsto (fun k ↦ prescribedNormalizedProfile (v : ℂ) events (initial n) J (J + k)
        (ω (J + k))) atTop (𝓝 (F ω)))
    (hLp : Tendsto (fun k ↦ eLpNorm
      ((fun ω ↦ prescribedNormalizedProfile (v : ℂ) events (initial n) J (J + k)
        (ω (J + k))) - F) (ENNReal.ofReal p)
        (prescribedTrajectoryMeasure events (initial n))) atTop (𝓝 0)) :
    (∀ᵐ ω ∂prescribedTrajectoryMeasure events (initial n), (F ω).im = 0 ∧ 0 ≤ (F ω).re) ∧
      (∫ ω, F ω ∂prescribedTrajectoryMeasure events (initial n)) = (realNormalizer v events 1 J : ℂ) ∧
      0 < (∫ ω, F ω ∂prescribedTrajectoryMeasure events (initial n)).re := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hL1 : Tendsto (fun k ↦ eLpNorm
      ((fun ω ↦ prescribedNormalizedProfile (v : ℂ) events (initial n) J (J + k)
        (ω (J + k))) - F) 1 (prescribedTrajectoryMeasure events (initial n))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLp
      (fun _ ↦ zero_le) (fun _ ↦ eLpNorm_le_eLpNorm_of_exponent_le hp1)
  have hint (k : ℕ) : Integrable (fun ω ↦ prescribedNormalizedProfile (v : ℂ) events
      (initial n) J (J + k) (ω (J + k))) (prescribedTrajectoryMeasure events (initial n)) := by
    have hh := prescribedTrajectory_profile_memLp (v : ℂ) events (initial n) J k (p := 1) zero_lt_one
    exact memLp_one_iff_integrable.mp (by simpa using hh)
  have ht := tendsto_integral_of_L1' F (Eventually.of_forall hint) hL1
  have heq : (∫ ω, F ω ∂prescribedTrajectoryMeasure events (initial n)) =
      (realNormalizer v events 1 J : ℂ) := by
    apply tendsto_nhds_unique ht
    convert tendsto_const_nhds using 1
    funext k
    exact prescribedTrajectory_profile_integral_ofReal hv events n J (J + k)
      (Nat.le_add_right _ _) (fun i _ ↦ hpos i)
  refine ⟨?_, heq, ?_⟩
  · filter_upwards [hlim] with ω hω
    have him := Complex.continuous_im.continuousAt.tendsto.comp hω
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hω
    have hi0 : (F ω).im = 0 := by
      apply tendsto_nhds_unique him
      convert tendsto_const_nhds using 1
      funext k
      exact (prescribedNormalizedProfile_ofReal_nonneg hv events (initial n) J (J + k) (ω (J + k))).1
    exact ⟨hi0, le_of_tendsto_of_tendsto' tendsto_const_nhds hre
      (fun k ↦ (prescribedNormalizedProfile_ofReal_nonneg hv events (initial n) J (J + k) (ω (J + k))).2)⟩
  · rw [heq, Complex.ofReal_re]
    exact zero_lt_one.trans_le (one_le_realNormalizer hv events 1 J)

end HeightPaper.Model

namespace HeightPaper.CountCoupling

/-- The actual local law supplies a nonnegative Lp limit with strictly positive
mean at every real tilt inside the positive profile region. -/
theorem localProfile_ae_exists_lp_limit_nonneg_mean {l x : ℝ} (hl : 1 < l)
    (hx : 0 < x) (hxr : x < profileRoot l) :
    ∃ p ∈ Set.Ioo (1 : ℝ) 2, ∀ᵐ u ∂uniformLaw,
      (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
      ∃ F : (ℕ → Model.State) → ℂ, Measurable F ∧
        MemLp F (ENNReal.ofReal p)
          (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
        (∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
          Tendsto (fun k ↦ Model.prescribedNormalizedProfile (Complex.exp (x : ℂ))
            (localBirth l u) (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
            (ω (localSafeCutoff l u + k))) atTop (𝓝 (F ω))) ∧
        Tendsto (fun k ↦ eLpNorm
          ((fun ω ↦ Model.prescribedNormalizedProfile (Complex.exp (x : ℂ))
            (localBirth l u) (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
            (ω (localSafeCutoff l u + k))) - F) (ENNReal.ofReal p)
          (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n))) atTop (𝓝 0) ∧
        (∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
          (F ω).im = 0 ∧ 0 ≤ (F ω).re) ∧
        (∫ ω, F ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) =
          (Model.realNormalizer (Real.exp x) (localBirth l u) 1 (localSafeCutoff l u) : ℂ) ∧
        0 < (∫ ω, F ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)).re := by
  obtain ⟨p, hp, η, hη, r, hr, hwindow⟩ := exists_localProfile_moment_disk hl hx hxr
  have hz := hwindow l le_rfl (x : ℂ) (by simpa using hr)
  have hexp : complexProfileMomentExponent l (x : ℂ) p < -1 := by linarith [hz.2.2.2]
  refine ⟨p, hp, ?_⟩
  filter_upwards [localProfile_ae_exists_lp_limit hl] with u hu
  intro hs n
  obtain ⟨F, hF, hmem, hlim, hLp⟩ := hu hs n (x : ℂ) p (by simpa using hx.le)
    (by simpa using (show x < 2 * profileRoot l by linarith [profileRoot_pos hl]))
    hp.1 hp.2.le hz.2.2.1 hexp
  have hpos : ∀ i, 0 < Model.prescribedWalk (localBirth l u) 1 i := by
    intro i
    apply prescribedWalk_local_pos (H := i) _ le_rfl
    intro j _
    exact_mod_cast hs j
  have hm := Model.prescribedTrajectory_profile_limit_nonneg_mean
    (Real.one_le_exp_iff.mpr hx.le) hp.1.le (localBirth l u) n (localSafeCutoff l u) hpos F
    (by simpa only [Complex.ofReal_exp] using hlim)
    (by simpa only [Complex.ofReal_exp] using hLp)
  exact ⟨F, hF, hmem, hlim, hLp, hm⟩

/-- Every cofinal almost-sure version of the real profile limit has the same
positive mean. This includes the canonical analytic limit obtained on dyadic
times, without assuming Lp convergence for that second version. -/
theorem localProfile_ae_subsequence_limit_nonneg_mean {l x : ℝ} (hl : 1 < l)
    (hx : 0 < x) (hxr : x < profileRoot l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
      ∀ times : ℕ → ℕ, Tendsto times atTop atTop → ∀ F : (ℕ → Model.State) → ℂ,
      (∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
        Tendsto (fun k ↦ Model.prescribedNormalizedProfile (Complex.exp (x : ℂ))
          (localBirth l u) (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + times k)
          (ω (localSafeCutoff l u + times k))) atTop (𝓝 (F ω))) →
      (∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
        (F ω).im = 0 ∧ 0 ≤ (F ω).re) ∧
      (∫ ω, F ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) =
        (Model.realNormalizer (Real.exp x) (localBirth l u) 1 (localSafeCutoff l u) : ℂ) ∧
      0 < (∫ ω, F ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)).re := by
  obtain ⟨p, hp, hword⟩ := localProfile_ae_exists_lp_limit_nonneg_mean hl hx hxr
  filter_upwards [hword] with u hu
  intro hs n times htimes F hF
  obtain ⟨G, _, _, hG, _, hnonneg, hmean, hposmean⟩ := hu hs n
  have heq : F =ᵐ[Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)] G := by
    filter_upwards [hF, hG] with ω hωF hωG
    exact tendsto_nhds_unique hωF (hωG.comp htimes)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [heq, hnonneg] with ω hωeq hωnonneg
    simpa only [hωeq] using hωnonneg
  · exact (integral_congr_ae heq).trans hmean
  · rwa [integral_congr_ae heq]

end HeightPaper.CountCoupling

namespace MeasureTheory

/-- For a nonnegative real-valued complex random variable, positive mean rules
out the probability-one zero event in a zero-one alternative. -/
theorem ae_re_pos_of_nonneg_mean_pos_zero_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℂ) (hF : Measurable F)
    (hnonneg : ∀ᵐ ω ∂μ, (F ω).im = 0 ∧ 0 ≤ (F ω).re)
    (hmean : 0 < (∫ ω, F ω ∂μ).re)
    (hzeroone : μ {ω | F ω = 0} = 0 ∨ μ {ω | F ω = 0} = 1) :
    ∀ᵐ ω ∂μ, 0 < (F ω).re := by
  have hzero : μ {ω | F ω = 0} = 0 := by
    rcases hzeroone with hz | hz
    · exact hz
    · have hae : F =ᵐ[μ] 0 :=
        (mem_ae_iff_prob_eq_one (measurableSet_eq_fun hF measurable_const)).mpr hz
      have hi : (∫ ω, F ω ∂μ) = 0 := by
        rw [integral_congr_ae hae]
        simp
      simp only [hi, Complex.zero_re, lt_self_iff_false] at hmean
  have hne : ∀ᵐ ω ∂μ, F ω ≠ 0 := by
    rw [ae_iff]
    simpa using hzero
  filter_upwards [hnonneg, hne] with ω hω hωne
  by_contra hh
  have hre : (F ω).re = 0 := le_antisymm (le_of_not_gt hh) hω.2
  apply hωne
  apply Complex.ext
  · simpa using hre
  · simpa using hω.1

end MeasureTheory
