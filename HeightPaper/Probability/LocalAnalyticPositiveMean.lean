module

public import HeightPaper.Probability.LocalProfilePositiveMean
public import HeightPaper.Probability.LocalAnalyticDomain

/-!
# Positive mean of the canonical analytic local profile

The canonical analytic limit and the Lp limit agree almost surely at each
positive real tilt, by uniqueness along their common dyadic subsequence.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace HeightPaper.CountCoupling

/-- One almost-sure set of local words supplies the positive mean for every
positive real tilt and every cofinal almost-sure version of its profile limit. -/
theorem localProfile_ae_subsequence_limit_nonneg_mean_all_real {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
      ∀ x : ℝ, 0 < x → x < profileRoot l → ∀ n : ℕ,
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
  filter_upwards [localProfile_ae_exists_lp_limit hl] with u hu
  intro hs x hx hxr n times htimes F hF
  obtain ⟨p, hp, η, hη, r, hr, hwindow⟩ := exists_localProfile_moment_disk hl hx hxr
  have hz := hwindow l le_rfl (x : ℂ) (by simpa using hr)
  have hexp : complexProfileMomentExponent l (x : ℂ) p < -1 := by linarith [hz.2.2.2]
  obtain ⟨G, _, _, hG, hLp⟩ := hu hs n (x : ℂ) p (by simpa using hx.le)
    (by simpa using (show x < 2 * profileRoot l by linarith [profileRoot_pos hl]))
    hp.1 hp.2.le hz.2.2.1 hexp
  have hpos : ∀ i, 0 < Model.prescribedWalk (localBirth l u) 1 i := by
    intro i
    apply prescribedWalk_local_pos (H := i) _ le_rfl
    intro j _
    exact_mod_cast hs j
  have hm := Model.prescribedTrajectory_profile_limit_nonneg_mean
    (Real.one_le_exp_iff.mpr hx.le) hp.1.le (localBirth l u) n (localSafeCutoff l u) hpos G
    (by simpa only [Complex.ofReal_exp] using hG)
    (by simpa only [Complex.ofReal_exp] using hLp)
  have heq : F =ᵐ[Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)] G := by
    filter_upwards [hF, hG] with ω hωF hωG
    exact tendsto_nhds_unique hωF (hωG.comp htimes)
  refine ⟨?_, (integral_congr_ae heq).trans hm.2.1, ?_⟩
  · filter_upwards [heq, hm.1] with ω hωeq hωnonneg
    simpa only [hωeq] using hωnonneg
  · rw [integral_congr_ae heq]
    exact hm.2.2

/-- The same canonical analytic limit used for locally uniform convergence is
real nonnegative at a fixed positive real tilt and has the exact positive mean
of the retained cutoff prefix. -/
theorem localAnalyticProfileLimit_ae_nonneg_mean {l x : ℝ} (hl : 1 < l)
    (hx : 0 < x) (hxr : x < profileRoot l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
      (∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
        (localAnalyticProfileLimit l n u ω (x : ℂ)).im = 0 ∧
          0 ≤ (localAnalyticProfileLimit l n u ω (x : ℂ)).re) ∧
      (∫ ω, localAnalyticProfileLimit l n u ω (x : ℂ)
        ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) =
        (Model.realNormalizer (Real.exp x) (localBirth l u) 1 (localSafeCutoff l u) : ℂ) ∧
      0 < (∫ ω, localAnalyticProfileLimit l n u ω (x : ℂ)
        ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)).re := by
  obtain ⟨R, hR, hcanonical⟩ := localProfile_ae_canonical_analytic_limit hl hx hxr
  filter_upwards [hcanonical l le_rfl, localProfile_ae_subsequence_limit_nonneg_mean hl hx hxr]
    with u hu hmean
  intro hs n
  apply hmean hs n (fun m ↦ 2 ^ m)
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
    (fun ω ↦ localAnalyticProfileLimit l n u ω (x : ℂ))
  filter_upwards [(hu hs n).1] with ω hω
  exact (hω 0 le_rfl hR).1.tendsto_at (by simp)

/-- The outer exceptional set is independent of the real tilt: every good
local word has the same canonical profile with a positive conditional mean at
every point of the positive profile interval. -/
theorem localAnalyticProfileLimit_ae_nonneg_mean_all_real {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
      ∀ x : ℝ, 0 < x → x < profileRoot l → ∀ n : ℕ,
      (∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
        (localAnalyticProfileLimit l n u ω (x : ℂ)).im = 0 ∧
          0 ≤ (localAnalyticProfileLimit l n u ω (x : ℂ)).re) ∧
      (∫ ω, localAnalyticProfileLimit l n u ω (x : ℂ)
        ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) =
        (Model.realNormalizer (Real.exp x) (localBirth l u) 1 (localSafeCutoff l u) : ℂ) ∧
      0 < (∫ ω, localAnalyticProfileLimit l n u ω (x : ℂ)
        ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)).re := by
  filter_upwards [localProfile_ae_canonical_analytic_limit_all_real hl,
    localProfile_ae_subsequence_limit_nonneg_mean_all_real hl] with u hu hmean
  intro hs x hx hxr n
  obtain ⟨R, hR, hcanonical⟩ := hu hs x hx hxr
  apply hmean hs x hx hxr n (fun m ↦ 2 ^ m)
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
    (fun ω ↦ localAnalyticProfileLimit l n u ω (x : ℂ))
  filter_upwards [(hcanonical n).1] with ω hω
  exact (hω 0 le_rfl hR).1.tendsto_at (by simp)

end HeightPaper.CountCoupling
