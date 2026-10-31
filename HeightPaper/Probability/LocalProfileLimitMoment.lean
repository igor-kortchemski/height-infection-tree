module

public import HeightPaper.Model.ProfileLimitMomentBound
public import HeightPaper.Probability.LocalProfileMomentTightness
public import HeightPaper.Probability.LocalAnalyticProfile
public import HeightPaper.Model.RankProfileBound
public import HeightPaper.Probability.UniformParentLaw

/-!
# Conditional moments of the canonical local analytic profile

The common moment envelope for finite local profiles passes to the
specific canonical analytic limit used by the finite-to-local comparison.
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace HeightPaper.Model

theorem prescribedTrajectory_analyticProfileLimit_moment_sub_le
    (events : ℕ → Bool) (n J j : ℕ) (z : ℂ) {p C : ℝ}
    (hp : 0 < p) (hC : 0 ≤ C) (hJj : J ≤ j)
    (hlim : ∀ᵐ ω ∂prescribedTrajectoryMeasure events (initial n),
      Tendsto (fun m ↦ prescribedNormalizedProfile (Complex.exp z) events
        (initial n) J (J + 2 ^ m) (ω (J + 2 ^ m))) atTop
        (𝓝 (prescribedAnalyticProfileLimit events (initial n) J ω z)))
    (hbound : ∀ N ≥ j,
      (∫ ω, ‖prescribedNormalizedProfile (Complex.exp z) events (initial n)
            J N (ω N) -
          prescribedNormalizedProfile (Complex.exp z) events (initial n)
            J j (ω j)‖ ^ p ∂prescribedTrajectoryMeasure events (initial n)) ≤ C) :
    Integrable (fun ω ↦ ‖prescribedAnalyticProfileLimit events (initial n) J ω z -
      prescribedNormalizedProfile (Complex.exp z) events (initial n) J j (ω j)‖ ^ p)
      (prescribedTrajectoryMeasure events (initial n)) ∧
    (∫ ω, ‖prescribedAnalyticProfileLimit events (initial n) J ω z -
      prescribedNormalizedProfile (Complex.exp z) events (initial n) J j (ω j)‖ ^ p
      ∂prescribedTrajectoryMeasure events (initial n)) ≤ C := by
  let μ := prescribedTrajectoryMeasure events (initial n)
  let f : ℕ → (ℕ → State) → ℂ := fun m ω ↦
    prescribedNormalizedProfile (Complex.exp z) events (initial n) J
      (J + 2 ^ m) (ω (J + 2 ^ m))
  let g : (ℕ → State) → ℂ := fun ω ↦
    prescribedAnalyticProfileLimit events (initial n) J ω z
  let h : (ℕ → State) → ℂ := fun ω ↦
    prescribedNormalizedProfile (Complex.exp z) events (initial n) J j (ω j)
  have hf (m : ℕ) : MemLp (f m - h) (ENNReal.ofReal p) μ := by
    have hf₁ := prescribedTrajectory_profile_memLp (Complex.exp z) events
      (initial n) J (2 ^ m) hp
    have hf₂ := prescribedTrajectory_profile_memLp (Complex.exp z) events
      (initial n) J (j - J) hp
    rw [Nat.add_sub_of_le hJj] at hf₂
    exact hf₁.sub hf₂
  have hg : Measurable g := measurable_prescribedAnalyticProfileLimit_eval
    events (initial n) J z
  have hh : Measurable h := by
    simpa only [h, Function.comp_def] using
      (measurable_state (prescribedNormalizedProfile (Complex.exp z) events
        (initial n) J j)).comp
        (measurable_pi_apply (X := fun _ : ℕ ↦ State) j)
  have hb : ∀ᶠ m in atTop, (∫ ω, ‖f m ω - h ω‖ ^ p ∂μ) ≤ C := by
    have ht : Tendsto (fun m : ℕ ↦ J + 2 ^ m) atTop atTop :=
      tendsto_atTop_mono (fun m ↦ Nat.le_add_left (2 ^ m) J)
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    filter_upwards [ht.eventually (eventually_ge_atTop j)] with m hm
    exact hbound (J + 2 ^ m) hm
  exact integral_norm_sub_limit_rpow_le μ hp hC hf hg hh hlim hb

end HeightPaper.Model

namespace HeightPaper.CountCoupling

theorem localAnalyticProfileLimit_moment_sub_le
    (l : ℝ) (u : ℕ → ℝ) (n j : ℕ) (z : ℂ) {p C : ℝ}
    (hp : 0 < p) (hC : 0 ≤ C) (hJj : localSafeCutoff l u ≤ j)
    (hlim : ∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
      Tendsto (fun m ↦ Model.prescribedNormalizedProfile (Complex.exp z)
        (localBirth l u) (Model.initial n) (localSafeCutoff l u)
        (localSafeCutoff l u + 2 ^ m) (ω (localSafeCutoff l u + 2 ^ m))) atTop
        (𝓝 (localAnalyticProfileLimit l n u ω z)))
    (hbound : ∀ N ≥ j, localProfileMomentDifference l u n z p j N ≤ C) :
    Integrable (fun ω ↦ ‖localAnalyticProfileLimit l n u ω z -
      Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
        (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p)
      (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
    (∫ ω, ‖localAnalyticProfileLimit l n u ω z -
      Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
        (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p
      ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤ C := by
  exact Model.prescribedTrajectory_analyticProfileLimit_moment_sub_le
    (localBirth l u) n (localSafeCutoff l u) j z hp hC hJj hlim hbound

end HeightPaper.CountCoupling



namespace HeightPaper.CountCoupling

/-- A deterministic finite-rank bound turns the local limit difference moment
into a conditional moment of the limit itself. -/
theorem localAnalyticProfileLimit_moment_le_real
    (l : ℝ) (u : ℕ → ℝ) (n j : ℕ) {x p C : ℝ}
    (hx : 0 ≤ x) (hp : 1 ≤ p)
    (hsub : Integrable (fun ω ↦ ‖localAnalyticProfileLimit l n u ω (x : ℂ) -
      Model.prescribedNormalizedProfile (Complex.exp (x : ℂ)) (localBirth l u)
        (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p)
        (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
      (∫ ω, ‖localAnalyticProfileLimit l n u ω (x : ℂ) -
        Model.prescribedNormalizedProfile (Complex.exp (x : ℂ)) (localBirth l u)
          (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p
        ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤ C) :
    Integrable (fun ω ↦ ‖localAnalyticProfileLimit l n u ω (x : ℂ)‖ ^ p)
      (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
    (∫ ω, ‖localAnalyticProfileLimit l n u ω (x : ℂ)‖ ^ p
      ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤
      (2 : ℝ) ^ (p - 1) * (C + ((Real.exp x) ^ (j + 1)) ^ p) := by
  let μ := Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)
  let g : (ℕ → Model.State) → ℂ := fun ω ↦ localAnalyticProfileLimit l n u ω (x : ℂ)
  let h : (ℕ → Model.State) → ℂ := fun ω ↦
    Model.prescribedNormalizedProfile (Complex.exp (x : ℂ)) (localBirth l u)
      (Model.initial n) (localSafeCutoff l u) j (ω j)
  have hg : Measurable g := Model.measurable_prescribedAnalyticProfileLimit_eval
    (localBirth l u) (Model.initial n) (localSafeCutoff l u) (x : ℂ)
  have hh : Measurable h := by
    simpa only [h, Function.comp_def] using
      (Model.measurable_state (Model.prescribedNormalizedProfile (Complex.exp (x : ℂ))
        (localBirth l u) (Model.initial n) (localSafeCutoff l u) j)).comp
        (measurable_pi_apply (X := fun _ : ℕ ↦ Model.State) j)
  have hW : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  have hw : ‖Complex.exp (x : ℂ)‖ ≤ Real.exp x := by
    rw [Complex.norm_exp]
    simp
  have hwr : 1 ≤ (Complex.exp (x : ℂ)).re := by
    simpa only [← Complex.ofReal_exp, Complex.ofReal_re] using hW
  have hfinite : ∀ᵐ ω ∂μ, ‖h ω‖ ≤ (Real.exp x) ^ (j + 1) := by
    have hset : MeasurableSet {ω : ℕ → Model.State | ‖h ω‖ ≤ (Real.exp x) ^ (j + 1)} :=
      measurableSet_le hh.norm measurable_const
    rw [show μ = uniformLaw.map (Model.rankState (localBirth l u) (Model.initial n)) from
      (Model.rankTrajectory_law _ _).symm]
    rw [ae_map_iff (Model.measurable_rankTrajectory (localBirth l u)
      (Model.initial n)).aemeasurable hset]
    exact ae_of_all _ (fun v ↦ Model.norm_rank_shifted_profile_le hW hw hwr
      (localBirth l u) n (localSafeCutoff l u) j v)
  exact Model.integral_norm_limit_rpow_le_of_sub_bound μ hp
    (pow_nonneg (Real.exp_pos x).le _) hg hsub hfinite

end HeightPaper.CountCoupling

namespace HeightPaper.CountCoupling

/-- The same canonical limit moment estimate with a moment window fixed before
the error tolerance is chosen. -/
theorem localProfileLimit_momentDifference_tight_of_window
    {l₀ x p η r : ℝ} (hl₀ : 1 < l₀)
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (hp : p ∈ Ioo (1 : ℝ) 2) (hη : 0 < η) (hr : 0 < r)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < r →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ l ≥ l₀,
      uniformLaw.real (localProfileMomentBad p η r x D l) ≤ ε ∧
      (∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
        u ∉ localProfileMomentBad p η r x D l →
        ∀ n j : ℕ, localSafeCutoff l u ≤ j → 1 ≤ j →
          Integrable (fun ω ↦ ‖localAnalyticProfileLimit l n u ω (x : ℂ) -
            Model.prescribedNormalizedProfile (Complex.exp (x : ℂ))
              (localBirth l u) (Model.initial n) (localSafeCutoff l u)
              j (ω j)‖ ^ p)
            (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
          (∫ ω, ‖localAnalyticProfileLimit l n u ω (x : ℂ) -
            Model.prescribedNormalizedProfile (Complex.exp (x : ℂ))
              (localBirth l u) (Model.initial n) (localSafeCutoff l u)
              j (ω j)‖ ^ p
            ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤
            D * (j : ℝ) ^ (-η)) := by
  obtain ⟨D, hD, hbad⟩ := localProfileMomentBad_uniform_tight hl₀ hp.1 hp.2.le hη
    hwindow hε
  obtain ⟨R, hR, hcan⟩ := localProfile_ae_canonical_analytic_limit hl₀ hx.1 hx.2
  refine ⟨D, hD, ?_⟩
  intro l hl
  constructor
  · exact hbad l hl
  · filter_upwards [hcan l hl] with u hu hs hgood n j hJj hj
    have hlim : ∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
        Tendsto (fun m ↦ Model.prescribedNormalizedProfile (Complex.exp (x : ℂ))
          (localBirth l u) (Model.initial n) (localSafeCutoff l u)
          (localSafeCutoff l u + 2 ^ m) (ω (localSafeCutoff l u + 2 ^ m))) atTop
          (𝓝 (localAnalyticProfileLimit l n u ω (x : ℂ))) := by
      filter_upwards [(hu hs n).1] with ω hω
      exact ((hω 0 le_rfl hR).1.tendsto_at (mem_closedBall_self le_rfl))
    have hb (N : ℕ) (hjN : j ≤ N) :
        localProfileMomentDifference l u n (x : ℂ) p j N ≤
          D * (j : ℝ) ^ (-η) := by
      apply le_of_not_gt
      intro hh
      apply hgood
      exact ⟨hs, n, j, N, hJj, hj, hjN, (x : ℂ), by simpa using hr, hh⟩
    exact localAnalyticProfileLimit_moment_sub_le l u n j (x : ℂ) (zero_lt_one.trans hp.1)
      (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hJj hlim hb

end HeightPaper.CountCoupling

namespace HeightPaper.CountCoupling

/-- On the good count words, the actual canonical local limit retains the
uniform conditional moment tail at the positive real tilt. The remaining
exceptional words are precisely the already measurable finite-time bad set. -/
theorem localProfileLimit_momentDifference_tight
    {l₀ x : ℝ} (hl₀ : 1 < l₀) (hx : x ∈ Ioo 0 (profileRoot l₀))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ Ioo (1 : ℝ) 2, ∃ η : ℝ, 0 < η ∧
      ∃ r : ℝ, 0 < r ∧ ∃ D : ℝ, 0 ≤ D ∧
      (∀ l ≥ l₀, complexProfileMomentExponent l (x : ℂ) p ≤ -1 - η) ∧
      ∀ l ≥ l₀,
        uniformLaw.real (localProfileMomentBad p η r x D l) ≤ ε ∧
        (∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
          u ∉ localProfileMomentBad p η r x D l →
          ∀ n j : ℕ, localSafeCutoff l u ≤ j → 1 ≤ j →
            Integrable (fun ω ↦ ‖localAnalyticProfileLimit l n u ω (x : ℂ) -
              Model.prescribedNormalizedProfile (Complex.exp (x : ℂ))
                (localBirth l u) (Model.initial n) (localSafeCutoff l u)
                j (ω j)‖ ^ p)
              (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
            (∫ ω, ‖localAnalyticProfileLimit l n u ω (x : ℂ) -
              Model.prescribedNormalizedProfile (Complex.exp (x : ℂ))
                (localBirth l u) (Model.initial n) (localSafeCutoff l u)
                j (ω j)‖ ^ p
              ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤
              D * (j : ℝ) ^ (-η)) := by
  obtain ⟨p, hp, η, hη, r, hr, hwindow⟩ :=
    exists_localProfile_moment_disk hl₀ hx.1 hx.2
  obtain ⟨D, hD, hbad⟩ := localProfileMomentBad_uniform_tight hl₀ hp.1 hp.2.le hη
    hwindow hε
  obtain ⟨R, hR, hcan⟩ := localProfile_ae_canonical_analytic_limit hl₀ hx.1 hx.2
  refine ⟨p, hp, η, hη, r, hr, D, hD, ?_, ?_⟩
  · intro l hl
    exact (hwindow l hl (x : ℂ) (by simpa using hr)).2.2.2
  intro l hl
  constructor
  · exact hbad l hl
  · filter_upwards [hcan l hl] with u hu hs hgood n j hJj hj
    have hlim : ∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
        Tendsto (fun m ↦ Model.prescribedNormalizedProfile (Complex.exp (x : ℂ))
          (localBirth l u) (Model.initial n) (localSafeCutoff l u)
          (localSafeCutoff l u + 2 ^ m) (ω (localSafeCutoff l u + 2 ^ m))) atTop
          (𝓝 (localAnalyticProfileLimit l n u ω (x : ℂ))) := by
      filter_upwards [(hu hs n).1] with ω hω
      exact ((hω 0 le_rfl hR).1.tendsto_at (mem_closedBall_self le_rfl))
    have hb (N : ℕ) (hjN : j ≤ N) :
        localProfileMomentDifference l u n (x : ℂ) p j N ≤
          D * (j : ℝ) ^ (-η) := by
      apply le_of_not_gt
      intro hh
      apply hgood
      exact ⟨hs, n, j, N, hJj, hj, hjN, (x : ℂ), by simpa using hr, hh⟩
    exact localAnalyticProfileLimit_moment_sub_le l u n j (x : ℂ) (zero_lt_one.trans hp.1)
      (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hJj hlim hb

end HeightPaper.CountCoupling

namespace HeightPaper.CountCoupling

/-- Uniform higher conditional moments for the canonical local limit at one
positive real tilt. Two explicit measurable exceptional sets account for the
profile envelope and the random safe cutoff. -/
theorem localProfileLimit_moment_uniform_tight
    {l₀ x : ℝ} (hl₀ : 1 < l₀) (hx : x ∈ Ioo 0 (profileRoot l₀))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ Ioo (1 : ℝ) 2, ∃ η : ℝ, 0 < η ∧
      ∃ r : ℝ, 0 < r ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        (∀ l ≥ l₀, complexProfileMomentExponent l (x : ℂ) p ≤ -1 - η) ∧
        ∀ l ≥ l₀,
          uniformLaw.real (localProfileMomentBad p η r x D l) ≤ ε / 2 ∧
          uniformLaw.real {u | K < localSafeCutoff l u} ≤ ε / 2 ∧
          (∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
            u ∉ localProfileMomentBad p η r x D l →
            localSafeCutoff l u ≤ K → ∀ n : ℕ,
              Integrable (fun ω ↦ ‖localAnalyticProfileLimit l n u ω (x : ℂ)‖ ^ p)
                (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
              (∫ ω, ‖localAnalyticProfileLimit l n u ω (x : ℂ)‖ ^ p
                ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤ C) := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨p, hp, η, hη, r, hr, D, hD, hexp, hmoment⟩ :=
    localProfileLimit_momentDifference_tight hl₀ hx hhalf
  obtain ⟨K, hKtight⟩ := localSafeCutoff_uniform_tight hl₀ hhalf
  let j := max K 1
  let C := (2 : ℝ) ^ (p - 1) *
    (D * (j : ℝ) ^ (-η) + ((Real.exp x) ^ (j + 1)) ^ p)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨p, hp, η, hη, r, hr, D, hD, K, C, hC, hexp, ?_⟩
  intro l hl
  obtain ⟨hbad, hgood⟩ := hmoment l hl
  refine ⟨hbad, hKtight l hl, ?_⟩
  filter_upwards [hgood] with u hu hs hnot hcut n
  have hJj : localSafeCutoff l u ≤ j := hcut.trans (le_max_left _ _)
  have hj : 1 ≤ j := le_max_right _ _
  have hsub := hu hs hnot n j hJj hj
  exact localAnalyticProfileLimit_moment_le_real l u n j hx.1.le hp.1.le hsub

end HeightPaper.CountCoupling

namespace HeightPaper.CountCoupling

theorem localProfileLimit_moment_uniform_tight_of_window
    {l₀ x p η r : ℝ} (hl₀ : 1 < l₀)
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (hp : p ∈ Ioo (1 : ℝ) 2) (hη : 0 < η) (hr : 0 < r)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < r →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ l ≥ l₀,
        uniformLaw.real (localProfileMomentBad p η r x D l) ≤ ε / 2 ∧
        uniformLaw.real {u | K < localSafeCutoff l u} ≤ ε / 2 ∧
        (∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
          u ∉ localProfileMomentBad p η r x D l →
          localSafeCutoff l u ≤ K → ∀ n : ℕ,
            Integrable (fun ω ↦ ‖localAnalyticProfileLimit l n u ω (x : ℂ)‖ ^ p)
              (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
            (∫ ω, ‖localAnalyticProfileLimit l n u ω (x : ℂ)‖ ^ p
              ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤ C) := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨D, hD, hmoment⟩ :=
    localProfileLimit_momentDifference_tight_of_window hl₀ hx hp hη hr hwindow hhalf
  obtain ⟨K, hKtight⟩ := localSafeCutoff_uniform_tight hl₀ hhalf
  let j := max K 1
  let C := (2 : ℝ) ^ (p - 1) *
    (D * (j : ℝ) ^ (-η) + ((Real.exp x) ^ (j + 1)) ^ p)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨D, hD, K, C, hC, ?_⟩
  intro l hl
  obtain ⟨hbad, hgood⟩ := hmoment l hl
  refine ⟨hbad, hKtight l hl, ?_⟩
  filter_upwards [hgood] with u hu hs hnot hcut n
  have hJj : localSafeCutoff l u ≤ j := hcut.trans (le_max_left _ _)
  have hj : 1 ≤ j := le_max_right _ _
  exact localAnalyticProfileLimit_moment_le_real l u n j hx.1.le hp.1.le
    (hu hs hnot n j hJj hj)

end HeightPaper.CountCoupling
