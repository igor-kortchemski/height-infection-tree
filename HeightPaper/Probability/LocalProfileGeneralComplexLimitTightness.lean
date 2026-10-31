module

public import HeightPaper.Probability.LocalProfileGeneralComplexTightness
public import HeightPaper.Probability.LocalProfileGeneralComplexAnalytic
public import HeightPaper.Probability.LocalProfileLimitMoment

/-!
# Weakly parameter-uniform conditional moments of the canonical limit
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology ENNReal BigOperators

namespace HeightPaper.CountCoupling

/-- A fixed strict complex moment point has one smaller disk where the
canonical limit inherits the finite-time moment tail outside a count-word
event with probability uniformly small for every larger epidemic parameter. -/
theorem localComplexLimitMomentBad_uniform_tight
    {l₀ p : ℝ} {z₀ : ℂ} (hl₀ : 1 < l₀)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (hz : z₀.re < profileRoot l₀)
    (he : complexProfileMomentExponent l₀ z₀ p < -1) :
    ∃ η : ℝ, 0 < η ∧ ∃ r : ℝ, 0 < r ∧
      ∀ δ > (0 : ℝ), ∃ D : ℝ, 0 ≤ D ∧ ∀ l ≥ l₀,
        uniformLaw.real (localComplexMomentBad p η (2 * r) z₀ D l) ≤ δ ∧
        (∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
          u ∉ localComplexMomentBad p η (2 * r) z₀ D l →
          ∀ n : ℕ, ∀ z ∈ closedBall z₀ r, ∀ j : ℕ,
            localSafeCutoff l u ≤ j → 1 ≤ j →
            Integrable (fun ω ↦ ‖localAnalyticProfileLimit l n u ω z -
              Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p)
              (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
            (∫ ω, ‖localAnalyticProfileLimit l n u ω z -
              Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p
              ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤
                D * (j : ℝ) ^ (-η)) := by
  obtain ⟨η, hη, ρ, hρ, hwindow⟩ :=
    exists_localProfile_complex_moment_disk hl₀ hp hp2 hz he
  obtain ⟨R, hR, hcan⟩ :=
    localProfile_ae_canonical_complex_analytic_limit hl₀ hp hp2 hz he
  let r := min (ρ / 3) (R / 2)
  have hr : 0 < r := by dsimp [r]; positivity
  have h2rρ : 2 * r < ρ := by dsimp [r]; linarith [min_le_left (ρ / 3) (R / 2)]
  have hrR : r < R := by dsimp [r]; linarith [min_le_right (ρ / 3) (R / 2)]
  have hwindow' : ∀ l ≥ l₀, ∀ z : ℂ, dist z z₀ < 2 * r →
      z.re < profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η :=
    fun l hl z hz' ↦ hwindow l hl z (hz'.trans h2rρ)
  refine ⟨η, hη, r, hr, ?_⟩
  intro δ hδ
  obtain ⟨D, hD, hDtight⟩ :=
    localComplexMomentBad_uniform_tight hl₀ hp hp2 hη hwindow' hδ
  refine ⟨D, hD, ?_⟩
  intro l hl
  refine ⟨hDtight l hl, ?_⟩
  filter_upwards [hcan l hl] with u hu
  intro hs hgood n z hz' j hJj hj
  have hlim : ∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
      Tendsto (fun m ↦ Model.prescribedNormalizedProfile (Complex.exp z)
        (localBirth l u) (Model.initial n) (localSafeCutoff l u)
        (localSafeCutoff l u + 2 ^ m) (ω (localSafeCutoff l u + 2 ^ m))) atTop
        (𝓝 (localAnalyticProfileLimit l n u ω z)) := by
    filter_upwards [(hu hs n).1] with ω hω
    exact ((hω r hr.le hrR).1.tendsto_at hz')
  have hb (N : ℕ) (hjN : j ≤ N) :
      localProfileMomentDifference l u n z p j N ≤ D * (j : ℝ) ^ (-η) := by
    apply le_of_not_gt
    intro hbad
    apply hgood
    exact ⟨hs, n, j, N, hJj, hj, hjN, z,
      (mem_closedBall.mp hz').trans_lt (by linarith : r < 2 * r), hbad⟩
  exact localAnalyticProfileLimit_moment_sub_le l u n j z
    (zero_lt_one.trans hp) (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    hJj hlim hb

end HeightPaper.CountCoupling
