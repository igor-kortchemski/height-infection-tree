module

public import HeightPaper.Probability.LocalProfileLimitMoment
public import HeightPaper.Probability.LocalProfileCarrier

/-!
# Conditional moments of the local limit under the parent-draw law

The prescribed trajectory measure is the image of the actual iid parent
draws. This transfers the newly proved local-limit moment envelope to the
conditional law used in the paper's finite-to-local proposition.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace HeightPaper.CountCoupling

theorem localRankProfileLimit_parentMoment_eq
    (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (z : ℂ) {p : ℝ} (hp : 0 ≤ p) :
    (∫ v, ‖localRankProfileLimit l n (u, v) z‖ ^ p ∂uniformLaw) =
      ∫ ω, ‖localAnalyticProfileLimit l n u ω z‖ ^ p
        ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n) := by
  let g : (ℕ → Model.State) → ℝ :=
    fun ω ↦ ‖localAnalyticProfileLimit l n u ω z‖ ^ p
  have hgm : Measurable g :=
    (Real.continuous_rpow_const hp).measurable.comp
      (Model.measurable_prescribedAnalyticProfileLimit_eval
        (localBirth l u) (Model.initial n) (localSafeCutoff l u) z).norm
  have hh := integral_map (μ := uniformLaw)
    (Model.measurable_rankTrajectory (localBirth l u) (Model.initial n)).aemeasurable
    hgm.aestronglyMeasurable
  rw [Model.rankTrajectory_law] at hh
  simpa only [g, localRankProfileLimit, localAnalyticProfileLimit, Function.comp_def]
    using hh.symm

theorem localRankProfileLimit_parentMoment_integrable
    (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (z : ℂ) {p : ℝ}
    (hint : Integrable (fun ω ↦ ‖localAnalyticProfileLimit l n u ω z‖ ^ p)
      (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n))) :
    Integrable (fun v ↦ ‖localRankProfileLimit l n (u, v) z‖ ^ p) uniformLaw := by
  rw [← Model.rankTrajectory_law (localBirth l u) (Model.initial n)] at hint
  exact hint.comp_measurable
    (Model.measurable_rankTrajectory (localBirth l u) (Model.initial n))

/-- The local limiting profile has a common higher conditional moment bound
under the actual parent-draw law, outside two uniformly rare count-word sets. -/
theorem localRankProfileLimit_parentMoment_uniform_tight
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
              Integrable (fun v ↦ ‖localRankProfileLimit l n (u, v) (x : ℂ)‖ ^ p)
                uniformLaw ∧
              (∫ v, ‖localRankProfileLimit l n (u, v) (x : ℂ)‖ ^ p
                ∂uniformLaw) ≤ C) := by
  obtain ⟨p, hp, η, hη, r, hr, D, hD, K, C, hC, hexp, hall⟩ :=
    localProfileLimit_moment_uniform_tight hl₀ hx hε
  refine ⟨p, hp, η, hη, r, hr, D, hD, K, C, hC, hexp, ?_⟩
  intro l hl
  obtain ⟨hbad, hcut, hgood⟩ := hall l hl
  refine ⟨hbad, hcut, ?_⟩
  filter_upwards [hgood] with u hu hs hnot hK n
  obtain ⟨hint, hbound⟩ := hu hs hnot hK n
  refine ⟨localRankProfileLimit_parentMoment_integrable l n u (x : ℂ) hint, ?_⟩
  exact (localRankProfileLimit_parentMoment_eq l n u (x : ℂ)
    (zero_le_one.trans hp.1.le)).trans_le hbound

theorem localRankProfileLimit_parentMoment_uniform_tight_of_window
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
            Integrable (fun v ↦ ‖localRankProfileLimit l n (u, v) (x : ℂ)‖ ^ p)
              uniformLaw ∧
            (∫ v, ‖localRankProfileLimit l n (u, v) (x : ℂ)‖ ^ p
              ∂uniformLaw) ≤ C) := by
  obtain ⟨D, hD, K, C, hC, hall⟩ :=
    localProfileLimit_moment_uniform_tight_of_window hl₀ hx hp hη hr hwindow hε
  refine ⟨D, hD, K, C, hC, ?_⟩
  intro l hl
  obtain ⟨hbad, hcut, hgood⟩ := hall l hl
  refine ⟨hbad, hcut, ?_⟩
  filter_upwards [hgood] with u hu hs hnot hK n
  obtain ⟨hint, hbound⟩ := hu hs hnot hK n
  refine ⟨localRankProfileLimit_parentMoment_integrable l n u (x : ℂ) hint, ?_⟩
  exact (localRankProfileLimit_parentMoment_eq l n u (x : ℂ)
    (zero_le_one.trans hp.1.le)).trans_le hbound

end HeightPaper.CountCoupling
