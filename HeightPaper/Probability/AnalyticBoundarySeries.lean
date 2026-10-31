module

public import HeightPaper.Analysis.AnalyticCircleControl
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Analytic random series from expected boundary estimates

Summable expected boundary norms imply almost-sure uniform convergence on
smaller disks. This supplies an analytic version of dyadic martingale limits;
no uniform-convergence hypothesis is imposed.
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology ENNReal BigOperators

namespace HeightPaper

theorem ae_summable_nonneg_of_summable_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (b : ℕ → Ω → ℝ) (hb : ∀ n ω, 0 ≤ b n ω)
    (hi : ∀ n, Integrable (b n) μ)
    (hs : Summable (fun n => ∫ ω, b n ω ∂μ)) :
    ∀ᵐ ω ∂μ, Summable (fun n => b n ω) := by
  have he (n : ℕ) : eLpNorm (b n) 1 μ = ENNReal.ofReal (∫ ω, b n ω ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hi n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi n)]
    congr 1
    apply integral_congr_ae
    exact ae_of_all μ (fun ω => Real.norm_of_nonneg (hb n ω))
  have ha := summable_norm_of_tsum_eLpNorm_ne_top (μ := μ) (f := b)
    (show (1 : ℝ≥0∞) ≤ 1 from le_rfl)
    (by simpa only [he] using hs.tsum_ofReal_ne_top)
  filter_upwards [ha] with ω hω
  exact hω.congr (fun n => Real.norm_of_nonneg (hb n ω))

/-- Summable expected boundary increments give a common analytic limit on
every smaller disk, on one probability-one event. -/
theorem ae_analytic_series_of_summable_mean_circleL1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (c : ℂ) (R : ℝ) (f : ℕ → Ω → ℂ → ℂ)
    (hf : ∀ᵐ ω ∂μ, ∀ n, DifferentiableOn ℂ (f n ω) (closedBall c R))
    (hi : ∀ n, Integrable (fun ω => circleL1 c R (f n ω)) μ)
    (hs : Summable (fun n => ∫ ω, circleL1 c R (f n ω) ∂μ)) :
    ∀ᵐ ω ∂μ, ∀ r : ℝ, 0 ≤ r → r < R →
      TendstoUniformlyOn (fun n z => ∑ i ∈ Finset.range n, f i ω z)
          (fun z => ∑' i, f i ω z) atTop (closedBall c r) ∧
        DifferentiableOn ℂ (fun z => ∑' i, f i ω z) (ball c r) := by
  have hsum := ae_summable_nonneg_of_summable_integral μ
    (fun n ω => circleL1 c R (f n ω)) (fun n ω => circleL1_nonneg c R (f n ω)) hi hs
  filter_upwards [hsum, hf] with ω hω hdiff r hr hrR
  exact ⟨analytic_series_uniform_of_circleL1 hr hrR (fun n => f n ω) hdiff hω,
    analytic_series_differentiable_of_circleL1 hr hrR (fun n => f n ω) hdiff hω⟩

/-- A summable deterministic majorant for the expected boundary norms is enough. -/
theorem ae_analytic_series_of_mean_circleL1_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (c : ℂ) (R : ℝ) (f : ℕ → Ω → ℂ → ℂ)
    (hf : ∀ᵐ ω ∂μ, ∀ n, DifferentiableOn ℂ (f n ω) (closedBall c R))
    (hi : ∀ n, Integrable (fun ω => circleL1 c R (f n ω)) μ)
    (B : ℕ → ℝ) (hB : Summable B)
    (hbound : ∀ n, (∫ ω, circleL1 c R (f n ω) ∂μ) ≤ B n) :
    ∀ᵐ ω ∂μ, ∀ r : ℝ, 0 ≤ r → r < R →
      TendstoUniformlyOn (fun n z => ∑ i ∈ Finset.range n, f i ω z)
          (fun z => ∑' i, f i ω z) atTop (closedBall c r) ∧
        DifferentiableOn ℂ (fun z => ∑' i, f i ω z) (ball c r) := by
  apply ae_analytic_series_of_summable_mean_circleL1 μ c R f hf hi
  exact Summable.of_nonneg_of_le
    (fun n => integral_nonneg (fun ω => circleL1_nonneg c R (f n ω))) hbound hB

/-- The analytic version constructed from the telescoping series. Applied to
`F n = M (2^n)`, this is a single analytic dyadic martingale limit. -/
noncomputable def analyticSequenceLimit {Ω : Type*} (F : ℕ → Ω → ℂ → ℂ)
    (ω : Ω) (z : ℂ) : ℂ :=
  F 0 ω z + ∑' n, (F (n + 1) ω z - F n ω z)

theorem ae_analytic_sequence_of_summable_mean_circleL1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (c : ℂ) (R : ℝ) (F : ℕ → Ω → ℂ → ℂ)
    (hF : ∀ᵐ ω ∂μ, ∀ n, DifferentiableOn ℂ (F n ω) (closedBall c R))
    (hi : ∀ n, Integrable
      (fun ω => circleL1 c R (fun z => F (n + 1) ω z - F n ω z)) μ)
    (hs : Summable
      (fun n => ∫ ω, circleL1 c R (fun z => F (n + 1) ω z - F n ω z) ∂μ)) :
    ∀ᵐ ω ∂μ, ∀ r : ℝ, 0 ≤ r → r < R →
      TendstoUniformlyOn (fun n => F n ω) (analyticSequenceLimit F ω)
          atTop (closedBall c r) ∧
        DifferentiableOn ℂ (analyticSequenceLimit F ω) (ball c r) := by
  have hh := ae_analytic_series_of_summable_mean_circleL1 μ c R
    (fun n ω z => F (n + 1) ω z - F n ω z)
    (hF.mono (fun ω hω n => (hω (n + 1)).sub (hω n))) hi hs
  filter_upwards [hh, hF] with ω hω hdiff r hr hrR
  obtain ⟨hconv, hana⟩ := hω r hr hrR
  constructor
  · have hconst : TendstoUniformlyOn (fun (_ : ℕ) z => F 0 ω z) (F 0 ω)
        atTop (closedBall c r) := by
      rw [tendstoUniformlyOn_iff]
      intro ε hε
      exact Eventually.of_forall (fun _ _ _ => by simpa using hε)
    have ht := hconst.add hconv
    convert ht using 1
    · ext n z
      simp only [Pi.add_apply]
      rw [Finset.sum_range_sub (fun i => F i ω z)]
      ring
    · rfl
  · exact ((hdiff 0).mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall hrR.le))).add hana

end HeightPaper
