module

public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Recovering a full sequence from convergent anchor distances

A scalar martingale convergence theorem suffices to recover full-time
convergence of a Banach-valued martingale with a convergent subsequence.
The candidate limit need not be a measurable random variable.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace HeightPaper

theorem tendsto_of_subsequence_of_dist_limits {E : Type*} [PseudoMetricSpace E]
    (X : ℕ → E) (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (L : E)
    (hsub : Tendsto (fun m ↦ X (a m)) atTop (𝓝 L))
    (hlim : ∀ m, ∃ b : ℝ,
      Tendsto (fun k ↦ dist (X k) (X (a m))) atTop (𝓝 b)) :
    Tendsto X atTop (𝓝 L) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨m, hm⟩ := Metric.tendsto_atTop.mp hsub (ε / 3) (by positivity)
  have hclose : dist L (X (a m)) < ε / 3 := by
    simpa only [dist_comm] using hm m le_rfl
  obtain ⟨b, hb⟩ := hlim m
  have he : b = dist L (X (a m)) :=
    tendsto_nhds_unique (hb.comp ha) (hsub.dist tendsto_const_nhds)
  subst b
  have htail : ∀ᶠ k : ℕ in atTop, dist (X k) (X (a m)) < 2 * ε / 3 :=
    hb.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  refine ⟨N, fun k hk ↦ ?_⟩
  have ht := dist_triangle (X k) (X (a m)) L
  have hc : dist (X (a m)) L < ε / 3 := by simpa only [dist_comm] using hclose
  have hn := hN k hk
  linarith

theorem ae_tendsto_of_subsequence_of_dist_limits
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (a : ℕ → ℕ)
    (ha : Tendsto a atTop atTop)
    (hlim : ∀ m, ∀ᵐ ω ∂μ, ∃ b : ℝ,
      Tendsto (fun k ↦ dist (X k ω) (X (a m) ω)) atTop (𝓝 b)) :
    ∀ᵐ ω ∂μ, ∀ L : E,
      Tendsto (fun m ↦ X (a m) ω) atTop (𝓝 L) →
        Tendsto (fun k ↦ X k ω) atTop (𝓝 L) := by
  filter_upwards [ae_all_iff.mpr hlim] with ω hω
  exact fun L hL ↦ tendsto_of_subsequence_of_dist_limits
    (fun k ↦ X k ω) a ha L hL hω

theorem martingale_ae_exists_norm_sub_initial_limit
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (F : ℕ → Ω → E) (hm : Martingale F ℱ μ)
    (B : ℝ) (hB : ∀ k, (∫ ω, ‖F k ω - F 0 ω‖ ∂μ) ≤ B) :
    ∀ᵐ ω ∂μ, ∃ b : ℝ,
      Tendsto (fun k ↦ ‖F k ω - F 0 ω‖) atTop (𝓝 b) := by
  have hc := martingale_const_fun ℱ μ (hm.stronglyMeasurable 0) (hm.integrable 0)
  have hd : Martingale (fun k ω ↦ F k ω - F 0 ω) ℱ μ := hm.sub hc
  have hs : Submartingale (fun k ω ↦ ‖F k ω - F 0 ω‖) ℱ μ := by
    apply submartingale_nat
      (fun k ↦ (hd.stronglyMeasurable k).norm)
      (fun k ↦ (hd.integrable k).norm)
    intro k
    filter_upwards [norm_condExp_le (μ := μ) (m := ℱ k) (fun ω ↦ F (k + 1) ω - F 0 ω),
      hd.condExp_ae_eq (Nat.le_succ k)] with ω hn he
    simpa only [he] using hn
  apply hs.exists_ae_tendsto_of_bdd (R := Real.toNNReal B)
  intro k
  have hi : Integrable (fun ω ↦ ‖F k ω - F 0 ω‖) μ := (hd.integrable k).norm
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  change ENNReal.ofReal _ ≤ ENNReal.ofReal B
  apply ENNReal.ofReal_le_ofReal
  simpa only [Real.norm_eq_abs, abs_norm] using hB k

end HeightPaper
