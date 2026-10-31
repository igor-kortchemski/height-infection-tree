module

public import HeightPaper.Probability.AnalyticBoundarySeries

/-!
# Probability bounds inherited by a common pointwise limit

An almost-sure common limit retains uniform exceedance bounds on an arbitrary
parameter set. The finite-time exceedance sets need not have a countable
parameterization: continuity from below is used for the ambient measure.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace HeightPaper

theorem measure_le_of_ae_eventually_mem {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (A : ℕ → Set Ω) {C : ℝ≥0∞}
    (hb : ∀ᶠ m in atTop, μ (A m) ≤ C)
    (he : ∀ᵐ ω ∂μ, ω ∈ E → ∀ᶠ m in atTop, ω ∈ A m) : μ E ≤ C := by
  let B : ℕ → Set Ω := fun n => ⋂ m ≥ n, A m
  have hB : Monotone B := by
    intro n k hnk ω hω
    simp only [B, mem_iInter] at hω ⊢
    intro m hkm
    exact hω m (hnk.trans hkm)
  have hsub : E ≤ᵐ[μ] ⋃ n, B n := by
    filter_upwards [he] with ω hω hE
    obtain ⟨n, hn⟩ := eventually_atTop.mp (hω hE)
    exact mem_iUnion.mpr ⟨n, by simpa only [B, mem_iInter] using hn⟩
  refine (measure_mono_ae hsub).trans ?_
  rw [hB.measure_iUnion]
  apply iSup_le
  intro n
  obtain ⟨k, hk⟩ := eventually_atTop.mp hb
  apply (measure_mono (show B n ⊆ A (max n k) from ?_)).trans (hk _ (le_max_right _ _))
  intro ω hω
  exact (mem_iInter.mp (mem_iInter.mp hω (max n k))) (le_max_left _ _)

/-- Common pointwise convergence suffices to pass a simultaneous exceedance
bound to the limit, with an arbitrarily smaller finite-time threshold. -/
theorem measure_uniform_exceedance_limit_le {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Set X) (F : ℕ → Ω → X → ℂ) (L G : Ω → X → ℂ)
    (hlim : ∀ᵐ ω ∂μ, ∀ z ∈ K, Tendsto (fun m => F m ω z) atTop (𝓝 (L ω z)))
    {δ ε : ℝ} (hδε : δ < ε) {C : ℝ≥0∞}
    (hb : ∀ᶠ m in atTop, μ {ω | ∃ z ∈ K, δ < ‖F m ω z - G ω z‖} ≤ C) :
    μ {ω | ∃ z ∈ K, ε < ‖L ω z - G ω z‖} ≤ C := by
  apply measure_le_of_ae_eventually_mem μ _ _ hb
  filter_upwards [hlim] with ω hω hbad
  obtain ⟨z, hz, he⟩ := hbad
  have ht := ((hω z hz).sub_const (G ω z)).norm
  exact (ht.eventually (Ioi_mem_nhds (hδε.trans he))).mono
    (fun m hm => ⟨z, hz, hm⟩)

end HeightPaper
