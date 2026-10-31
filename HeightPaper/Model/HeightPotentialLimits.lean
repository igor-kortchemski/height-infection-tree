module

public import HeightPaper.Model.HeightPotentialBounds

/-! # Vanishing tails for actual epidemic outgrowth maxima -/

public section

open MeasureTheory Filter
open scoped Topology NNReal

namespace HeightPaper.Model

/-- If the geometric expected upper count vanishes, the actual selected
outgrowth maximum fails to reach the level with probability tending to one. -/
theorem tendsto_continuation_freshHeight_tail_zero {ι : Type*} {ℓ : Filter ι}
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (rate : ι → ℝ≥0) (s₀ : ι → State) (roots : ι → Finset ℕ) (H K : ι → ℕ)
    (hvalid : ∀ᶠ n in ℓ, 0 < H n ∧
      (p : ℝ) ≤ 1 - (infectionProbability (rate n) (s₀ n).susceptible : ℝ) ∧
      potential (s₀ n) ≤ K n)
    (hscale : Tendsto (fun n ↦
      (((s₀ n).active.filter (fun v ↦ v.val ∈ roots n)).card : ℝ) *
        Branching.geometricMean p ^ H n) ℓ (𝓝 0)) :
    Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
      {s | ¬belowFreshHeight (s₀ n).vertices (s₀ n).tree.size_pos (roots n) (H n) s})
        ℓ (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hscale
  filter_upwards [hvalid] with n hn
  exact continuation_freshHeight_tail_le_geometric hp hp1 (rate n) (s₀ n) (roots n)
    hn.1 hn.2.1 hn.2.2

/-- If the geometric expected lower count diverges and the terminal
susceptible-barrier error vanishes, the actual maximum reaches the level
with probability tending to one. -/
theorem tendsto_continuation_freshHeight_cdf_zero {ι : Type*} {ℓ : Filter ι}
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (rate : ι → ℝ≥0) (s₀ : ι → State) (roots : ι → Finset ℕ) (H K L : ι → ℕ)
    (hvalid : ∀ᶠ n in ℓ, 0 < H n ∧
      1 - (infectionProbability (rate n) (L n) : ℝ) ≤ (p : ℝ) ∧
      potential (s₀ n) ≤ K n)
    (hscale : Tendsto (fun n ↦
      (((s₀ n).active.filter (fun v ↦ v.val ∈ roots n)).card : ℝ) *
        Branching.geometricMean p ^ H n) ℓ atTop)
    (hbarrier : Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
      {s | s.susceptible < L n}) ℓ (𝓝 0)) :
    Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
      {s | belowFreshHeight (s₀ n).vertices (s₀ n).tree.size_pos (roots n) (H n) s})
        ℓ (𝓝 0) := by
  have hm1 := Branching.geometricMean_lt_one hp
  have hexp : Tendsto (fun n ↦ Real.exp (-(1 - Branching.geometricMean p) *
      ((((s₀ n).active.filter (fun v ↦ v.val ∈ roots n)).card : ℝ) *
        Branching.geometricMean p ^ H n))) ℓ (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg
      (by linarith : -(1 - Branching.geometricMean p) < 0) hscale)
  have hsum := hexp.add hbarrier
  rw [add_zero] at hsum
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hsum
  filter_upwards [hvalid] with n hn
  have heq : -(((s₀ n).active.filter (fun v ↦ v.val ∈ roots n)).card : ℝ) *
      ((1 - Branching.geometricMean p) * Branching.geometricMean p ^ H n) =
      -(1 - Branching.geometricMean p) *
        ((((s₀ n).active.filter (fun v ↦ v.val ∈ roots n)).card : ℝ) *
          Branching.geometricMean p ^ H n) := by ring
  simpa only [heq] using continuation_freshHeight_cdf_le_geometric_exp hp hp1
    (rate n) (s₀ n) (roots n) hn.1 (L n) hn.2.1 hn.2.2

end HeightPaper.Model
