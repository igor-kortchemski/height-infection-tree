module

public import HeightPaper.Probability.LocalProfileCompactModulus
public import HeightPaper.Probability.FiniteLocalProfileCompactDisk

/-! # Central comparison uniformly over a compact set of saddle tilts -/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal

namespace HeightPaper.CountCoupling

/-- Uniformly near every real saddle in a compact admissible set, the finite
unshifted profile is close to the local analytic limit at that saddle. -/
theorem uniform_finiteProfile_compact_centered_disk
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    {K : Set ℝ} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKd : K ⊆ Ioo 0 (profileRoot l₀))
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ∃ t > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real {q | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n q.1 i) ∧
        ∃ x ∈ K, ∃ z ∈ closedBall (x : ℂ) t,
          τ < ‖finiteUnshiftedRankProfile l n q ⌊T * n⌋₊ z -
            localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖} < δ := by
  have hτ2 : 0 < τ / 2 := by positivity
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨t₀, ht₀, N, hcmp⟩ := uniform_finiteLocalProfile_compact_disk_comparison
    hI hl₀ hT hparams hIlower hK hKne hKd hτ2 hδ2
  obtain ⟨t₁, ht₁, hmod⟩ := localProfile_unshifted_compact_modulus_uniform
    hl₀ hK hKd hτ2 hδ2
  let t := min t₀ t₁
  have ht : 0 < t := lt_min ht₀ ht₁
  refine ⟨t, ht, N, ?_⟩
  intro n hn l hl
  let C := finiteLocalProfileBad l n ⌊T * n⌋₊
    (⋃ x ∈ K, closedBall (x : ℂ) t₀) (τ / 2)
  let M : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ x ∈ K, ∃ z ∈ closedBall (x : ℂ) t₁,
        τ / 2 < ‖localUnshiftedRankProfileLimit l 0 q z -
          localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖}
  have hC : birthParentLaw.real C < δ / 2 := hcmp n hn l hl
  have hM : birthParentLaw.real M < δ / 2 := hmod l (hIlower l hl) 0
  have hsub : {q | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n q.1 i) ∧
      ∃ x ∈ K, ∃ z ∈ closedBall (x : ℂ) t,
        τ < ‖finiteUnshiftedRankProfile l n q ⌊T * n⌋₊ z -
          localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖} ⊆ C ∪ M := by
    rintro q ⟨hs, x, hx, z, hz, hbad⟩
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    have hz₀ : z ∈ closedBall (x : ℂ) t₀ :=
      closedBall_subset_closedBall (min_le_left _ _) hz
    have hz₁ : z ∈ closedBall (x : ℂ) t₁ :=
      closedBall_subset_closedBall (min_le_right _ _) hz
    have hls : ∀ i, 0 < (localWalk l q.1 i : ℝ) := by
      have hnotC : q ∉ C := hnot.1
      have hyes : (∀ i, 0 < localWalk l q.1 i) := by
        by_contra hh
        exact hnotC ⟨hs, Or.inl hh⟩
      exact_mod_cast hyes
    have hclose : ‖finiteUnshiftedRankProfile l n q ⌊T * n⌋₊ z -
        localUnshiftedRankProfileLimit l 0 q z‖ ≤ τ / 2 := by
      apply le_of_not_gt
      intro hh
      exact hnot.1 ⟨hs, Or.inr ⟨z,
        mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, hz₀⟩⟩, hh⟩⟩
    have hmodclose : ‖localUnshiftedRankProfileLimit l 0 q z -
        localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ ≤ τ / 2 := by
      apply le_of_not_gt
      intro hh
      exact hnot.2 ⟨hls, x, hx, z, hz₁, hh⟩
    have hle : ‖finiteUnshiftedRankProfile l n q ⌊T * n⌋₊ z -
        localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ ≤ τ := by
      calc
        _ = ‖(finiteUnshiftedRankProfile l n q ⌊T * n⌋₊ z -
              localUnshiftedRankProfileLimit l 0 q z) +
              (localUnshiftedRankProfileLimit l 0 q z -
                localUnshiftedRankProfileLimit l 0 q (x : ℂ))‖ := by
              congr 1
              ring
        _ ≤ _ := norm_add_le _ _
        _ ≤ τ := by linarith
    exact (not_lt_of_ge hle) hbad
  have hh := (measureReal_mono (μ := birthParentLaw) hsub).trans
    (measureReal_union_le _ _)
  linarith

end HeightPaper.CountCoupling
