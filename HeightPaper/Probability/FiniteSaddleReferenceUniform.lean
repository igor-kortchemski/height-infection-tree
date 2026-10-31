module

public import HeightPaper.Probability.FiniteSaddleUniformParameter

/-! # Positive bounds for the reference amplitude in the saddle integral -/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

/-- The random reference amplitude is bounded above and away from zero with
one threshold for compact parameter and tilt families. -/
theorem finiteSaddle_reference_amplitude_uniform_tight
    {I : Set ℝ≥0} (hI : IsCompact I) (hIne : I.Nonempty)
    {T : ℝ} (hT : 0 < T)
    {K : Set ℝ} (hK : IsCompact K) (hKne : K.Nonempty)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l ∧
      K ⊆ Ioo 0 (profileRoot l))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c > (0 : ℝ), ∃ B > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real {q | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n q.1 i) ∧
        ∃ x ∈ K,
          ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
            finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ q.1
              (Real.log n) (x : ℂ)‖ < c ∨
          B < ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
            finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ q.1
              (Real.log n) (x : ℂ)‖} < δ := by
  obtain ⟨lmin, hlmin, hminL⟩ := hI.exists_isLeast hIne
  have hparams' : ∀ a ∈ I, 1 < (a : ℝ) ∧ T < fluidExtinctionTime a := by
    intro a ha
    exact ⟨(hparams a ha).1, (hparams a ha).2.1⟩
  have hIlower : ∀ a ∈ I, (lmin : ℝ) ≤ (a : ℝ) := by
    intro a ha
    exact_mod_cast hminL ha
  have hhalf : 0 < δ / 2 := by positivity
  obtain ⟨c₀, hc₀, B₀, hB₀, NA, hamp⟩ := finite_profileResidual_compact_tight
    hI (hparams lmin hlmin).1 hT hparams' hIlower hK hKne
    (hparams lmin hlmin).2.2 hhalf
  obtain ⟨t, ht, NC, hcenter⟩ := finite_profileResidual_compact_centered_disk
    hI (hparams lmin hlmin).1 hT hparams' hIlower hK hKne
    (hparams lmin hlmin).2.2 (half_pos hc₀) hhalf
  let c : ℝ := c₀ / 2
  let B : ℝ := B₀ + c₀ / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨c, hc, B, hB, max NA NC, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let A : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ x ∈ K,
        ‖profileResidual (coupledTreeState l n q H) (growthFactor l)
          (Real.log n) (x : ℂ)‖ < c₀ ∨
        B₀ < ‖profileResidual (coupledTreeState l n q H) (growthFactor l)
          (Real.log n) (x : ℂ)‖}
  let C : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ x ∈ K, ∃ z ∈ closedBall (x : ℂ) t,
        c₀ / 2 < ‖profileResidual (coupledTreeState l n q H) (growthFactor l)
          (Real.log n) z -
          localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
            finiteUnshiftedNormalizerResidual l n H q.1
              (Real.log n) (x : ℂ)‖}
  have hA : birthParentLaw.real A < δ / 2 :=
    hamp n ((le_max_left _ _).trans hn) l hl
  have hC : birthParentLaw.real C < δ / 2 :=
    hcenter n ((le_max_right _ _).trans hn) l hl
  have hsub : {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ x ∈ K,
        ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
          finiteUnshiftedNormalizerResidual l n H q.1
            (Real.log n) (x : ℂ)‖ < c ∨
        B < ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
          finiteUnshiftedNormalizerResidual l n H q.1
            (Real.log n) (x : ℂ)‖} ⊆ A ∪ C := by
    rintro q ⟨hs, x, hx, hbad⟩
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    let A₀ : ℂ := localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
      finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n) (x : ℂ)
    let F : ℂ := profileResidual (coupledTreeState l n q H)
      (growthFactor l) (Real.log n) (x : ℂ)
    have hFlo : c₀ ≤ ‖F‖ := by
      apply le_of_not_gt
      intro hh
      exact hnot.1 ⟨hs, x, hx, Or.inl hh⟩
    have hFhi : ‖F‖ ≤ B₀ := by
      apply le_of_not_gt
      intro hh
      exact hnot.1 ⟨hs, x, hx, Or.inr hh⟩
    have hclose : ‖F - A₀‖ ≤ c₀ / 2 := by
      apply le_of_not_gt
      intro hh
      exact hnot.2 ⟨hs, x, hx, (x : ℂ), mem_closedBall_self ht.le, hh⟩
    have hbound := norm_le_norm_add_norm_sub F A₀
    have hbound' := norm_le_norm_add_norm_sub A₀ F
    rw [norm_sub_rev] at hbound'
    have hlo : c ≤ ‖A₀‖ := by dsimp [c]; linarith
    have hhi : ‖A₀‖ ≤ B := by dsimp [B]; linarith
    exact hbad.elim (fun hh => (not_lt_of_ge hlo) hh)
      (fun hh => (not_lt_of_ge hhi) hh)
  have hh := (measureReal_mono (μ := birthParentLaw) hsub).trans
    (measureReal_union_le _ _)
  linarith

end HeightPaper.CountCoupling
