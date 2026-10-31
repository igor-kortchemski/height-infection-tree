module

public import HeightPaper.Probability.FiniteSaddleReferenceUniform

/-! # Uniform positive bounds for the normalized lattice saddle integral -/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

/-- The normalized saddle integral is bounded above and away from zero for
every exact lattice height, uniformly in the compact parameter and tilt sets. -/
theorem finiteSaddle_uniform_integral_amplitude_tight
    {I : Set ℝ≥0} (hI : IsCompact I) (hIne : I.Nonempty)
    {T : ℝ} (hT : 0 < T)
    {K : Set ℝ} (hK : IsCompact K) (hKne : K.Nonempty)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l ∧
      K ⊆ Ioo 0 (profileRoot l))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c > (0 : ℝ), ∃ B > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real {q | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n q.1 i) ∧
        ∃ x ∈ K, ∃ k : ℕ,
          (k : ℝ) = growthFactor l * Real.exp x * Real.log n ∧
          (‖(Real.sqrt (Real.log n * (growthFactor l * Real.exp x) / 2) : ℂ) *
            (∫ v : ℝ in -Real.pi..Real.pi,
              finiteSaddleIntegrandAtScale l ⌊T * n⌋₊ (Real.log n) x
                (coupledTreeHistory l n ⌊T * n⌋₊ q) v)‖ < c ∨
          B < ‖(Real.sqrt (Real.log n * (growthFactor l * Real.exp x) / 2) : ℂ) *
            (∫ v : ℝ in -Real.pi..Real.pi,
              finiteSaddleIntegrandAtScale l ⌊T * n⌋₊ (Real.log n) x
                (coupledTreeHistory l n ⌊T * n⌋₊ q) v)‖)} < δ := by
  have hhalf : 0 < δ / 2 := by positivity
  obtain ⟨c₀, hc₀, B₀, hB₀, NR, href⟩ :=
    finiteSaddle_reference_amplitude_uniform_tight hI hIne hT hK hKne hparams hhalf
  let τ : ℝ := c₀ * Real.sqrt Real.pi / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨NS, hsaddle⟩ := finiteSaddle_uniform_parameter_tilt_integral_tight
    hI hIne hT hK hKne hparams hτ hhalf
  let c : ℝ := τ
  let B : ℝ := B₀ * Real.sqrt Real.pi + τ
  have hc : 0 < c := hτ
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨c, hc, B, hB, max NR NS, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let R : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ x ∈ K,
        ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
          finiteUnshiftedNormalizerResidual l n H q.1
            (Real.log n) (x : ℂ)‖ < c₀ ∨
        B₀ < ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
          finiteUnshiftedNormalizerResidual l n H q.1
            (Real.log n) (x : ℂ)‖}
  let S : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ x ∈ K, ∃ k : ℕ,
        (k : ℝ) = growthFactor l * Real.exp x * Real.log n ∧
        τ < ‖(Real.sqrt (Real.log n * (growthFactor l * Real.exp x) / 2) : ℂ) *
          (∫ v : ℝ in -Real.pi..Real.pi,
            finiteSaddleIntegrandAtScale l H (Real.log n) x
              (coupledTreeHistory l n H q) v) -
          (localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
            finiteUnshiftedNormalizerResidual l n H q.1
              (Real.log n) (x : ℂ)) * (Real.sqrt Real.pi : ℂ)‖}
  have hR : birthParentLaw.real R < δ / 2 := href n ((le_max_left _ _).trans hn) l hl
  have hS : birthParentLaw.real S < δ / 2 := hsaddle n ((le_max_right _ _).trans hn) l hl
  have hsub : {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ x ∈ K, ∃ k : ℕ,
        (k : ℝ) = growthFactor l * Real.exp x * Real.log n ∧
        (‖(Real.sqrt (Real.log n * (growthFactor l * Real.exp x) / 2) : ℂ) *
          (∫ v : ℝ in -Real.pi..Real.pi,
            finiteSaddleIntegrandAtScale l H (Real.log n) x
              (coupledTreeHistory l n H q) v)‖ < c ∨
        B < ‖(Real.sqrt (Real.log n * (growthFactor l * Real.exp x) / 2) : ℂ) *
          (∫ v : ℝ in -Real.pi..Real.pi,
            finiteSaddleIntegrandAtScale l H (Real.log n) x
              (coupledTreeHistory l n H q) v)‖)} ⊆ R ∪ S := by
    rintro q ⟨hs, x, hx, k, hk, hbad⟩
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    let A₀ : ℂ := localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
      finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n) (x : ℂ)
    let Z : ℂ := (Real.sqrt (Real.log n * (growthFactor l * Real.exp x) / 2) : ℂ) *
      (∫ v : ℝ in -Real.pi..Real.pi,
        finiteSaddleIntegrandAtScale l H (Real.log n) x
          (coupledTreeHistory l n H q) v)
    have hAlo : c₀ ≤ ‖A₀‖ := by
      apply le_of_not_gt
      intro hh
      exact hnot.1 ⟨hs, x, hx, Or.inl hh⟩
    have hAhi : ‖A₀‖ ≤ B₀ := by
      apply le_of_not_gt
      intro hh
      exact hnot.1 ⟨hs, x, hx, Or.inr hh⟩
    have hclose : ‖Z - A₀ * (Real.sqrt Real.pi : ℂ)‖ ≤ τ := by
      apply le_of_not_gt
      intro hh
      exact hnot.2 ⟨hs, x, hx, k, hk, hh⟩
    have hnormA : ‖A₀ * (Real.sqrt Real.pi : ℂ)‖ =
        ‖A₀‖ * Real.sqrt Real.pi := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos)]
    have htri := norm_le_norm_add_norm_sub Z (A₀ * (Real.sqrt Real.pi : ℂ))
    have htri' := norm_le_norm_add_norm_sub (A₀ * (Real.sqrt Real.pi : ℂ)) Z
    rw [norm_sub_rev] at htri'
    rw [hnormA] at htri htri'
    have hAprodLo : c₀ * Real.sqrt Real.pi ≤ ‖A₀‖ * Real.sqrt Real.pi :=
      mul_le_mul_of_nonneg_right hAlo (Real.sqrt_nonneg Real.pi)
    have hAprodHi : ‖A₀‖ * Real.sqrt Real.pi ≤ B₀ * Real.sqrt Real.pi :=
      mul_le_mul_of_nonneg_right hAhi (Real.sqrt_nonneg Real.pi)
    dsimp [τ] at hclose
    have hlo : c ≤ ‖Z‖ := by
      dsimp [c, τ]
      linarith
    have hhi : ‖Z‖ ≤ B := by
      dsimp [B, τ]
      linarith
    exact hbad.elim (fun hh => (not_lt_of_ge hlo) hh)
      (fun hh => (not_lt_of_ge hhi) hh)
  have hh := (measureReal_mono (μ := birthParentLaw) hsub).trans
    (measureReal_union_le _ _)
  linarith

end HeightPaper.CountCoupling
