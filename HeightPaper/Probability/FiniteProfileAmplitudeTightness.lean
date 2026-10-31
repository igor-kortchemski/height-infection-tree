module

public import HeightPaper.Probability.FiniteProfileAmplitude
public import HeightPaper.Probability.FiniteResidualTightness
public import HeightPaper.Probability.FiniteLocalProfileIntegrated
public import HeightPaper.Probability.LocalProfileUniformPositive

/-! # Uniform real-tilt bounds for the actual finite saddle amplitude -/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

/-- On finite survival, the entire residual amplitude at real tilts stays
between positive deterministic constants with high probability. The constants
are uniform in the epidemic parameter and every admissible tilt in the compact. -/
theorem finite_profileResidual_compact_tight
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    {K : Set ℝ} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKd : K ⊆ Ioo 0 (profileRoot l₀))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c > (0 : ℝ), ∃ B > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real {q | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n q.1 i) ∧
        ∃ x ∈ K, ‖profileResidual (coupledTreeState l n q ⌊T * n⌋₊)
          (growthFactor l) (Real.log n) (x : ℂ)‖ < c ∨
          B < ‖profileResidual (coupledTreeState l n q ⌊T * n⌋₊)
            (growthFactor l) (Real.log n) (x : ℂ)‖} < δ := by
  have hd : 0 < δ / 4 := by positivity
  obtain ⟨c₀, hc₀, hlow⟩ := localProfile_unshifted_compact_lower_tight_nnreal
    hl₀ hI hIlower hK hKd hd
  obtain ⟨B₀, hB₀, hupp⟩ := localProfile_unshifted_compact_upper_tight
    hl₀ hK hKd hd
  have hKres : ∀ l ∈ I, ∀ z ∈ Complex.ofReal '' K, z.re ≤ 2 * profileRoot l := by
    intro l hl z hz
    obtain ⟨x, hx, rfl⟩ := hz
    simp only [Complex.ofReal_re]
    have hr := profileRoot_mono_supercritical hl₀ (hIlower l hl)
    have hroot := (profileRoot_pos (hparams l hl).1).le
    linarith [(hKd hx).2]
  have hKexp : ∀ z ∈ Complex.ofReal '' K, 1 ≤ (Complex.exp z).re := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    simpa only [← Complex.ofReal_exp, Complex.ofReal_re] using
      (Real.one_le_exp_iff.mpr (hKd hx).1.le)
  obtain ⟨M, hM, NR, hres⟩ := finiteUnshiftedNormalizerResidual_uniform_bounds
    hI hT hparams hKres hKexp hd
  obtain ⟨NC, hcmp⟩ := uniform_finiteLocalProfile_compact_comparison
    hI hl₀ hT hparams hIlower hK hKne hKd (half_pos hc₀) hd
  let c : ℝ := c₀ / (2 * M)
  let B : ℝ := (B₀ + c₀ / 2) * M
  have hc : 0 < c := by dsimp [c]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨c, hc, B, hB, max NR NC, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let F := finiteLocalProfileBad l n H (Complex.ofReal '' K) (c₀ / 2)
  let L : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ x ∈ K, ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ < c₀}
  let U : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ x ∈ K, B₀ < ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖}
  let R : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ z ∈ Complex.ofReal '' K,
        M < ‖finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n) z‖ ∨
          ‖finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n) z‖ < M⁻¹}
  have hF : birthParentLaw.real F < δ / 4 := hcmp n (le_max_right _ _ |>.trans hn) l hl
  have hL : birthParentLaw.real L < δ / 4 := hlow l hl 0
  have hU : birthParentLaw.real U < δ / 4 := hupp l (hIlower l hl) 0
  have hR : birthParentLaw.real R < δ / 4 :=
    (birthParentLaw_real_fst_le _).trans_lt (hres n ((le_max_left _ _).trans hn) l hl)
  have hsub : {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ x ∈ K, ‖profileResidual (coupledTreeState l n q H)
        (growthFactor l) (Real.log n) (x : ℂ)‖ < c ∨
        B < ‖profileResidual (coupledTreeState l n q H)
          (growthFactor l) (Real.log n) (x : ℂ)‖} ⊆ (F ∪ L) ∪ (U ∪ R) := by
    rintro q ⟨hs, x, hx, hbad⟩
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    have hls : ∀ i, 0 < (localWalk l q.1 i : ℝ) := by
      by_contra hh
      exact hnot.1.1 ⟨hs, Or.inl (by exact_mod_cast hh)⟩
    have hdiff : ‖finiteUnshiftedRankProfile l n q H (x : ℂ) -
        localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ ≤ c₀ / 2 := by
      apply le_of_not_gt
      intro hh
      exact hnot.1.1 ⟨hs, Or.inr ⟨(x : ℂ), ⟨x, hx, rfl⟩, hh⟩⟩
    have hlimlo : c₀ ≤ ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ :=
      le_of_not_gt (fun hh => hnot.1.2 ⟨hls, x, hx, hh⟩)
    have hlimhi : ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ ≤ B₀ :=
      le_of_not_gt (fun hh => hnot.2.1 ⟨hls, x, hx, hh⟩)
    have hreslo : M⁻¹ ≤ ‖finiteUnshiftedNormalizerResidual l n H q.1
        (Real.log n) (x : ℂ)‖ := by
      apply le_of_not_gt
      intro hh
      exact hnot.2.2 ⟨hs, (x : ℂ), ⟨x, hx, rfl⟩, Or.inr hh⟩
    have hreshi : ‖finiteUnshiftedNormalizerResidual l n H q.1
        (Real.log n) (x : ℂ)‖ ≤ M := by
      apply le_of_not_gt
      intro hh
      exact hnot.2.2 ⟨hs, (x : ℂ), ⟨x, hx, rfl⟩, Or.inl hh⟩
    have hproflo : c₀ / 2 ≤ ‖finiteUnshiftedRankProfile l n q H (x : ℂ)‖ := by
      have ht := norm_le_norm_add_norm_sub
        (finiteUnshiftedRankProfile l n q H (x : ℂ))
        (localUnshiftedRankProfileLimit l 0 q (x : ℂ))
      linarith
    have hprofhi : ‖finiteUnshiftedRankProfile l n q H (x : ℂ)‖ ≤ B₀ + c₀ / 2 := by
      have ht := norm_le_norm_add_norm_sub
        (localUnshiftedRankProfileLimit l 0 q (x : ℂ))
        (finiteUnshiftedRankProfile l n q H (x : ℂ))
      rw [norm_sub_rev] at ht
      linarith
    have hexp : 1 ≤ (Complex.exp (x : ℂ)).re := hKexp _ ⟨x, hx, rfl⟩
    have hamp : ‖profileResidual (coupledTreeState l n q H)
        (growthFactor l) (Real.log n) (x : ℂ)‖ =
        ‖finiteUnshiftedRankProfile l n q H (x : ℂ)‖ *
          ‖finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n) (x : ℂ)‖ := by
      rw [profileResidual_eq_unshifted_mul_residual l (Real.log n) n H q hexp, norm_mul]
    have hlo : c ≤ ‖profileResidual (coupledTreeState l n q H)
        (growthFactor l) (Real.log n) (x : ℂ)‖ := by
      rw [hamp]
      have ht := mul_le_mul hproflo hreslo (inv_nonneg.mpr hM.le)
        (norm_nonneg (finiteUnshiftedRankProfile l n q H (x : ℂ)))
      have heq : c = c₀ / 2 * M⁻¹ := by dsimp [c]; field_simp
      rw [heq]
      exact ht
    have hhi : ‖profileResidual (coupledTreeState l n q H)
        (growthFactor l) (Real.log n) (x : ℂ)‖ ≤ B := by
      rw [hamp]
      exact (mul_le_mul hprofhi hreshi (norm_nonneg _) (by positivity)).trans_eq rfl
    exact hbad.elim (fun hh => (not_lt_of_ge hlo) hh) (fun hh => (not_lt_of_ge hhi) hh)
  have hh := (measureReal_mono (μ := birthParentLaw) hsub).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (measureReal_union_le _ _) (measureReal_union_le _ _)))
  linarith

end HeightPaper.CountCoupling
