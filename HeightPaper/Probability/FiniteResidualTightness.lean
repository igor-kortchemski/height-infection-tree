module

public import HeightPaper.Probability.FiniteAnalyticResidual
public import HeightPaper.Analysis.ProfileTimeScale
public import HeightPaper.Analysis.ComplexMomentExponent

/-! # Uniform upper and lower bounds for the entire finite residual -/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper.CountCoupling

theorem finiteUnshiftedNormalizerResidual_uniform_bounds
    {I : Set ℝ≥0} (hI : IsCompact I) {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {K : Set ℂ} (hK : ∀ l ∈ I, ∀ z ∈ K, z.re ≤ 2 * profileRoot l)
    (hexp : ∀ z ∈ K, 1 ≤ (Complex.exp z).re) {ε : ℝ} (hε : 0 < ε) :
    ∃ M > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I, uniformLaw.real
      {u | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u i) ∧ ∃ z ∈ K,
        M < ‖finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ u (Real.log n) z‖ ∨
          ‖finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ u (Real.log n) z‖ < M⁻¹} < ε := by
  by_cases hne : I.Nonempty
  swap
  · exact ⟨1, zero_lt_one, 0, fun _ _ l hl => False.elim (hne ⟨l, hl⟩)⟩
  obtain ⟨l₀, hl₀, hmin⟩ := hI.exists_isLeast hne
  have hl₀1 := (hparams l₀ hl₀).1
  have hhalf := half_pos hε
  obtain ⟨J, NJ, hcut⟩ := finiteSafeCutoff_survival_uniform_tight hI hT hparams hhalf
  obtain ⟨R, hR, NR, herr⟩ := finiteNormalizerLogError_uniform_tight hI hT hparams hK hhalf
  obtain ⟨D, hD, ND, hscale⟩ := log_floor_sub_log_bounded hT
  let G := growthFactor l₀ * (Real.exp 2 + 1) * D
  have hG : 0 ≤ G := by dsimp [G]; positivity [growthFactor_pos hl₀1]
  let M := (2 + Real.exp 2) ^ J * Real.exp (R + G)
  have hM : 0 < M := by dsimp [M]; positivity
  have hpow : 1 ≤ (2 + Real.exp 2) ^ J := one_le_pow₀ (by linarith [Real.exp_pos 2])
  have hExpM : Real.exp (R + G) ≤ M := le_mul_of_one_le_left (Real.exp_pos _).le hpow
  have hInv : M⁻¹ ≤ Real.exp (-(R + G)) := by
    simpa only [one_div, Real.exp_neg] using one_div_le_one_div_of_le (Real.exp_pos _) hExpM
  refine ⟨M, hM, NJ + NR + ND, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let E₀ : Set (ℕ → ℝ) := {u | J < if ∀ i ≤ H, 0 < finiteWalk l n u i then
    finiteSafeCutoff l n H u else 0}
  let E₁ : Set (ℕ → ℝ) := {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
    ∃ k ≤ H, finiteSafeCutoff l n H u ≤ k ∧ ∃ z ∈ K,
      R < ‖finiteNormalizerLogError l n H u k z‖}
  have hp₀ : uniformLaw.real E₀ < ε / 2 := hcut n (by omega) l hl
  have hp₁ : uniformLaw.real E₁ < ε / 2 := herr n (by omega) l hl
  have hsub : {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧ ∃ z ∈ K,
      M < ‖finiteUnshiftedNormalizerResidual l n H u (Real.log n) z‖ ∨
        ‖finiteUnshiftedNormalizerResidual l n H u (Real.log n) z‖ < M⁻¹} ⊆ E₀ ∪ E₁ := by
    rintro u ⟨hs, z, hz, hbad⟩
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    have hJ : finiteSafeCutoff l n H u ≤ J := by
      apply le_of_not_gt
      intro hj
      apply hnot.1
      change J < if ∀ i ≤ H, 0 < finiteWalk l n u i then finiteSafeCutoff l n H u else 0
      rw [ite_eq_left hs]
      exact hj
    have he : ‖finiteNormalizerLogError l n H u H z‖ ≤ R :=
      le_of_not_gt (fun he => hnot.2 ⟨hs, H, le_rfl, finiteSafeCutoff_le_horizon l n H u, z, hz, he⟩)
    have hzroot := hK l hl z hz
    have hz2 : z.re ≤ 2 := hzroot.trans (by linarith [profileRoot_lt_one (hparams l hl).1])
    have hg : |growthFactor l| ≤ growthFactor l₀ := by
      rw [abs_of_pos (growthFactor_pos (hparams l hl).1)]
      exact growthFactor_antitone hl₀1 (by exact_mod_cast hmin hl)
    have hscl : ‖(growthFactor l : ℂ) * (Complex.exp z - 1) *
        ((Real.log H - Real.log n : ℝ) : ℂ)‖ ≤ G := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hzexp := norm_exp_sub_one_le_of_re_le hz2
      have hlog := (hscale n (by omega)).2.2
      have hg0 : 0 ≤ growthFactor l₀ := (growthFactor_pos hl₀1).le
      change _ ≤ growthFactor l₀ * (Real.exp 2 + 1) * D
      gcongr
    have hu := norm_finiteUnshiftedNormalizerResidual_le hs hJ hzroot hz2 he hscl
    have hd := exp_neg_le_norm_finiteUnshiftedNormalizerResidual hs hzroot (hexp z hz) he hscl
    rcases hbad with hbad | hbad
    · exact not_lt_of_ge hu hbad
    · exact not_lt_of_ge (hInv.trans hd) hbad
  have hb := (measureReal_mono (μ := uniformLaw) hsub).trans (measureReal_union_le _ _)
  linarith

end HeightPaper.CountCoupling
