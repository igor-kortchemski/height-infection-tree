module

public import HeightPaper.Probability.FiniteResidualTightness
public import HeightPaper.Probability.LocalProfileCarrier

/-! # Entire residual bounds near compact real saddle sets -/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal

namespace HeightPaper.CountCoupling

/-- The entire finite normalizer residual has simultaneous upper and lower
stochastic bounds on one complex neighborhood of a compact admissible set. -/
theorem finiteUnshiftedNormalizerResidual_compact_disk_bounds
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    {K : Set ℝ} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKd : K ⊆ Ioo 0 (profileRoot l₀))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t > (0 : ℝ), ∃ M > (0 : ℝ),
      (∀ l ∈ I, ∀ x ∈ K, ∀ z ∈ closedBall (x : ℂ) t,
        z.re ≤ 2 * profileRoot l ∧ 1 ≤ (Complex.exp z).re) ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real {u | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u i) ∧
        ∃ x ∈ K, ∃ z ∈ closedBall (x : ℂ) t,
          M < ‖finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ u
            (Real.log n) z‖ ∨
          ‖finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ u
            (Real.log n) z‖ < M⁻¹} < δ := by
  classical
  have hlocal : ∀ x : K, ∃ r > (0 : ℝ),
      (∀ l ∈ I, ∀ z ∈ closedBall ((x : ℝ) : ℂ) r,
        z.re ≤ 2 * profileRoot l) ∧
      (∀ z ∈ closedBall ((x : ℝ) : ℂ) r, 1 ≤ (Complex.exp z).re) := by
    intro x
    obtain ⟨p, hp, η, hη, ρ, hρ, hw⟩ :=
      exists_localProfile_unshifted_moment_disk hl₀ (hKd x.property).1 (hKd x.property).2
    refine ⟨ρ / 2, by positivity, ?_, ?_⟩
    · intro l hl z hz
      have hdist : dist z ((x : ℝ) : ℂ) < ρ :=
        (mem_closedBall.mp hz).trans_lt (by linarith)
      have hwin := (hw (l : ℝ) (hIlower l hl) z hdist).2
      have hroot : 0 ≤ profileRoot l := (profileRoot_pos (hparams l hl).1).le
      linarith [hwin.2.1]
    · intro z hz
      have hdist : dist z ((x : ℝ) : ℂ) < ρ :=
        (mem_closedBall.mp hz).trans_lt (by linarith)
      exact (hw l₀ le_rfl z hdist).1.le
  choose r hr hroot hexp using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℝ) (r x / 4))
    (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩,
      mem_ball_self (div_pos (hr ⟨x, hx⟩) (by norm_num))⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hy, _⟩ := mem_iUnion.mp hy
    exact ⟨y, hy⟩
  let t : ℝ := s.inf' hsne (fun x => r x / 4)
  have ht : 0 < t := (Finset.lt_inf'_iff hsne).mpr (fun x _ =>
    div_pos (hr x) (by norm_num))
  let U : Set ℂ := ⋃ x ∈ s, closedBall ((x : ℝ) : ℂ) (r x)
  have hUroot : ∀ l ∈ I, ∀ z ∈ U, z.re ≤ 2 * profileRoot l := by
    intro l hl z hz
    obtain ⟨x, hx⟩ := mem_iUnion.mp hz
    obtain ⟨_, hzx⟩ := mem_iUnion.mp hx
    exact hroot x l hl z hzx
  have hUexp : ∀ z ∈ U, 1 ≤ (Complex.exp z).re := by
    intro z hz
    obtain ⟨x, hx⟩ := mem_iUnion.mp hz
    obtain ⟨_, hzx⟩ := mem_iUnion.mp hx
    exact hexp x z hzx
  obtain ⟨M, hM, N, hres⟩ := finiteUnshiftedNormalizerResidual_uniform_bounds
    hI hT hparams hUroot hUexp hδ
  have hnearU : ∀ x ∈ K, ∀ z ∈ closedBall (x : ℂ) t, z ∈ U := by
    intro y hy z hz
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hs hy)
    obtain ⟨hx, hyx⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, ?_⟩⟩
    have hyxC : dist (y : ℂ) ((x : ℝ) : ℂ) < r x / 4 := by
      simpa only [mem_ball, Complex.isometry_ofReal.dist_eq] using hyx
    have hzt : dist z (y : ℂ) ≤ t := mem_closedBall.mp hz
    have htr : t ≤ r x / 4 := Finset.inf'_le _ hx
    exact mem_closedBall.mpr (by linarith [dist_triangle z (y : ℂ) ((x : ℝ) : ℂ)])
  refine ⟨t, ht, M, hM, ?_, N, ?_⟩
  · intro l hl x hx z hz
    exact ⟨hUroot l hl z (hnearU x hx z hz),
      hUexp z (hnearU x hx z hz)⟩
  intro n hn l hl
  have hsub : {u | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u i) ∧
      ∃ x ∈ K, ∃ z ∈ closedBall (x : ℂ) t,
        M < ‖finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ u
          (Real.log n) z‖ ∨
        ‖finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ u
          (Real.log n) z‖ < M⁻¹} ⊆
      {u | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u i) ∧ ∃ z ∈ U,
        M < ‖finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ u
          (Real.log n) z‖ ∨
        ‖finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ u
          (Real.log n) z‖ < M⁻¹} := by
    rintro u ⟨hu, y, hy, z, hz, hbad⟩
    exact ⟨hu, z, hnearU y hy z hz, hbad⟩
  exact (measureReal_mono (μ := uniformLaw) hsub).trans_lt (hres n hn l hl)

end HeightPaper.CountCoupling
