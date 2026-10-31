module

public import HeightPaper.Probability.FiniteProfileCompactCentral
public import HeightPaper.Probability.FiniteResidualCompactDisk
public import HeightPaper.Probability.LocalProfileCompactStability
public import HeightPaper.Probability.FiniteProfileAmplitude

/-! # Central residual amplitude uniformly over compact saddle tilts -/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

/-- The actual finite saddle amplitude is close, simultaneously near every
tilt in a compact real set, to the local limit at that tilt times the finite
entire normalizer residual at the tilt. -/
theorem finite_profileResidual_compact_centered_disk
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
          τ < ‖profileResidual (coupledTreeState l n q ⌊T * n⌋₊)
            (growthFactor l) (Real.log n) z -
            localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
              finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ q.1
                (Real.log n) (x : ℂ)‖} < δ := by
  have hquarter : 0 < δ / 4 := by positivity
  obtain ⟨r, hr, M, hM, hgeom, NR, hres⟩ :=
    finiteUnshiftedNormalizerResidual_compact_disk_bounds
      hI hl₀ hT hparams hIlower hK hKne hKd hquarter
  obtain ⟨B, hB, hupper⟩ :=
    localProfile_unshifted_compact_upper_tight hl₀ hK hKd hquarter
  have hε : 0 < τ / (3 * M) := by positivity
  obtain ⟨t₀, ht₀, NC, hcenter⟩ := uniform_finiteProfile_compact_centered_disk
    hI hl₀ hT hparams hIlower hK hKne hKd hε hquarter
  obtain ⟨NS, hsurv⟩ := uniform_survival_disagreement hI hT hparams hquarter
  let t := min (min (t₀ / 2) (r / 2)) (τ * r / (6 * B * M))
  have ht : 0 < t := by dsimp [t]; positivity
  have htm : t ≤ min (t₀ / 2) (r / 2) := min_le_left _ _
  have htt₀ : t < t₀ := (htm.trans (min_le_left _ _)).trans_lt (by linarith)
  have htr : t < r := (htm.trans (min_le_right _ _)).trans_lt (by linarith)
  have hsmall : B * (2 * M / r) * t ≤ τ / 3 := by
    have hle : t ≤ τ * r / (6 * B * M) := min_le_right _ _
    have hm := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ B * (2 * M / r))
    have heq : B * (2 * M / r) * (τ * r / (6 * B * M)) = τ / 3 := by
      field_simp
      ring
    rw [heq] at hm
    exact hm
  refine ⟨t, ht, max NR (max NC NS), ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let C : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ x ∈ K, ∃ z ∈ closedBall (x : ℂ) t₀,
        τ / (3 * M) < ‖finiteUnshiftedRankProfile l n q H z -
          localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖}
  let U : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ x ∈ K, B < ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖}
  let Q : Set (ℕ → ℝ) :=
    {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
      ∃ x ∈ K, ∃ z ∈ closedBall (x : ℂ) r,
        M < ‖finiteUnshiftedNormalizerResidual l n H u (Real.log n) z‖ ∨
          ‖finiteUnshiftedNormalizerResidual l n H u (Real.log n) z‖ < M⁻¹}
  let S : Set (ℕ → ℝ) :=
    {u | ¬((∀ i ≤ H, 0 < finiteWalk l n u i) ↔ ∀ i, 0 < localWalk l u i)}
  have hC : birthParentLaw.real C < δ / 4 :=
    hcenter n ((le_max_left _ _).trans ((le_max_right _ _).trans hn)) l hl
  have hU : birthParentLaw.real U < δ / 4 := hupper l (hIlower l hl) 0
  have hQ : birthParentLaw.real {q | q.1 ∈ Q} < δ / 4 :=
    (birthParentLaw_real_fst_le Q).trans_lt
      (hres n ((le_max_left _ _).trans hn) l hl)
  have hS : birthParentLaw.real {q | q.1 ∈ S} < δ / 4 :=
    (birthParentLaw_real_fst_le S).trans_lt
      (hsurv n ((le_max_right _ _).trans ((le_max_right _ _).trans hn)) l hl)
  have hsub : {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ x ∈ K, ∃ z ∈ closedBall (x : ℂ) t,
        τ < ‖profileResidual (coupledTreeState l n q H)
          (growthFactor l) (Real.log n) z -
          localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
            finiteUnshiftedNormalizerResidual l n H q.1
              (Real.log n) (x : ℂ)‖} ⊆
      ((C ∪ U) ∪ {q | q.1 ∈ Q}) ∪ {q | q.1 ∈ S} := by
    rintro q ⟨hs, y, hy, z, hz, hbad⟩
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    have hls : ∀ i, 0 < (localWalk l q.1 i : ℝ) := by
      have he : (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ↔
          ∀ i, 0 < localWalk l q.1 i := not_not.mp hnot.2
      exact_mod_cast he.mp hs
    have hL : ‖localUnshiftedRankProfileLimit l 0 q (y : ℂ)‖ ≤ B := by
      apply le_of_not_gt
      intro hh
      exact hnot.1.1.2 ⟨hls, y, hy, hh⟩
    have hG : ∀ w ∈ ball (y : ℂ) r,
        ‖finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n) w‖ ≤ M := by
      intro w hw
      apply le_of_not_gt
      intro hh
      exact hnot.1.2 ⟨hs, y, hy, w, ball_subset_closedBall hw, Or.inl hh⟩
    have hclose : ‖finiteUnshiftedRankProfile l n q H z -
        localUnshiftedRankProfileLimit l 0 q (y : ℂ)‖ ≤ τ / (3 * M) := by
      apply le_of_not_gt
      intro hh
      exact hnot.1.1.1 ⟨hs, y, hy, z,
        closedBall_subset_closedBall htt₀.le hz, hh⟩
    have hzb : z ∈ ball (y : ℂ) r :=
      mem_ball.mpr ((mem_closedBall.mp hz).trans_lt htr)
    have hprod := analytic_product_amplitude_error hr hM.le
      (differentiable_finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n)).differentiableOn
      hG hzb hclose
    have hzt : ‖z - (y : ℂ)‖ ≤ t := by
      simpa only [dist_eq_norm] using (mem_closedBall.mp hz)
    have hmul := mul_le_mul_of_nonneg_left hzt (by positivity : 0 ≤ B * (2 * M / r))
    have hprod' : ‖finiteUnshiftedRankProfile l n q H z *
        finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n) z -
        localUnshiftedRankProfileLimit l 0 q (y : ℂ) *
          finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n) (y : ℂ)‖ ≤
        τ / 3 + τ / 3 := by
      calc
        _ ≤ (τ / (3 * M)) * M +
            ‖localUnshiftedRankProfileLimit l 0 q (y : ℂ)‖ *
              (2 * M / r) * ‖z - (y : ℂ)‖ := hprod
        _ ≤ τ / 3 + B * (2 * M / r) * t := by
          have heq : (τ / (3 * M)) * M = τ / 3 := by field_simp
          rw [heq]
          have hmulL := mul_le_mul_of_nonneg_right hL
            (by positivity : 0 ≤ (2 * M / r) * ‖z - (y : ℂ)‖)
          nlinarith [hmul, hmulL]
        _ ≤ τ / 3 + τ / 3 := by linarith
    have hexp : 1 ≤ (Complex.exp z).re :=
      (hgeom l hl y hy z (closedBall_subset_closedBall htr.le hz)).2
    rw [profileResidual_eq_unshifted_mul_residual l (Real.log n) n H q hexp] at hbad
    linarith
  have hh := (measureReal_mono (μ := birthParentLaw) hsub).trans
    ((measureReal_union_le _ _).trans
      (add_le_add
        ((measureReal_union_le _ _).trans
          (add_le_add (measureReal_union_le _ _) le_rfl)) le_rfl))
  linarith

end HeightPaper.CountCoupling
