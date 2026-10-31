module

public import HeightPaper.Probability.FiniteShiftedLocalPrefix
public import HeightPaper.Probability.FiniteLocalProfileMovingTime

/-!
# Joint finite-to-local convergence of the shifted profile

At a diverging preterminal time, the actual shifted finite profile approaches
the canonical shifted local analytic limit on the common coupling space.
The exact cutoff/word prefix identity reduces this to the already proved
unshifted comparison.
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

open Model

/-- Joint-probability comparison at one positive real tilt, uniformly over a
compact parameter family. This is the coupling term in the paper's four-term
comparison with the limiting martingale. -/
theorem uniform_finiteShiftedProfile_localLimit_moving_time_probability
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (hp : p ∈ Ioc (1 : ℝ) 2) (hη : 0 < η)
    (hr : 0 ≤ r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real {q | q.1 ∈ finiteSurvival l n ⌊T * n⌋₊ ∧
        q.1 ∈ localSurvival l ∧
        finiteSafeCutoff l n ⌊T * n⌋₊ q.1 ≤ A n ∧
        ε < ‖finiteShiftedRankProfile l n ⌊T * n⌋₊ q (A n) (x : ℂ) -
          localRankProfileLimit l 0 q (x : ℂ)‖} < δ := by
  let d := δ / 3
  have hd : 0 < d := by positivity
  obtain ⟨K, hK⟩ := localSafeCutoff_uniform_tight hl₀ hd
  obtain ⟨Nprefix, hprefix⟩ :=
    finiteLocal_cutoff_and_prefix_disagreement_uniform hI hT hparams hd
  let C : ℝ := (2 + Real.exp x) ^ K
  have hC : 0 < C := by dsimp [C]; positivity
  have hεC : 0 < ε / C := div_pos hε hC
  obtain ⟨Nprofile, hprofile⟩ :=
    uniform_finiteLocalProfile_moving_time_comparison hI hl₀ hT
      hparams hIlower hp hη hr hrR hRρ hright hwindow
      A hA hAH hεC hd
  refine ⟨max Nprefix Nprofile, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let E₁ : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | q.1 ∈ finiteSurvival l n H ∧ q.1 ∈ localSurvival l ∧
      (finiteSafeCutoff l n H q.1 ≠ localSafeCutoff l q.1 ∨
        ∃ i ≤ localSafeCutoff l q.1,
          finiteWalk l n q.1 i ≠ localWalk l q.1 i)}
  let E₂ : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | K < localSafeCutoff l q.1}
  let E₃ := finiteLocalProfileMovingTimeBad l n H (A n)
    (closedBall (x : ℂ) r) (ε / C)
  have h₁ : birthParentLaw.real E₁ < d :=
    (birthParentLaw_real_fst_le _).trans_lt
      (hprefix n ((le_max_left _ _).trans hn) l hl)
  have h₂ : birthParentLaw.real E₂ ≤ d :=
    (birthParentLaw_real_fst_le _).trans (hK l (hIlower l hl))
  have h₃ : birthParentLaw.real E₃ < d :=
    hprofile n ((le_max_right _ _).trans hn) l hl
  have hsub : {q | q.1 ∈ finiteSurvival l n H ∧
      q.1 ∈ localSurvival l ∧
      finiteSafeCutoff l n H q.1 ≤ A n ∧
      ε < ‖finiteShiftedRankProfile l n H q (A n) (x : ℂ) -
        localRankProfileLimit l 0 q (x : ℂ)‖} ⊆ E₁ ∪ (E₂ ∪ E₃) := by
    rintro q ⟨hs, hloc, hJ, hbad⟩
    by_contra hnot
    have hnot₁ : q ∉ E₁ := fun h ↦ hnot (Or.inl h)
    have hnot₂ : q ∉ E₂ := fun h ↦ hnot (Or.inr (Or.inl h))
    have hnot₃ : q ∉ E₃ := fun h ↦ hnot (Or.inr (Or.inr h))
    have hJexact : finiteSafeCutoff l n H q.1 = localSafeCutoff l q.1 := by
      by_contra he
      exact hnot₁ ⟨hs, hloc, Or.inl he⟩
    have hwalk : ∀ i ≤ localSafeCutoff l q.1,
        finiteWalk l n q.1 i = localWalk l q.1 i := by
      intro i hi
      by_contra he
      exact hnot₁ ⟨hs, hloc, Or.inr ⟨i, hi, he⟩⟩
    have hJK : localSafeCutoff l q.1 ≤ K := le_of_not_gt hnot₂
    have hsmall : ‖finiteUnshiftedRankProfile l n q (A n) (x : ℂ) -
        localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ ≤ ε / C := by
      apply le_of_not_gt
      intro he
      exact hnot₃ ⟨hs, Or.inr ⟨(x : ℂ),
        mem_closedBall_self hr, he⟩⟩
    have hmain := finiteShiftedRankProfile_sub_localLimit_norm_le
      l n H q (A n) K x hx.1.le hJ hJK hJexact hwalk
    have hεeq : C * (ε / C) = ε := mul_div_cancel₀ ε hC.ne'
    exact (not_lt_of_ge (hmain.trans
      ((mul_le_mul_of_nonneg_left hsmall hC.le).trans_eq hεeq))) hbad
  have hm := measureReal_mono (μ := birthParentLaw) hsub
  have hu := measureReal_union_le (μ := birthParentLaw) E₁ (E₂ ∪ E₃)
  have hu₂ := measureReal_union_le (μ := birthParentLaw) E₂ E₃
  change birthParentLaw.real {q | q.1 ∈ finiteSurvival l n H ∧
    q.1 ∈ localSurvival l ∧
    finiteSafeCutoff l n H q.1 ≤ A n ∧
    ε < ‖finiteShiftedRankProfile l n H q (A n) (x : ℂ) -
      localRankProfileLimit l 0 q (x : ℂ)‖} < δ
  dsimp [d] at h₁ h₂ h₃
  linarith

/-- The analytic moment window is supplied automatically at every admissible
positive real tilt. Thus the finite shifted profile converges jointly in
probability to the canonical local shifted limit at any diverging preterminal
observation time, on joint survival and after the safe cutoff. -/
theorem uniform_finiteShiftedProfile_localLimit_moving_time_probability_of_real_tilt
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real {q | q.1 ∈ finiteSurvival l n ⌊T * n⌋₊ ∧
        q.1 ∈ localSurvival l ∧
        finiteSafeCutoff l n ⌊T * n⌋₊ q.1 ≤ A n ∧
        ε < ‖finiteShiftedRankProfile l n ⌊T * n⌋₊ q (A n) (x : ℂ) -
          localRankProfileLimit l 0 q (x : ℂ)‖} < δ := by
  obtain ⟨p, hp, η, hη, ρ, hρ, hw⟩ :=
    exists_localProfile_unshifted_moment_disk hl₀ hx.1 hx.2
  have hr : 0 ≤ ρ / 4 := by positivity
  have hrR : ρ / 4 < ρ / 2 := by linarith
  have hRρ : ρ / 2 < ρ := by linarith
  have hright : ∀ z ∈ closedBall (x : ℂ) (ρ / 2),
      1 ≤ (Complex.exp z).re := by
    intro z hz
    exact (hw l₀ le_rfl z ((mem_closedBall.mp hz).trans_lt hRρ)).1.le
  have hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η :=
    fun l hl z hz ↦ (hw l hl z hz).2
  exact uniform_finiteShiftedProfile_localLimit_moving_time_probability
    hI hl₀ hT hparams hIlower hx ⟨hp.1, hp.2.le⟩ hη
    hr hrR hRρ hright hwindow A hA hAH hε hδ

end HeightPaper.CountCoupling
