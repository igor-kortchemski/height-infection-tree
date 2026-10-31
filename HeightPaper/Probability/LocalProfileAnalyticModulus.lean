module

public import HeightPaper.Probability.LocalProfileStability
public import HeightPaper.Probability.LocalProfilePointwisePositive
public import HeightPaper.Analysis.AnalyticAmplitudeControl
public import HeightPaper.Probability.FiniteLocalProfileIntegrated

/-! # Uniform stochastic modulus for the local analytic profile -/

@[expose] public section

open MeasureTheory Set Metric
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

/-- Analyticity and disk upper tightness give a parameter-uniform modulus at
the real saddle. The radius is chosen before the epidemic parameter. -/
theorem localProfile_unshifted_disk_modulus_uniform {l₀ x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hr : 0 < r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ t > (0 : ℝ), t < r ∧ ∀ l ≥ l₀, ∀ n : ℕ,
      birthParentLaw.real {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
        ∃ z ∈ closedBall (x : ℂ) t,
          ε < ‖localUnshiftedRankProfileLimit l n q z -
            localUnshiftedRankProfileLimit l n q (x : ℂ)‖} < δ := by
  obtain ⟨B, hB, hupper⟩ := localProfile_unshifted_disk_upper_tight hl₀ hp hp2 hη
    hr.le hrR hRρ hright hwindow hδ
  let t := min (r / 2) (ε * r / (4 * B))
  have ht : 0 < t := by dsimp [t]; positivity
  have htr : t < r := (min_le_left _ _).trans_lt (by linarith)
  have hlin : (2 * B / r) * t < ε := by
    have hle : t ≤ ε * r / (4 * B) := min_le_right _ _
    have hh := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 2 * B / r)
    have heq : (2 * B / r) * (ε * r / (4 * B)) = ε / 2 := by
      field_simp
      ring
    rw [heq] at hh
    linarith
  refine ⟨t, ht, htr, ?_⟩
  intro l hl n
  let E : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ z ∈ closedBall (x : ℂ) t,
        ε < ‖localUnshiftedRankProfileLimit l n q z -
          localUnshiftedRankProfileLimit l n q (x : ℂ)‖}
  let U : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ z ∈ closedBall (x : ℂ) r, B < ‖localUnshiftedRankProfileLimit l n q z‖}
  have hsub : ∀ᵐ q ∂birthParentLaw, q ∈ E → q ∈ U := by
    filter_upwards [localUnshiftedRankProfileLimit_joint_ae_differentiable_disk
      (hl₀.trans_le hl) hp hp2 hη hr.le hrR hRρ hright (hwindow l hl) n]
      with q hq
    rintro ⟨hs, z, hz, hbad⟩
    by_contra hnot
    have hbound : ∀ w ∈ ball (x : ℂ) r,
        ‖localUnshiftedRankProfileLimit l n q w‖ ≤ B := by
      intro w hw
      exact le_of_not_gt (fun hh => hnot ⟨hs, w, ball_subset_closedBall hw, hh⟩)
    have hzb : z ∈ ball (x : ℂ) r :=
      mem_ball.mpr ((mem_closedBall.mp hz).trans_lt htr)
    have hh := analytic_norm_sub_center_le hr (hq hs) hbound hzb
    have hzt : ‖z - (x : ℂ)‖ ≤ t := by
      simpa only [dist_eq_norm] using (mem_closedBall.mp hz)
    have hnonneg : 0 ≤ 2 * B / r := by positivity
    have hle := mul_le_mul_of_nonneg_left hzt hnonneg
    exact (not_lt_of_ge (hh.trans (hle.trans hlin.le))) hbad
  have hm : birthParentLaw E ≤ birthParentLaw U := measure_mono_ae hsub
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hm).trans_lt (hupper l hl n)

/-- On a sufficiently small fixed disk around the saddle, the finite profile
is close to the local limit evaluated at the center, uniformly in parameter. -/
theorem uniform_finite_profile_centered_disk
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hr : 0 < r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ t > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real {q | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n q.1 i) ∧
        ∃ z ∈ closedBall (x : ℂ) t,
          ε < ‖finiteUnshiftedRankProfile l n q ⌊T * n⌋₊ z -
            localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖} < δ := by
  have hhalfε : 0 < ε / 2 := by positivity
  have hhalfδ : 0 < δ / 2 := by positivity
  obtain ⟨t, ht, htr, hmod⟩ := localProfile_unshifted_disk_modulus_uniform
    hl₀ hp hp2 hη hr hrR hRρ hright hwindow hhalfε hhalfδ
  obtain ⟨N, hcmp⟩ := uniform_finiteLocalProfile_comparison hI hl₀ hT hparams
    hIlower ⟨hp, hp2⟩ hη ht.le (htr.trans hrR) hRρ hright hwindow
    hhalfε hhalfδ
  refine ⟨t, ht, N, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let F := finiteLocalProfileBad l n H (closedBall (x : ℂ) t) (ε / 2)
  let G : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ z ∈ closedBall (x : ℂ) t,
        ε / 2 < ‖localUnshiftedRankProfileLimit l 0 q z -
          localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖}
  have hF : birthParentLaw.real F < δ / 2 := hcmp n hn l hl
  have hG : birthParentLaw.real G < δ / 2 := hmod l (hIlower l hl) 0
  have hsub : {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ z ∈ closedBall (x : ℂ) t,
        ε < ‖finiteUnshiftedRankProfile l n q H z -
          localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖} ⊆ F ∪ G := by
    rintro q ⟨hs, z, hz, hbad⟩
    by_cases hqF : q ∈ F
    · exact Or.inl hqF
    right
    have hls : ∀ i, 0 < (localWalk l q.1 i : ℝ) := by
      by_contra hh
      exact hqF ⟨hs, Or.inl (by exact_mod_cast hh)⟩
    have hdiff : ‖finiteUnshiftedRankProfile l n q H z -
        localUnshiftedRankProfileLimit l 0 q z‖ ≤ ε / 2 := by
      apply le_of_not_gt
      intro hh
      exact hqF ⟨hs, Or.inr ⟨z, hz, hh⟩⟩
    refine ⟨hls, z, hz, ?_⟩
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (finiteUnshiftedRankProfile l n q H z)
      (localUnshiftedRankProfileLimit l 0 q z)
      (localUnshiftedRankProfileLimit l 0 q (x : ℂ))
    linarith
  have hh := (measureReal_mono (μ := birthParentLaw) hsub).trans
    (measureReal_union_le F G)
  linarith

end HeightPaper.CountCoupling
