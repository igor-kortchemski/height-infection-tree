module

public import HeightPaper.Probability.FiniteLocalProfileIntegrated
public import HeightPaper.Probability.LocalProfileCompactModulus

/-!
# Finite local profile comparison at diverging observation times

The comparison at a fixed macroscopic horizon and the uniform finite profile
tail imply the same local approximation at any diverging earlier time. This is
one of the estimates needed for the source's small-tilt perturbation lemma.
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

def finiteLocalProfileMovingTimeBad (l : ℝ) (n H j : ℕ)
    (K : Set ℂ) (ε : ℝ) : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
    (¬(∀ i, 0 < localWalk l q.1 i) ∨ ∃ z ∈ K,
      ε < ‖finiteUnshiftedRankProfile l n q j z -
        localUnshiftedRankProfileLimit l 0 q z‖)}

/-- The actual coupled finite profile at any diverging time below a fixed
preterminal horizon approaches the same local analytic profile, uniformly
over the compact epidemic-rate family. -/
theorem uniform_finiteLocalProfile_moving_time_comparison
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
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
      birthParentLaw.real (finiteLocalProfileMovingTimeBad l n
        ⌊T * n⌋₊ (A n) (closedBall (x : ℂ) r) ε) < δ := by
  have hhalfε : 0 < ε / 2 := half_pos hε
  have hhalfδ : 0 < δ / 2 := half_pos hδ
  have hfinitewindow : ∀ l ∈ I, ∀ z ∈ closedBall (x : ℂ) R,
      0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η := by
    intro l hl z hz
    obtain ⟨hz0, hzroot, _, hm⟩ :=
      hwindow l (hIlower l hl) z ((mem_closedBall.mp hz).trans_lt hRρ)
    have hroot : 0 ≤ profileRoot l := (profileRoot_pos (hparams l hl).1).le
    exact ⟨hz0, by linarith, hm⟩
  have hexp : ∀ z ∈ closedBall (x : ℂ) r, 1 ≤ (Complex.exp z).re :=
    fun z hz ↦ hright z (closedBall_subset_closedBall hrR.le hz)
  obtain ⟨Nfixed, hfixed⟩ :=
    uniform_finiteLocalProfile_comparison hI hl₀ hT hparams hIlower
      hp hη hr hrR hRρ hright hwindow hhalfε hhalfδ
  obtain ⟨J, Ntail, hJ, htail⟩ :=
    finiteUnshiftedProfile_disk_tail_uniform hI hT hparams (x : ℂ)
      hr hrR hp hη hfinitewindow hexp hhalfε hhalfδ
  obtain ⟨NA, hNA⟩ := eventually_atTop.mp (hA.eventually_ge_atTop J)
  refine ⟨max Nfixed (max Ntail NA), ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let K := closedBall (x : ℂ) r
  have hnfixed : Nfixed ≤ n := (le_max_left _ _).trans hn
  have hntail : Ntail ≤ n := (le_max_left _ _).trans
    ((le_max_right _ _).trans hn)
  have hnA : NA ≤ n := (le_max_right _ _).trans
    ((le_max_right _ _).trans hn)
  have hAf : birthParentLaw.real (finiteLocalProfileBad l n H K (ε / 2)) <
      δ / 2 := hfixed n hnfixed l hl
  have hAt : birthParentLaw.real
      (finiteUnshiftedProfileDiskBad l n H (A n) K (ε / 2)) < δ / 2 :=
    (htail n hntail).2 l hl (A n) (hNA n hnA) (hAH n)
  have hsub : finiteLocalProfileMovingTimeBad l n H (A n) K ε ⊆
      finiteLocalProfileBad l n H K (ε / 2) ∪
        finiteUnshiftedProfileDiskBad l n H (A n) K (ε / 2) := by
    rintro q ⟨hs, hbad⟩
    rcases hbad with hnosurv | ⟨z, hz, he⟩
    · exact Or.inl ⟨hs, Or.inl hnosurv⟩
    by_contra hnot
    have hfixedGood : ‖finiteUnshiftedRankProfile l n q H z -
        localUnshiftedRankProfileLimit l 0 q z‖ ≤ ε / 2 := by
      have hnotF : q ∉ finiteLocalProfileBad l n H K (ε / 2) :=
        fun hq ↦ hnot (Or.inl hq)
      exact le_of_not_gt (fun hh ↦ hnotF ⟨hs, Or.inr ⟨z, hz, hh⟩⟩)
    have htailGood : ‖finiteUnshiftedRankProfile l n q H z -
        finiteUnshiftedRankProfile l n q (A n) z‖ ≤ ε / 2 := by
      have hnotT : q ∉ finiteUnshiftedProfileDiskBad l n H (A n) K (ε / 2) :=
        fun hq ↦ hnot (Or.inr hq)
      exact le_of_not_gt (fun hh ↦ hnotT ⟨hs, z, hz, hh⟩)
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (finiteUnshiftedRankProfile l n q (A n) z)
      (finiteUnshiftedRankProfile l n q H z)
      (localUnshiftedRankProfileLimit l 0 q z)
    rw [norm_sub_rev (finiteUnshiftedRankProfile l n q (A n) z)
      (finiteUnshiftedRankProfile l n q H z)] at htri
    linarith
  have hb := (measureReal_mono (μ := birthParentLaw) hsub).trans
    (measureReal_union_le _ _)
  linarith

def finiteProfileMovingTimeTiltBad (l : ℝ) (n H j : ℕ)
    (x t ε : ℝ) : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
    ∃ z ∈ closedBall (x : ℂ) t,
      ε < ‖finiteUnshiftedRankProfile l n q j z -
        finiteUnshiftedRankProfile l n q j (x : ℂ)‖}

/-- The finite profile at a diverging observation time has a stochastic
complex-tilt modulus on the survival event, uniformly in the epidemic rate.
The radius is fixed after the probability tolerance. -/
theorem uniform_finiteProfile_moving_time_tilt_modulus
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (hp : p ∈ Ioc (1 : ℝ) 2) (hη : 0 < η)
    (hr : 0 < r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ t > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real (finiteProfileMovingTimeTiltBad l n
        ⌊T * n⌋₊ (A n) x t ε) < δ := by
  have hthirdε : 0 < ε / 3 := by positivity
  have hhalfδ : 0 < δ / 2 := half_pos hδ
  obtain ⟨t₀, ht₀, hmod⟩ :=
    localProfile_unshifted_compact_modulus_uniform hl₀ isCompact_singleton
      (by simpa only [singleton_subset_iff] using hx)
      hthirdε hhalfδ
  obtain ⟨N, happrox⟩ :=
    uniform_finiteLocalProfile_moving_time_comparison hI hl₀ hT
      hparams hIlower hp hη hr.le hrR hRρ hright hwindow
      A hA hAH hthirdε hhalfδ
  let t := min r t₀
  have ht : 0 < t := lt_min hr ht₀
  refine ⟨t, ht, N, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let K := closedBall (x : ℂ) r
  let M : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ y ∈ ({x} : Set ℝ), ∃ z ∈ closedBall (y : ℂ) t₀,
        ε / 3 < ‖localUnshiftedRankProfileLimit l 0 q z -
          localUnshiftedRankProfileLimit l 0 q (y : ℂ)‖}
  have hM : birthParentLaw.real M < δ / 2 :=
    hmod l (hIlower l hl) 0
  have hF : birthParentLaw.real
      (finiteLocalProfileMovingTimeBad l n H (A n) K (ε / 3)) < δ / 2 :=
    happrox n hn l hl
  have hsub : finiteProfileMovingTimeTiltBad l n H (A n) x t ε ⊆
      finiteLocalProfileMovingTimeBad l n H (A n) K (ε / 3) ∪ M := by
    rintro q ⟨hs, z, hz, he⟩
    by_contra hnot
    have hnotF : q ∉ finiteLocalProfileMovingTimeBad l n H (A n) K (ε / 3) :=
      fun hq ↦ hnot (Or.inl hq)
    have hnotM : q ∉ M := fun hq ↦ hnot (Or.inr hq)
    have hsurv : ∀ i, 0 < localWalk l q.1 i := by
      by_contra hh
      exact hnotF ⟨hs, Or.inl hh⟩
    have hzK : z ∈ K :=
      closedBall_subset_closedBall (min_le_left _ _) hz
    have hxK : (x : ℂ) ∈ K :=
      mem_closedBall_self hr.le
    have hzF : ‖finiteUnshiftedRankProfile l n q (A n) z -
        localUnshiftedRankProfileLimit l 0 q z‖ ≤ ε / 3 :=
      le_of_not_gt (fun hh ↦ hnotF ⟨hs, Or.inr ⟨z, hzK, hh⟩⟩)
    have hxF : ‖finiteUnshiftedRankProfile l n q (A n) (x : ℂ) -
        localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ ≤ ε / 3 :=
      le_of_not_gt (fun hh ↦ hnotF ⟨hs, Or.inr ⟨x, hxK, hh⟩⟩)
    have hzM : ‖localUnshiftedRankProfileLimit l 0 q z -
        localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ ≤ ε / 3 := by
      apply le_of_not_gt
      intro hh
      exact hnotM ⟨by exact_mod_cast hsurv, x, mem_singleton x,
        z, closedBall_subset_closedBall (min_le_right _ _) hz, hh⟩
    have htri₁ := norm_sub_le_norm_sub_add_norm_sub
      (finiteUnshiftedRankProfile l n q (A n) z)
      (localUnshiftedRankProfileLimit l 0 q z)
      (finiteUnshiftedRankProfile l n q (A n) (x : ℂ))
    have htri₂ := norm_sub_le_norm_sub_add_norm_sub
      (localUnshiftedRankProfileLimit l 0 q z)
      (localUnshiftedRankProfileLimit l 0 q (x : ℂ))
      (finiteUnshiftedRankProfile l n q (A n) (x : ℂ))
    rw [norm_sub_rev (localUnshiftedRankProfileLimit l 0 q (x : ℂ))
      (finiteUnshiftedRankProfile l n q (A n) (x : ℂ))] at htri₂
    linarith
  have hb := (measureReal_mono (μ := birthParentLaw) hsub).trans
    (measureReal_union_le _ _)
  linarith

/-- A shrinking family of complex tilt sets inherits the uniform moving-time
profile continuity estimate. This is the probability-level part of the
source's conditional-moment perturbation lemma. -/
theorem uniform_finiteProfile_shrinking_tilts_probability
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (hp : p ∈ Ioc (1 : ℝ) 2) (hη : 0 < η)
    (hr : 0 < r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n))
    (hxK : ∀ n, (x : ℂ) ∈ K n)
    (hdiam : Tendsto (fun n ↦ Metric.diam (K n)) atTop (𝓝 0))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real {q | (∀ i ≤ ⌊T * n⌋₊,
        0 < finiteWalk l n q.1 i) ∧ ∃ z ∈ K n,
          ε < ‖finiteUnshiftedRankProfile l n q (A n) z -
            finiteUnshiftedRankProfile l n q (A n) (x : ℂ)‖} < δ := by
  obtain ⟨t, ht, N₁, hmod⟩ :=
    uniform_finiteProfile_moving_time_tilt_modulus hI hl₀ hT
      hparams hIlower hx hp hη hr hrR hRρ hright hwindow
      A hA hAH hε hδ
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (hdiam.eventually (Iio_mem_nhds ht))
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn l hl
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
  apply lt_of_le_of_lt (measureReal_mono ?_) (hmod n hn₁ l hl)
  rintro q ⟨hs, z, hz, hbad⟩
  refine ⟨hs, z, ?_, hbad⟩
  apply mem_closedBall.mpr
  exact (Metric.dist_le_diam_of_mem (hK n).isBounded hz (hxK n)).trans
    (hN₂ n hn₂).le

end HeightPaper.CountCoupling
