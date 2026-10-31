module

public import HeightPaper.Probability.FiniteUnshiftedProfileTail
public import HeightPaper.Probability.LocalProfileCarrier
public import HeightPaper.Probability.ProfileCouplingComparison

/-!
# Finite-to-local comparison on the common birth-parent space

A fixed comparison time is chosen after the probability tolerance. Uniform
finite and local tails, followed by exact short-prefix agreement, give the
comparison without requiring equality of the auxiliary random cutoffs.
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

theorem birthParentLaw_real_fst_le (E : Set (ℕ → ℝ)) :
    birthParentLaw.real {q | q.1 ∈ E} ≤ uniformLaw.real E := by
  have hh := Measure.le_map_apply (μ := birthParentLaw) measurable_fst.aemeasurable E
  rw [birthParentLaw_map_fst] at hh
  exact ENNReal.toReal_mono (measure_ne_top _ _) hh

theorem finite_local_unshifted_rankProfile_eq {l : ℝ} {n A : ℕ}
    (q : (ℕ → ℝ) × (ℕ → ℝ))
    (hwalk : ∀ k ≤ A, finiteWalk l n q.1 k = localWalk l q.1 k) (z : ℂ) :
    finiteUnshiftedRankProfile l n q A z = localUnshiftedRankProfile l 0 q A z := by
  exact Model.rankProfile_congr_events_prefix _ n 0 q.2
    (finiteBirth_eq_localBirth_of_walk_prefix hwalk)

def finiteLocalProfileBad (l : ℝ) (n H : ℕ) (K : Set ℂ) (ε : ℝ) :
    Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
    (¬(∀ i, 0 < localWalk l q.1 i) ∨ ∃ z ∈ K,
      ε < ‖finiteUnshiftedRankProfile l n q H z - localUnshiftedRankProfileLimit l 0 q z‖)}

/-- The local disk-tail theorem is the sole remaining input of this coupling
step. The finite stochastic controls and exact coupling are discharged here. -/
theorem uniform_finiteLocalProfile_comparison_of_local_tail
    {I : Set ℝ≥0} (hI : IsCompact I) {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (z₀ : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {p η : ℝ} (hp : p ∈ Ioc (1 : ℝ) 2) (hη : 0 < η)
    (hwindow : ∀ l ∈ I, ∀ z ∈ closedBall z₀ R,
      0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    (hexp : ∀ z ∈ closedBall z₀ r, 1 ≤ (Complex.exp z).re)
    (hlocal : ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ), ∃ A : ℕ, ∀ l ∈ I, ∀ j ≥ A,
      birthParentLaw.real {q | (∀ i, 0 < localWalk l q.1 i) ∧ ∃ z ∈ closedBall z₀ r,
        ε < ‖localUnshiftedRankProfile l 0 q j z - localUnshiftedRankProfileLimit l 0 q z‖} < δ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real (finiteLocalProfileBad l n ⌊T * n⌋₊ (closedBall z₀ r) ε) < δ := by
  have hquarter : 0 < δ / 4 := by positivity
  obtain ⟨Af, Nf, _, hfinite⟩ := finiteUnshiftedProfile_disk_tail_uniform hI hT hparams
    z₀ hr hrR hp hη hwindow hexp (half_pos hε) hquarter
  obtain ⟨Al, hloc⟩ := hlocal (ε / 2) (half_pos hε) (δ / 4) hquarter
  let A := max Af Al
  obtain ⟨Ns, hsurv⟩ := uniform_survival_disagreement hI hT hparams hquarter
  obtain ⟨L, hL⟩ := hI.bddAbove
  have hHt : Tendsto (fun n : ℕ => ⌊T * n⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hT)
  obtain ⟨Nh, hNh⟩ := eventually_atTop.mp (hHt.eventually_ge_atTop A)
  have hPt : Tendsto (fun n : ℕ => (L : ℝ) * (A : ℝ) ^ 2 / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  obtain ⟨Np, hNp⟩ := eventually_atTop.mp (hPt.eventually (Iio_mem_nhds hquarter))
  refine ⟨Nf + Ns + Nh + Np + A + 1, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  have hAH : A ≤ H := hNh n (by omega)
  let S : Set (ℕ → ℝ) :=
    {u | ¬((∀ i ≤ H, 0 < finiteWalk l n u i) ↔ ∀ i, 0 < localWalk l u i)}
  let P : Set (ℕ → ℝ) := {u | ∃ k ≤ A, finiteWalk l n u k ≠ localWalk l u k}
  let F := finiteUnshiftedProfileDiskBad l n H A (closedBall z₀ r) (ε / 2)
  let G : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i, 0 < localWalk l q.1 i) ∧ ∃ z ∈ closedBall z₀ r,
      ε / 2 < ‖localUnshiftedRankProfile l 0 q A z - localUnshiftedRankProfileLimit l 0 q z‖}
  have hS : birthParentLaw.real {q | q.1 ∈ S} < δ / 4 :=
    (birthParentLaw_real_fst_le S).trans_lt (hsurv n (by omega) l hl)
  have hP : birthParentLaw.real {q | q.1 ∈ P} < δ / 4 := by
    have hlL : (l : ℝ) ≤ L := by exact_mod_cast hL hl
    exact (birthParentLaw_real_fst_le P).trans_lt
      ((prefix_disagreement_probability_le_uniform (L := L) (n := n) (K := A)
        (by omega) (by omega) l ⟨l.coe_nonneg, hlL⟩).trans_lt (hNp n (by omega)))
  have hF : birthParentLaw.real F < δ / 4 :=
    (hfinite n (by omega)).2 l hl A (le_max_left _ _) hAH
  have hG : birthParentLaw.real G < δ / 4 := hloc l hl A (le_max_right _ _)
  have hsub : finiteLocalProfileBad l n H (closedBall z₀ r) ε ⊆
      ({q | q.1 ∈ S} ∪ {q | q.1 ∈ P}) ∪ (F ∪ G) := by
    rintro q ⟨hs, hbad⟩
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or] at hnot
    have hls : ∀ i, 0 < localWalk l q.1 i := (not_not.mp hnot.1.1).mp hs
    have hwalk : ∀ k ≤ A, finiteWalk l n q.1 k = localWalk l q.1 k := by
      intro k hk
      by_contra he
      exact hnot.1.2 ⟨k, hk, he⟩
    obtain ⟨z, hz, he⟩ := hbad.resolve_left (not_not.mpr hls)
    have hf := le_of_not_gt (fun hb => hnot.2.1 ⟨hs, z, hz, hb⟩)
    have hg := le_of_not_gt (fun hb => hnot.2.2 ⟨hls, z, hz, hb⟩)
    rw [← finite_local_unshifted_rankProfile_eq q hwalk z] at hg
    have ht := norm_sub_le_norm_sub_add_norm_sub (finiteUnshiftedRankProfile l n q H z)
      (finiteUnshiftedRankProfile l n q A z) (localUnshiftedRankProfileLimit l 0 q z)
    linarith
  have hb := (measureReal_mono (μ := birthParentLaw) hsub).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (measureReal_union_le _ _) (measureReal_union_le _ _)))
  linarith

end HeightPaper.CountCoupling
