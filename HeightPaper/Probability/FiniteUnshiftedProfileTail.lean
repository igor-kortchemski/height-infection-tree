module

public import HeightPaper.Probability.FiniteProfileDiskTail
public import HeightPaper.Model.UnshiftedProfile

/-! # Joint tails for the finite unshifted profile -/

@[expose] public section

open MeasureTheory Complex Metric Set
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

noncomputable def finiteUnshiftedRankProfile (l : ℝ) (n : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) (k : ℕ) (z : ℂ) : ℂ :=
  prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n q.1) (initial n) 0 k
    (rankState (finiteBirth l n q.1) (initial n) q.2 k)

def finiteUnshiftedProfileDiskBad (l : ℝ) (n H j : ℕ) (K : Set ℂ) (ε : ℝ) :
    Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧ ∃ z ∈ K,
    ε < ‖finiteUnshiftedRankProfile l n q H z - finiteUnshiftedRankProfile l n q j z‖}

theorem measurableSet_finiteUnshiftedProfileDiskBad (l : ℝ) (n H j : ℕ)
    (hj : j ≤ H) (K : Set ℂ) (ε : ℝ) :
    MeasurableSet (finiteUnshiftedProfileDiskBad l n H j K ε) := by
  apply measurableSet_of_finiteBirth_rankStates l n H j H
  intro q q' he hsj hsk
  have hsurv := forall₂_congr (fun i (hi : i ≤ H) =>
    show (0 < finiteWalk l n q.1 i) ↔ (0 < finiteWalk l n q'.1 i) by
      rw [finiteWalk_congr_birth_prefix he hi])
  have hC (i : ℕ) (hi : i ≤ H) (z : ℂ) :=
    prescribedNormalizerFrom_congr_prefix (Complex.exp z) 1 0 he hi
  simp only [finiteUnshiftedProfileDiskBad, finiteUnshiftedRankProfile, mem_ofPred_eq,
    hsurv, prescribedNormalizedProfile, infectious_initial, hsj, hsk, hC j hj, hC H le_rfl]

/-- Passing to the unshifted normalization costs only the already-controlled
event that the random cutoff lies after the comparison time. -/
theorem finiteUnshiftedProfileDiskBad_probability_le (l : ℝ) (n H j : ℕ)
    (hj : j ≤ H) (K : Set ℂ) (hK : ∀ z ∈ K, 1 ≤ (Complex.exp z).re) (ε : ℝ) :
    birthParentLaw.real (finiteUnshiftedProfileDiskBad l n H j K ε) ≤
      uniformLaw.real {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧ j < finiteSafeCutoff l n H u} +
        birthParentLaw.real (finiteProfileDiskBad l n H j K ε) := by
  let B : Set (ℕ → ℝ) :=
    {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧ j < finiteSafeCutoff l n H u}
  have hB : MeasurableSet B := by
    apply measurableSet_of_finiteBirth_prefix l n H
    intro u v he
    have hs := forall₂_congr (fun i (hi : i ≤ H) =>
      show (0 < finiteWalk l n u i) ↔ (0 < finiteWalk l n v i) by
        rw [finiteWalk_congr_birth_prefix he hi])
    simp only [B, mem_ofPred_eq, hs, finiteSafeCutoff_congr_birth_prefix he]
  have hmap : birthParentLaw.real (Prod.fst ⁻¹' B) = uniformLaw.real B := by
    rw [← birthParentLaw_map_fst]
    simp only [Measure.real, Measure.map_apply measurable_fst hB]
  have hsub : finiteUnshiftedProfileDiskBad l n H j K ε ⊆
      Prod.fst ⁻¹' B ∪ finiteProfileDiskBad l n H j K ε := by
    rintro q ⟨hs, z, hz, he⟩
    by_cases hJ : finiteSafeCutoff l n H q.1 ≤ j
    · right
      refine ⟨hs, z, hz, he.trans_le ?_⟩
      exact norm_unshifted_profile_difference_le (hK z hz) _ _ _ _ hJ (hJ.trans hj)
    · exact Or.inl ⟨hs, lt_of_not_ge hJ⟩
  have hb := (measureReal_mono (μ := birthParentLaw) hsub).trans
    (measureReal_union_le (μ := birthParentLaw) _ _)
  rwa [hmap] at hb

theorem finiteUnshiftedProfile_disk_tail_uniform {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (z₀ : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {p η : ℝ} (hp : p ∈ Ioc (1 : ℝ) 2) (hη : 0 < η)
    (hwindow : ∀ l ∈ I, ∀ z ∈ closedBall z₀ R,
      0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    (hexp : ∀ z ∈ closedBall z₀ r, 1 ≤ (Complex.exp z).re)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A N : ℕ, 1 ≤ A ∧ ∀ n ≥ N, A ≤ ⌊T * n⌋₊ ∧ ∀ l ∈ I,
      ∀ j ≥ A, j ≤ ⌊T * n⌋₊ → birthParentLaw.real
        (finiteUnshiftedProfileDiskBad l n ⌊T * n⌋₊ j (closedBall z₀ r) ε) < δ := by
  obtain ⟨A, N, hA, htail⟩ := finiteProfile_disk_tail_uniform_with_cutoff
    hI hT hparams z₀ hr hrR hp hη hwindow hε (half_pos hδ)
  refine ⟨A, N, hA, ?_⟩
  intro n hn
  refine ⟨(htail n hn).1, ?_⟩
  intro l hl j hj hjH
  obtain ⟨hprof, hcut⟩ := (htail n hn).2 l hl j hj hjH
  have hb := finiteUnshiftedProfileDiskBad_probability_le l n ⌊T * n⌋₊ j hjH
    (closedBall z₀ r) hexp ε
  linarith

end HeightPaper.CountCoupling
