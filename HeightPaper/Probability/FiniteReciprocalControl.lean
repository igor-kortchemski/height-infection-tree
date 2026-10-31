module

public import HeightPaper.Probability.CoupledCountControl
public import HeightPaper.Probability.CountCouplingTightness
public import HeightPaper.Probability.ReciprocalWalkLimit
public import HeightPaper.Model.ReciprocalCoupling

/-!
# Uniform centered reciprocal control for the finite epidemic

The local harmonic martingale, count ratios, and coupled walk gap all have
proved uniform stochastic bounds. Their intersection supplies the source's
unscaled centered reciprocal estimate simultaneously at every event time.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators NNReal

namespace HeightPaper.CountCoupling

/-- The finite-epidemic centered reciprocal sum, on survival through the full
horizon, is tight uniformly in time and weakly uniformly on compact parameter
sets. The rate is exactly `λ/n`, as throughout this part of the paper. -/
theorem finiteCenteredReciprocal_uniform_tight {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real {u | (∀ j ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u j) ∧
        ∃ k ≤ ⌊T * n⌋₊, R <
          |birthReciprocalSum (fun j ↦ (finiteWalk l n u j : ℝ)) (finiteBirth l n u) k -
            (l : ℝ) / ((l : ℝ) - 1) * Real.log k|} < ε := by
  classical
  by_cases hne : I.Nonempty
  swap
  · refine ⟨0, le_rfl, 0, ?_⟩
    intro n hn l hl
    exact False.elim (hne ⟨l, hl⟩)
  obtain ⟨l₀, hl₀, hmin⟩ := hI.exists_isLeast hne
  obtain ⟨L, hL⟩ := hI.bddAbove
  have hl₀1 : 1 < (l₀ : ℝ) := (hparams l₀ hl₀).1
  have hδ : 0 < ε / 5 := by positivity
  obtain ⟨A, hA, hlocalSum⟩ := localCenteredReciprocal_uniform_tight hl₀1 hδ
  obtain ⟨M, hM, hlocalRatio⟩ := positiveReciprocal_uniform_tight hl₀1 hδ
  obtain ⟨Mn, N, hfiniteRatio⟩ := coupled_count_ratio_uniform_tight hI hT hparams hδ
  obtain ⟨C, hC, hwalkGap⟩ := walkGap_uniform_tight L.coe_nonneg hδ
  let R := A + M * (Mn + 1) * C * (2 + T)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨R, hR, max N 1, ?_⟩
  intro n hn l hl
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := (le_max_right N 1).trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlmin : (l₀ : ℝ) ≤ l := by exact_mod_cast hmin hl
  have hlL : (l : ℝ) ≤ L := by exact_mod_cast hL hl
  let H := ⌊T * n⌋₊
  let E₁ : Set (ℕ → ℝ) := {u | ∃ k : ℕ,
    (∀ i ≤ k, 0 < (localWalk l u i : ℝ)) ∧ A <
      |(∑ i ∈ Finset.range k, (if localBirth l u i then (1 : ℝ) else 0) /
        (localWalk l u (i + 1) : ℝ)) - (l : ℝ) / ((l : ℝ) - 1) * Real.log k|}
  let E₂ : Set (ℕ → ℝ) := {u | ∃ k, M < positiveReciprocal l u k}
  let E₃ := coupledCountRatioTail Mn l n H
  let E₄ : Set (ℕ → ℝ) := {u | ∃ k : ℕ, C <
    ((localWalk l u k : ℝ) - finiteWalk l n u k) / (1 + (k : ℝ) ^ 2 / n)}
  have h₁ : uniformLaw.real E₁ ≤ ε / 5 := hlocalSum l hlmin
  have h₂ : uniformLaw.real E₂ ≤ ε / 5 := hlocalRatio l hlmin
  have h₃ : uniformLaw.real E₃ < ε / 5 := hfiniteRatio n hnN l hl
  have h₄ : uniformLaw.real E₄ ≤ ε / 5 := hwalkGap n hnpos l ⟨l.coe_nonneg, hlL⟩
  have hsub : {u | (∀ j ≤ H, 0 < finiteWalk l n u j) ∧ ∃ k ≤ H, R <
      |birthReciprocalSum (fun j ↦ (finiteWalk l n u j : ℝ)) (finiteBirth l n u) k -
        (l : ℝ) / ((l : ℝ) - 1) * Real.log k|} ⊆ (E₁ ∪ E₂) ∪ (E₃ ∪ E₄) := by
    intro u hu
    by_contra hnot
    have hnot₁ : u ∉ E₁ := fun h ↦ hnot (Or.inl (Or.inl h))
    have hnot₂ : u ∉ E₂ := fun h ↦ hnot (Or.inl (Or.inr h))
    have hnot₃ : u ∉ E₃ := fun h ↦ hnot (Or.inr (Or.inl h))
    have hnot₄ : u ∉ E₄ := fun h ↦ hnot (Or.inr (Or.inr h))
    obtain ⟨hsurv, k, hk, hlarge⟩ := hu
    have hpos (j : ℕ) (hj : j ≤ H) : 0 < (finiteWalk l n u j : ℝ) := by
      exact_mod_cast hsurv j hj
    have hposLocal (j : ℕ) (hj : j ≤ H) : 0 < (localWalk l u j : ℝ) :=
      (hpos j hj).trans_le (Int.cast_le.mpr (walk_sandwich l.coe_nonneg hnpos u j).2)
    have hlocal (j : ℕ) (hj : j ≤ H) : (j : ℝ) / localWalk l u j ≤ M := by
      have hp : 0 < localWalk l u j := by exact_mod_cast hposLocal j hj
      have h := le_of_not_gt (fun h ↦ hnot₂ ⟨j, h⟩)
      simpa only [positiveReciprocal, ite_eq_left hp] using h
    have hfinite (j : ℕ) (hj : j ≤ H) : (j : ℝ) / finiteWalk l n u j ≤ Mn :=
      le_of_not_gt (fun h ↦ hnot₃ ⟨hsurv, j, hj, h⟩)
    have hgap (j : ℕ) (_hj : j ≤ H) : (localWalk l u j : ℝ) - finiteWalk l n u j ≤
        C * (1 + (j : ℝ) ^ 2 / n) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1 + (j : ℝ) ^ 2 / n)).mp
      exact le_of_not_gt (fun h ↦ hnot₄ ⟨j, h⟩)
    have hHT : (H : ℝ) / n ≤ T := by
      apply (div_le_iff₀ hnR).mpr
      exact Nat.floor_le (by positivity : 0 ≤ T * n)
    have hcompare := birthReciprocalSum_difference_le l.coe_nonneg hnpos u H
      hM (Nat.cast_nonneg Mn) hC.le hT.le hpos hlocal hfinite hgap hHT hk
    have hlocalBound : |birthReciprocalSum (fun j ↦ (localWalk l u j : ℝ)) (localBirth l u) k -
        (l : ℝ) / ((l : ℝ) - 1) * Real.log k| ≤ A := by
      apply le_of_not_gt
      intro h
      exact hnot₁ ⟨k, fun i hi ↦ hposLocal i (hi.trans hk), h⟩
    have htriangle := abs_sub_le
      (birthReciprocalSum (fun j ↦ (finiteWalk l n u j : ℝ)) (finiteBirth l n u) k)
      (birthReciprocalSum (fun j ↦ (localWalk l u j : ℝ)) (localBirth l u) k)
      ((l : ℝ) / ((l : ℝ) - 1) * Real.log k)
    dsimp only [R] at hlarge
    linarith
  have hprob := measureReal_mono (μ := uniformLaw) hsub
  have hUnion := measureReal_union_le (μ := uniformLaw) (E₁ ∪ E₂) (E₃ ∪ E₄)
  have h12 := measureReal_union_le (μ := uniformLaw) E₁ E₂
  have h34 := measureReal_union_le (μ := uniformLaw) E₃ E₄
  change uniformLaw.real {u | (∀ j ≤ H, 0 < finiteWalk l n u j) ∧ ∃ k ≤ H, R <
      |birthReciprocalSum (fun j ↦ (finiteWalk l n u j : ℝ)) (finiteBirth l n u) k -
        (l : ℝ) / ((l : ℝ) - 1) * Real.log k|} < ε
  linarith

end HeightPaper.CountCoupling
