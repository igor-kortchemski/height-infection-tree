module

public import HeightPaper.Probability.FiniteProfileGrowth

/-!
# Uniform finite profile moments in a summable complex window

The general moment envelope has logarithmic growth at the critical exponent.
Below that exponent the increment sum is absolutely summable and the profile
moment has a time-independent tight bound.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal Classical

namespace HeightPaper.CountCoupling

def finiteProfileStrictDecayBad (C η l : ℝ) (n H : ℕ) : Set (ℕ → ℝ) :=
  {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
    ∃ k, 1 ≤ k ∧ k ≤ H ∧ finiteSafeCutoff l n H u ≤ k ∧
      ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
        ∃ p ∈ Ioc (1 : ℝ) 2,
          complexProfileMomentExponent l z p ≤ -1 - η ∧
          C < finiteProfileMoment (Complex.exp z) p l n H u k}

theorem measurableSet_finiteProfileStrictDecayBad (C η l : ℝ) (n H : ℕ) :
    MeasurableSet (finiteProfileStrictDecayBad C η l n H) := by
  apply measurableSet_of_finiteBirth_prefix l n H
  intro u v he
  have hsurv := forall₂_congr (fun i (hi : i ≤ H) =>
    show (0 < finiteWalk l n u i) ↔ (0 < finiteWalk l n v i) by
      rw [finiteWalk_congr_birth_prefix he hi])
  simp only [finiteProfileStrictDecayBad, mem_ofPred_eq, hsurv,
    finiteSafeCutoff_congr_birth_prefix he]
  apply and_congr_right
  intro _
  apply exists_congr
  intro k
  apply and_congr_right
  intro _
  apply and_congr_right
  intro hk
  apply and_congr_right
  intro _
  apply exists_congr
  intro z
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply exists_congr
  intro p
  simp only [finiteProfileMoment_congr_prefix (Complex.exp z) p he hk]

/-- One random constant bounds all finite profile conditional moments at
every event time and every complex tilt/moment order in a common strictly
summable exponent window. -/
theorem finiteProfileMoment_strictDecay_uniform
    {I : Set ℝ≥0} (hI : IsCompact I)
    {T η : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hη : 0 < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real (finiteProfileStrictDecayBad C η l n ⌊T * n⌋₊) < ε := by
  have hδ : 0 < ε / 3 := by positivity
  obtain ⟨R, hR, NR, hinc⟩ :=
    finiteProfileIncrementBound_uniform_exp hI hT hparams hδ
  obtain ⟨K, NK, hcut⟩ :=
    finiteSafeCutoff_survival_uniform_tight hI hT hparams hδ
  let B : ℝ := 32 * Real.exp R *
      (∑' i : ℕ, ((i + 1 : ℕ) : ℝ) ^ (-1 - η)) + 2 * Real.exp (4 * K)
  let C : ℝ := max 0 B
  refine ⟨C, le_max_left _ _, max NR NK, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let E₁ : Set (ℕ → ℝ) := {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
    ∃ k < H, finiteSafeCutoff l n H u ≤ k ∧
      ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧ ∃ p ∈ Icc (1 : ℝ) 2,
        Real.exp (complexProfileMomentExponent l z p * Real.log (k + 1 : ℕ) + R) <
          finiteProfileIncrementBound l n H u k z p}
  let E₂ : Set (ℕ → ℝ) := {u | K <
    (if ∀ i ≤ H, 0 < finiteWalk l n u i then finiteSafeCutoff l n H u else 0)}
  have hsub : finiteProfileStrictDecayBad C η l n H ⊆ E₁ ∪ E₂ := by
    rintro u ⟨hs, k, hk1, hk, hJk, z, hz0, hz, p, hp, hdecay, hbad⟩
    by_contra hnot
    have h₁ : u ∉ E₁ := fun h ↦ hnot (Or.inl h)
    have h₂ : u ∉ E₂ := fun h ↦ hnot (Or.inr h)
    have hJ : finiteSafeCutoff l n H u ≤ K := by
      apply le_of_not_gt
      intro h
      apply h₂
      simpa only [E₂, mem_ofPred_eq, ite_eq_left hs] using h
    have hbound : ∀ i ∈ Finset.Ico (finiteSafeCutoff l n H u) k,
        finiteProfileIncrementBound l n H u i z p ≤
          Real.exp (complexProfileMomentExponent l z p * Real.log (i + 1 : ℕ) + R) := by
      intro i hi
      obtain ⟨hJi, hik⟩ := Finset.mem_Ico.mp hi
      apply le_of_not_gt
      intro h
      exact h₁ ⟨hs, i, hik.trans_le hk, hJi, z, hz0, hz, p,
        ⟨hp.1.le, hp.2⟩, h⟩
    have hm := finiteProfileMoment_le_of_strict_decay (hparams l hl).1 hη
      hs hJ hk hJk hz0 hz hp.1 hp.2 hdecay hbound
    have hBC : B ≤ C := le_max_right _ _
    exact (not_lt_of_ge (hm.trans hBC)) hbad
  have h₁ : uniformLaw.real E₁ < ε / 3 := hinc n (by omega) l hl
  have h₂ : uniformLaw.real E₂ < ε / 3 := hcut n (by omega) l hl
  have hm := measureReal_mono (μ := uniformLaw) hsub
  have hu := measureReal_union_le (μ := uniformLaw) E₁ E₂
  change uniformLaw.real (finiteProfileStrictDecayBad C η l n H) < ε
  linarith

end HeightPaper.CountCoupling
