module

public import HeightPaper.Probability.FiniteShiftedLocalIdentity
public import HeightPaper.Probability.SafeCutoffConvergence

/-!
# Agreement of finite and local event words through the local cutoff

The local cutoff is tight uniformly over compact supercritical rates.
Consequently the finite and local walks agree through that random cutoff
with probability tending to one.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

/-- Uniform agreement of the finite and local signed count walks through the
random local safe cutoff. -/
theorem localSafeCutoff_prefix_disagreement_uniform
    {I : Set ℝ≥0} (hI : IsCompact I)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real {u | ∃ k ≤ localSafeCutoff l u,
        finiteWalk l n u k ≠ localWalk l u k} < ε := by
  by_cases hne : I.Nonempty
  swap
  · exact ⟨0, fun n hn l hl ↦ False.elim (hne ⟨l, hl⟩)⟩
  obtain ⟨l₀, hl₀, hmin⟩ := hI.exists_isLeast hne
  obtain ⟨L, hL⟩ := hI.bddAbove
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨K, hK⟩ := localSafeCutoff_uniform_tight (hparams l₀ hl₀) hhalf
  have hlim : Tendsto (fun n : ℕ ↦ (L : ℝ) * (K : ℝ) ^ 2 / n)
      atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  obtain ⟨Nprob, hNprob⟩ := eventually_atTop.mp
    (hlim.eventually (Iio_mem_nhds hhalf))
  refine ⟨max Nprob (K + 1), ?_⟩
  intro n hn l hl
  have hnK : K ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hlmin : (l₀ : ℝ) ≤ (l : ℝ) := by exact_mod_cast hmin hl
  have hll : (l : ℝ) ≤ L := by exact_mod_cast hL hl
  have hloc : uniformLaw.real {u | K < localSafeCutoff l u} ≤ ε / 2 :=
    hK l hlmin
  have hpre : uniformLaw.real {u | ∃ k ≤ K,
      finiteWalk l n u k ≠ localWalk l u k} < ε / 2 :=
    (prefix_disagreement_probability_le_uniform hn0 hnK l
      ⟨l.coe_nonneg, hll⟩).trans_lt (hNprob n ((le_max_left _ _).trans hn))
  have hsub : {u | ∃ k ≤ localSafeCutoff l u,
      finiteWalk l n u k ≠ localWalk l u k} ⊆
      {u | K < localSafeCutoff l u} ∪
        {u | ∃ k ≤ K, finiteWalk l n u k ≠ localWalk l u k} := by
    rintro u ⟨k, hk, hbad⟩
    by_cases hJK : K < localSafeCutoff l u
    · exact Or.inl hJK
    · exact Or.inr ⟨k, hk.trans (le_of_not_gt hJK), hbad⟩
  have hmono := measureReal_mono (μ := uniformLaw) hsub
  have hunion := measureReal_union_le (μ := uniformLaw)
    {u | K < localSafeCutoff l u}
    {u | ∃ k ≤ K, finiteWalk l n u k ≠ localWalk l u k}
  linarith

/-- On joint survival, the finite and local safe cutoffs and the entire
birth-word prefix through that cutoff agree with high probability. -/
theorem finiteLocal_cutoff_and_prefix_disagreement_uniform
    {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real {u | u ∈ finiteSurvival l n ⌊T * n⌋₊ ∧
        u ∈ localSurvival l ∧
        (finiteSafeCutoff l n ⌊T * n⌋₊ u ≠ localSafeCutoff l u ∨
          ∃ k ≤ localSafeCutoff l u,
            finiteWalk l n u k ≠ localWalk l u k)} < ε := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Ncut, hcut⟩ :=
    safeCutoff_survival_disagreement_uniform hI hT hparams hhalf
  obtain ⟨Npre, hpre⟩ :=
    localSafeCutoff_prefix_disagreement_uniform hI
      (fun l hl ↦ (hparams l hl).1) hhalf
  refine ⟨max Ncut Npre, ?_⟩
  intro n hn l hl
  have hc := hcut n ((le_max_left _ _).trans hn) l hl
  have hp := hpre n ((le_max_right _ _).trans hn) l hl
  have hsub : {u | u ∈ finiteSurvival l n ⌊T * n⌋₊ ∧
      u ∈ localSurvival l ∧
      (finiteSafeCutoff l n ⌊T * n⌋₊ u ≠ localSafeCutoff l u ∨
        ∃ k ≤ localSafeCutoff l u,
          finiteWalk l n u k ≠ localWalk l u k)} ⊆
      {u | survivingFiniteSafeCutoff l n ⌊T * n⌋₊ u ≠
        survivingLocalSafeCutoff l u} ∪
      {u | ∃ k ≤ localSafeCutoff l u,
        finiteWalk l n u k ≠ localWalk l u k} := by
    rintro u ⟨hs, hloc, hbad⟩
    rcases hbad with hJ | hwalk
    · left
      have hs' : ∀ j ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u j := hs
      have hloc' : ∀ j, 0 < localWalk l u j := hloc
      simpa only [mem_ofPred_eq, survivingFiniteSafeCutoff, survivingLocalSafeCutoff,
        ite_eq_left hs', ite_eq_left hloc'] using hJ
    · exact Or.inr hwalk
  have hm := measureReal_mono (μ := uniformLaw) hsub
  have hu := measureReal_union_le (μ := uniformLaw)
    {u | survivingFiniteSafeCutoff l n ⌊T * n⌋₊ u ≠
      survivingLocalSafeCutoff l u}
    {u | ∃ k ≤ localSafeCutoff l u,
      finiteWalk l n u k ≠ localWalk l u k}
  linarith

end HeightPaper.CountCoupling
