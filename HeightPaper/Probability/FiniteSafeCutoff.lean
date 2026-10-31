module

public import HeightPaper.Probability.SafeCutoff
public import HeightPaper.Probability.CoupledCountControl

/-! # Uniform tightness of the exact finite-population safe cutoff -/

@[expose] public section

open MeasureTheory Set
open scoped Classical NNReal

namespace HeightPaper.CountCoupling

/-- Source `Jⁿ` through the given horizon. The unsafe set contains time zero,
so the manuscript's empty-set convention is never needed for these walks. -/
noncomputable def finiteSafeCutoff (l : ℝ) (n H : ℕ) (u : ℕ → ℝ) : ℕ :=
  sSup {k : ℕ | k ≤ H ∧ (1 / 2 : ℝ) ≤
    1 / (finiteWalk l n u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)}

theorem finiteSafeCutoff_le_horizon (l : ℝ) (n H : ℕ) (u : ℕ → ℝ) :
    finiteSafeCutoff l n H u ≤ H := csSup_le' (fun _ h ↦ h.1)

theorem finiteSafeCutoff_zero_unsafe (l : ℝ) (n H : ℕ) (u : ℕ → ℝ) :
    (0 : ℕ) ≤ H ∧ (1 / 2 : ℝ) ≤
      1 / (finiteWalk l n u 0 : ℝ) * (Real.exp (2 * profileRoot l) + 1) := by
  constructor
  · exact Nat.zero_le H
  · simp only [finiteWalk_zero, Int.cast_one, div_one, one_mul]
    linarith [Real.exp_pos (2 * profileRoot l)]

theorem finiteSafeCutoff_eq_iSup (l : ℝ) (n H : ℕ) (u : ℕ → ℝ) :
    finiteSafeCutoff l n H u = ⨆ k : ℕ, if k ≤ H ∧ (1 / 2 : ℝ) ≤
      1 / (finiteWalk l n u k : ℝ) * (Real.exp (2 * profileRoot l) + 1) then k else 0 := by
  let P : ℕ → Prop := fun k ↦ k ≤ H ∧ (1 / 2 : ℝ) ≤
    1 / (finiteWalk l n u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)
  have hzero : P 0 := finiteSafeCutoff_zero_unsafe l n H u
  change sSup {k | P k} = sSup (range (fun k ↦ if P k then k else 0))
  congr 1
  ext k
  constructor
  · intro hk
    exact ⟨k, by simp only [show P k from hk, ↓reduceIte]⟩
  · rintro ⟨j, hj⟩
    change P k
    by_cases h : P j
    · have hj' : j = k := by simpa only [h, ↓reduceIte] using hj
      exact hj' ▸ h
    · have hk : k = 0 := by simpa only [h, ↓reduceIte] using hj.symm
      rw [hk]
      exact hzero

theorem measurable_finiteSafeCutoff (l : ℝ) (n H : ℕ) :
    Measurable (finiteSafeCutoff l n H) := by
  have hm (k : ℕ) : Measurable (fun u : ℕ → ℝ ↦ if k ≤ H ∧ (1 / 2 : ℝ) ≤
      1 / (finiteWalk l n u k : ℝ) * (Real.exp (2 * profileRoot l) + 1) then k else 0) := by
    apply measurable_const.ite _ measurable_const
    have hA : MeasurableSet {u : ℕ → ℝ | k ≤ H} := by
      by_cases h : k ≤ H <;> simp [h]
    exact hA.inter (measurableSet_le measurable_const ((measurable_const.div
      ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
        (measurable_finiteWalk l n k))).mul_const _))
  simpa only [← finiteSafeCutoff_eq_iSup] using Measurable.iSup hm

theorem finiteSafeCutoff_safe_after (l : ℝ) (n H : ℕ) (u : ℕ → ℝ)
    {k : ℕ} (hJ : finiteSafeCutoff l n H u < k) (hk : k ≤ H) :
    1 / (finiteWalk l n u k : ℝ) * (Real.exp (2 * profileRoot l) + 1) < 1 / 2 := by
  apply lt_of_not_ge
  intro h
  exact not_le_of_gt hJ (le_csSup ⟨H, fun _ h ↦ h.1⟩ ⟨hk, h⟩)

/-- Equality of the coupled prefix identifies the exact two cutoffs whenever
both last unsafe indices lie in that prefix. -/
theorem finiteSafeCutoff_eq_local_of_prefix (l : ℝ) (n H K : ℕ) (u : ℕ → ℝ)
    (hKH : K ≤ H)
    (hb : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (hfinite : finiteSafeCutoff l n H u ≤ K) (hlocal : localSafeCutoff l u ≤ K)
    (heq : ∀ k ≤ K, finiteWalk l n u k = localWalk l u k) :
    finiteSafeCutoff l n H u = localSafeCutoff l u := by
  unfold finiteSafeCutoff localSafeCutoff
  congr 1
  ext k
  constructor
  · intro hk
    have hkJ : k ≤ finiteSafeCutoff l n H u :=
      le_csSup ⟨H, fun _ h ↦ h.1⟩ hk
    have hkK := hkJ.trans hfinite
    change (1 / 2 : ℝ) ≤ 1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)
    simpa only [heq k hkK] using hk.2
  · intro hk
    change (1 / 2 : ℝ) ≤ 1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1) at hk
    have hkK : k ≤ K := (le_csSup hb hk).trans hlocal
    refine ⟨hkK.trans hKH, ?_⟩
    simpa only [heq k hkK] using hk

theorem finiteSafeCutoff_le_of_count_ratio {l M : ℝ} (hl : 1 < l) (hM : 0 ≤ M)
    (n H J : ℕ) (u : ℕ → ℝ)
    (hJ : M * (2 * (Real.exp 2 + 1)) ≤ J)
    (hcount : ∀ k ≤ H, (k : ℝ) / (finiteWalk l n u k : ℝ) ≤ M) :
    finiteSafeCutoff l n H u ≤ J := by
  apply csSup_le'
  intro k hk
  obtain ⟨hpos, hsmall⟩ := (sourceUnsafe_iff l _).mp hk.2
  have hratio := (div_le_iff₀ hpos).mp (hcount k hk.1)
  have hupper : (k : ℝ) ≤ J := hratio.trans
    ((mul_le_mul_of_nonneg_left (hsmall.trans (sourceSafeThreshold_le hl)) hM).trans hJ)
  exact_mod_cast hupper

/-- The finite cutoff, clipped by full-horizon survival as in the paper, is
tight uniformly on compact supercritical parameter sets. -/
theorem finiteSafeCutoff_survival_uniform_tight {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J N : ℕ, ∀ n ≥ N, ∀ l ∈ I, uniformLaw.real {u | J <
      (if ∀ k ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u k then
        finiteSafeCutoff l n ⌊T * n⌋₊ u else 0)} < ε := by
  obtain ⟨M, N, hMN⟩ := coupled_count_ratio_uniform_tight hI hT hparams hε
  obtain ⟨J, hJ⟩ := exists_nat_gt ((M : ℝ) * (2 * (Real.exp 2 + 1)))
  refine ⟨J, N, ?_⟩
  intro n hn l hl
  apply lt_of_le_of_lt (measureReal_mono ?_) (hMN n hn l hl)
  intro u hu
  change J < (if ∀ k ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u k then
    finiteSafeCutoff l n ⌊T * n⌋₊ u else 0) at hu
  split_ifs at hu with hsurv
  · refine ⟨hsurv, ?_⟩
    by_contra hbad
    have hratio : ∀ k ≤ ⌊T * n⌋₊, (k : ℝ) / (finiteWalk l n u k : ℝ) ≤ M :=
      fun k hk ↦ le_of_not_gt (fun h ↦ hbad ⟨k, hk, h⟩)
    exact not_le_of_gt hu (finiteSafeCutoff_le_of_count_ratio (hparams l hl).1
      (Nat.cast_nonneg M) n ⌊T * n⌋₊ J u hJ.le hratio)
  · exact False.elim (Nat.not_lt_zero J hu)

end HeightPaper.CountCoupling
