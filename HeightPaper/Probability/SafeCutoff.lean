module

public import HeightPaper.Probability.UniformWalkDeviation
public import HeightPaper.Probability.UniformCountControl
public import HeightPaper.Analysis.Parameters

/-!
# The paper's local safe-product cutoff

The source threshold is retained exactly. Its bound by `2 * (exp 2 + 1)`
uses `z_λ < 1`. On the almost-sure bounded-set event the natural supremum is
the last unsafe index, and it is tight uniformly for all `λ ≥ λ₀ > 1`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology Classical

namespace HeightPaper.CountCoupling

noncomputable def sourceSafeThreshold (l : ℝ) : ℝ :=
  2 * (Real.exp (2 * profileRoot l) + 1)

theorem sourceSafeThreshold_pos (l : ℝ) : 0 < sourceSafeThreshold l := by
  unfold sourceSafeThreshold
  positivity

theorem sourceSafeThreshold_le {l : ℝ} (hl : 1 < l) :
    sourceSafeThreshold l ≤ 2 * (Real.exp 2 + 1) := by
  have h := Real.exp_le_exp.mpr (show 2 * profileRoot l ≤ 2 by
    linarith [profileRoot_lt_one hl])
  unfold sourceSafeThreshold
  linarith

/-- Exact equivalence with the denominator test defining the source cutoffs. -/
theorem sourceUnsafe_iff (l s : ℝ) :
    (1 / 2 : ℝ) ≤ 1 / s * (Real.exp (2 * profileRoot l) + 1) ↔
      0 < s ∧ s ≤ sourceSafeThreshold l := by
  have hC : 0 < Real.exp (2 * profileRoot l) + 1 := by positivity
  rw [one_div_mul_eq_div]
  constructor
  · intro h
    have hs : 0 < s := by
      by_contra hh
      have hle := div_nonpos_of_nonneg_of_nonpos hC.le (le_of_not_gt hh)
      linarith
    refine ⟨hs, ?_⟩
    have h := (le_div_iff₀ hs).mp h
    unfold sourceSafeThreshold
    linarith
  · rintro ⟨hs, h⟩
    apply (le_div_iff₀ hs).mpr
    unfold sourceSafeThreshold at h
    linarith

/-- The exact last unsafe local index. The totalized natural supremum is used
off the almost-sure finite-set event; on survival this is the source `J`. -/
noncomputable def localSafeCutoff (l : ℝ) (u : ℕ → ℝ) : ℕ :=
  sSup {k : ℕ | (1 / 2 : ℝ) ≤
    1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)}

theorem localSafeCutoff_eq_iSup (l : ℝ) (u : ℕ → ℝ) :
    localSafeCutoff l u = ⨆ k : ℕ, if (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1) then k else 0 := by
  classical
  let P : ℕ → Prop := fun k ↦ (1 / 2 : ℝ) ≤
    1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)
  have hzero : P 0 := by
    dsimp [P, localWalk]
    simp only [Int.cast_one, div_one, one_mul]
    linarith [Real.exp_pos (2 * profileRoot l)]
  change sSup {k | P k} = sSup (range (fun k ↦ if P k then k else 0))
  congr 1
  ext k
  constructor
  · intro hk
    exact ⟨k, by simp only [show P k from hk, ↓reduceIte]⟩
  · rintro ⟨j, hj⟩
    by_cases h : P j
    · have hj' : j = k := by simpa only [h, ↓reduceIte] using hj
      exact hj' ▸ h
    · have hk : k = 0 := by simpa only [h, ↓reduceIte] using hj.symm
      change P k
      rw [hk]
      exact hzero

theorem measurable_localSafeCutoff (l : ℝ) : Measurable (localSafeCutoff l) := by
  have hm (k : ℕ) : Measurable (fun u : ℕ → ℝ ↦ if (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1) then k else 0) := by
    apply measurable_const.ite _ measurable_const
    exact measurableSet_le measurable_const
      ((measurable_const.div (measurable_localWalk_real l k)).mul_const _)
  simpa only [← localSafeCutoff_eq_iSup] using Measurable.iSup hm

theorem localSafeCutoff_le_of_no_late_small (l : ℝ) (u : ℕ → ℝ) (N : ℕ)
    (h : ∀ k ≥ N, sourceSafeThreshold l < (localWalk l u k : ℝ)) :
    localSafeCutoff l u ≤ N := by
  apply csSup_le'
  intro k hk
  have hsmall := ((sourceUnsafe_iff l (localWalk l u k)).mp hk).2
  by_contra hnot
  exact not_lt_of_ge hsmall (h k (by omega))

/-- The unsafe set is almost surely finite, including without conditioning on
infinite survival. Hence the natural supremum has its intended meaning. -/
theorem localSafeCutoff_ae_bddAbove {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)} := by
  filter_upwards [localWalk_ae_eventually_uniform_lower hl] with u ⟨N, hN⟩
  obtain ⟨J, hJ⟩ := exists_nat_gt (sourceSafeThreshold l / (localDrift l / 2))
  refine ⟨max N J, ?_⟩
  intro k hk
  by_contra hbad
  have hkN : N ≤ k := by omega
  have hkJ : (J : ℝ) ≤ k := by exact_mod_cast (show J ≤ k by omega)
  have hlarge : sourceSafeThreshold l < localDrift l / 2 * (k : ℝ) := by
    have h := (div_lt_iff₀ (half_pos (localDrift_pos hl))).mp hJ
    nlinarith [mul_le_mul_of_nonneg_left hkJ (half_pos (localDrift_pos hl)).le]
  exact not_lt_of_ge ((sourceUnsafe_iff l _).mp hk).2
    (hlarge.trans_le (hN k hkN l le_rfl))

/-- Every later factor obeys the strict source safe-denominator test. -/
theorem localSafeCutoff_safe_after (l : ℝ) (u : ℕ → ℝ)
    (hb : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    {k : ℕ} (hk : localSafeCutoff l u < k) :
    1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1) < 1 / 2 := by
  apply lt_of_not_ge
  intro h
  exact not_le_of_gt hk (le_csSup hb h)

/-- Tightness of the exact source local cutoff, with the multiplier chosen
before the parameter. This is stronger than the survival-clipped claim. -/
theorem localSafeCutoff_uniform_tight {l₀ : ℝ} (hl₀ : 1 < l₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ l ≥ l₀, uniformLaw.real {u | N < localSafeCutoff l u} ≤ ε := by
  obtain ⟨N, hN⟩ := localWalk_safeCutoff_uniform_tight hl₀ (2 * (Real.exp 2 + 1)) hε
  refine ⟨N, ?_⟩
  intro l hl
  apply (measureReal_mono ?_).trans (hN l hl)
  intro u hu
  change N < localSafeCutoff l u at hu
  by_contra hn
  apply not_le_of_gt hu
  apply localSafeCutoff_le_of_no_late_small
  intro k hk
  have hlarge : 2 * (Real.exp 2 + 1) < (localWalk l u k : ℝ) := by
    exact lt_of_not_ge (fun hh ↦ hn ⟨k, hk, hh⟩)
  exact (sourceSafeThreshold_le (hl₀.trans_le hl)).trans_lt hlarge

theorem localSafeCutoff_survival_uniform_tight {l₀ : ℝ} (hl₀ : 1 < l₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ l ≥ l₀, uniformLaw.real {u | N <
      (if ∀ k, 0 < localWalk l u k then localSafeCutoff l u else 0)} ≤ ε := by
  classical
  obtain ⟨N, hN⟩ := localSafeCutoff_uniform_tight hl₀ hε
  refine ⟨N, fun l hl ↦ (measureReal_mono ?_).trans (hN l hl)⟩
  intro u hu
  change N < (if ∀ k, 0 < localWalk l u k then localSafeCutoff l u else 0) at hu
  change N < localSafeCutoff l u
  split_ifs at hu with h
  · exact hu
  · exact False.elim (Nat.not_lt_zero N hu)

end HeightPaper.CountCoupling
