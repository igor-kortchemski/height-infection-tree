module

public import HeightPaper.Probability.UniformWalkBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Three-quarter-power fluctuations of the local walk

Bounded independent increments give summable deviation probabilities.  The
resulting random fluctuation envelope is finite almost surely and has tails
uniform in the parameter.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace HeightPaper.CountCoupling

noncomputable def walkFluctuation (l : ℝ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  (localWalk l u k : ℝ) - 1 - k * localDrift l

theorem walkFluctuation_eq_sum (l : ℝ) (u : ℕ → ℝ) (k : ℕ) :
    walkFluctuation l u k = ∑ i ∈ Finset.range k, (localStep l i u - localDrift l) := by
  simp only [walkFluctuation, localWalk_cast, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  ring

theorem walkFluctuation_subgaussian {l : ℝ} (hl : 0 ≤ l) (k : ℕ) :
    HasSubgaussianMGF (fun u ↦ walkFluctuation l u k) k uniformLaw := by
  have hi := (localStep_independent l).comp (fun _ x ↦ x - localDrift l)
    (fun _ ↦ measurable_id.sub_const _)
  have h := HasSubgaussianMGF.sum_of_iIndepFun hi
    (s := Finset.range k) (fun i _ ↦ localStep_subgaussian hl i)
  simpa only [Function.comp_def, ← walkFluctuation_eq_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one] using h

theorem walkFluctuation_abs_tail {l : ℝ} (hl : 0 ≤ l) (k : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    uniformLaw.real {u | ε ≤ |walkFluctuation l u k|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * k)) := by
  have h := walkFluctuation_subgaussian hl k
  have hp := h.measure_ge_le hε
  have hn := h.neg.measure_ge_le hε
  have heq : {u | ε ≤ |walkFluctuation l u k|} =
      {u | ε ≤ walkFluctuation l u k} ∪ {u | ε ≤ -walkFluctuation l u k} := by
    ext u
    simp only [mem_ofPred_eq, mem_union, le_abs]
  rw [heq]
  have hu := measureReal_union_le (μ := uniformLaw)
    {u | ε ≤ walkFluctuation l u k} {u | ε ≤ -walkFluctuation l u k}
  have hn' : uniformLaw.real {u | ε ≤ -walkFluctuation l u k} ≤
      Real.exp (-ε ^ 2 / (2 * k)) := by
    simpa only [Pi.neg_apply, NNReal.coe_natCast] using hn
  have hp' : uniformLaw.real {u | ε ≤ walkFluctuation l u k} ≤
      Real.exp (-ε ^ 2 / (2 * k)) := by
    simpa only [NNReal.coe_natCast] using hp
  linarith

theorem localDrift_mem_Icc {l : ℝ} (hl : 0 ≤ l) : localDrift l ∈ Icc (-1 : ℝ) 1 := by
  have hd : 0 < 1 + l := by linarith
  constructor
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (div_le_iff₀ hd).mpr
    linarith

theorem walkFluctuation_abs_le {l : ℝ} (hl : 0 ≤ l) (u : ℕ → ℝ) (k : ℕ) :
    |walkFluctuation l u k| ≤ 2 * k := by
  rw [walkFluctuation_eq_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range k, |localStep l i u - localDrift l| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range k, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨ha, hb⟩ := localStep_mem_Icc l i u
      obtain ⟨hc, hd⟩ := localDrift_mem_Icc hl
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    _ = _ := by simp; ring

noncomputable def deviationMajorant (k : ℕ) : ℝ :=
  2 * Real.exp (-(k : ℝ) ^ (1 / 2 : ℝ) / 2)

theorem summable_deviationMajorant : Summable deviationMajorant := by
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have ho := (isLittleO_exp_neg_mul_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 2) (-4)).comp_tendsto ht
  have ho' : (fun n : ℕ ↦ Real.exp (-(n : ℝ) ^ (1 / 2 : ℝ) / 2))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) := by
    convert ho.isBigO using 1
    · funext n
      congr 1
      ring
    · funext n
      simp only [Function.comp_def]
      rw [← Real.rpow_mul (Nat.cast_nonneg n)]
      norm_num
  exact (summable_of_isBigO_nat (Real.summable_nat_rpow.mpr (by norm_num)) ho').mul_left 2

def deviationEvent (l : ℝ) (k : ℕ) : Set (ℕ → ℝ) :=
  {u | (k : ℝ) ^ (3 / 4 : ℝ) ≤ |walkFluctuation l u k|}

theorem deviationEvent_measure_le {l : ℝ} (hl : 0 ≤ l) (k : ℕ) :
    uniformLaw (deviationEvent l k) ≤ ENNReal.ofReal (deviationMajorant k) := by
  have h := walkFluctuation_abs_tail hl k
    (Real.rpow_nonneg (Nat.cast_nonneg k) (3 / 4 : ℝ))
  have hexp : -((k : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (2 * k) =
      -(k : ℝ) ^ (1 / 2 : ℝ) / 2 := by
    by_cases hk : k = 0
    · simp [hk]
    · have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      have hp : ((k : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = (k : ℝ) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hkpos.le]
        norm_num
      have hq : (k : ℝ) ^ (3 / 2 : ℝ) / k = (k : ℝ) ^ (1 / 2 : ℝ) := by
        calc
          _ = (k : ℝ) ^ (3 / 2 : ℝ) / (k : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_sub hkpos]; norm_num
      rw [hp]
      calc
        _ = -((k : ℝ) ^ (3 / 2 : ℝ) / k) / 2 := by ring
        _ = _ := by rw [hq]
  rw [hexp] at h
  rw [← ofReal_measureReal (μ := uniformLaw) (s := deviationEvent l k)]
  exact ENNReal.ofReal_le_ofReal h

theorem sourceDeviation_le (l : ℝ) (u : ℕ → ℝ) (k : ℕ) :
    |(localWalk l u k : ℝ) - k * localDrift l| ≤ 1 + |walkFluctuation l u k| := by
  have he : (localWalk l u k : ℝ) - k * localDrift l = 1 + walkFluctuation l u k := by
    unfold walkFluctuation
    ring
  rw [he]
  simpa only [abs_one] using abs_add_le (1 : ℝ) (walkFluctuation l u k)

/-- A deterministic conversion of a late fluctuation bound into an envelope
valid at every positive time. -/
theorem sourceDeviation_envelope {l : ℝ} (hl : 0 ≤ l) (u : ℕ → ℝ) (N : ℕ)
    (hsmall : ∀ k ≥ N, |walkFluctuation l u k| < (k : ℝ) ^ (3 / 4 : ℝ)) :
    ∀ k ≥ 1, |(localWalk l u k : ℝ) - k * localDrift l| ≤
      (2 * N + 3) * (k : ℝ) ^ (3 / 4 : ℝ) := by
  intro k hk
  have hp : (1 : ℝ) ≤ (k : ℝ) ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  have hC : (0 : ℝ) ≤ 2 * N + 3 := by positivity
  by_cases hkN : k < N
  · have hkR : (k : ℝ) ≤ N := by exact_mod_cast hkN.le
    calc
      _ ≤ 1 + |walkFluctuation l u k| := sourceDeviation_le l u k
      _ ≤ 1 + 2 * k := add_le_add_right (walkFluctuation_abs_le hl u k) 1
      _ ≤ 2 * N + 3 := by linarith
      _ ≤ _ := by nlinarith
  · have hs := (hsmall k (by omega)).le
    calc
      _ ≤ 1 + |walkFluctuation l u k| := sourceDeviation_le l u k
      _ ≤ 2 * (k : ℝ) ^ (3 / 4 : ℝ) := by linarith
      _ ≤ _ := by nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]

/-- The actual walk has an almost surely finite three-quarter-power envelope. -/
theorem localWalk_ae_power_deviation {l : ℝ} (hl : 0 ≤ l) :
    ∀ᵐ u ∂uniformLaw, ∃ C : ℝ, 0 < C ∧ ∀ k ≥ 1,
      |(localWalk l u k : ℝ) - k * localDrift l| ≤ C * (k : ℝ) ^ (3 / 4 : ℝ) := by
  have hsum : (∑' k, uniformLaw (deviationEvent l k)) ≠ ∞ :=
    ne_top_of_le_ne_top summable_deviationMajorant.tsum_ofReal_ne_top
      (ENNReal.tsum_le_tsum (deviationEvent_measure_le hl))
  filter_upwards [ae_eventually_notMem hsum] with u hu
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  refine ⟨2 * N + 3, by positivity, sourceDeviation_envelope hl u N ?_⟩
  intro k hk
  exact lt_of_not_ge (hN k hk)

/-- Uniform tightness of the fluctuation envelopes. The cutoff and multiplier
are independent of the parameter, even on the whole nonnegative half-line. -/
theorem localWalk_power_deviation_uniform_tight {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ l ≥ 0,
      uniformLaw.real {u | ∃ (k : ℕ), 1 ≤ k ∧
        C * (k : ℝ) ^ (3 / 4 : ℝ) < |(localWalk l u k : ℝ) - k * localDrift l|} ≤ ε := by
  have ht := ENNReal.tendsto_sum_nat_add
    (fun k ↦ ENNReal.ofReal (deviationMajorant k))
    summable_deviationMajorant.tsum_ofReal_ne_top
  obtain ⟨N, hN⟩ := (ht.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  refine ⟨2 * N + 3, by positivity, fun l hl ↦ ?_⟩
  have hsub : {u | ∃ (k : ℕ), 1 ≤ k ∧
        (2 * N + 3) * (k : ℝ) ^ (3 / 4 : ℝ) < |(localWalk l u k : ℝ) - k * localDrift l|}
      ⊆ ⋃ j : ℕ, deviationEvent l (j + N) := by
    intro u hu
    by_contra hnot
    have hsmall : ∀ k ≥ N, |walkFluctuation l u k| < (k : ℝ) ^ (3 / 4 : ℝ) := by
      intro k hk
      apply lt_of_not_ge
      intro hbad
      apply hnot
      refine mem_iUnion.mpr ⟨k - N, ?_⟩
      rw [Nat.sub_add_cancel hk]
      exact hbad
    obtain ⟨k, hk, hbad⟩ := hu
    exact (not_lt_of_ge (sourceDeviation_envelope hl u N hsmall k hk)) hbad
  have hb : uniformLaw {u | ∃ (k : ℕ), 1 ≤ k ∧
        (2 * N + 3) * (k : ℝ) ^ (3 / 4 : ℝ) < |(localWalk l u k : ℝ) - k * localDrift l|}
      ≤ ENNReal.ofReal ε := by
    calc
      _ ≤ uniformLaw (⋃ j : ℕ, deviationEvent l (j + N)) := measure_mono hsub
      _ ≤ ∑' j, uniformLaw (deviationEvent l (j + N)) := measure_iUnion_le _
      _ ≤ ∑' j, ENNReal.ofReal (deviationMajorant (j + N)) :=
        ENNReal.tsum_le_tsum (fun j ↦ deviationEvent_measure_le hl (j + N))
      _ ≤ _ := hN.le
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
    (ENNReal.toReal_ofReal hε.le)

/-- Uniform tightness of the last time the walk is below any fixed safe level.
This also controls the manuscript's local normalizer cutoff when its parameter
dependent safe levels have a common upper bound. -/
theorem localWalk_safeCutoff_uniform_tight {l₀ : ℝ} (hl₀ : 1 < l₀) (A : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ l ≥ l₀,
      uniformLaw.real {u | ∃ k ≥ N, (localWalk l u k : ℝ) ≤ A} ≤ ε := by
  obtain ⟨N₀, hN₀⟩ := ((lateLowerFailure_tendsto hl₀).eventually (Iio_mem_nhds hε)).exists
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (A / (localDrift l₀ / 2))
  refine ⟨max N₀ N₁, fun l hl ↦ ?_⟩
  apply (measureReal_mono (μ := uniformLaw) (s₂ := lateLowerFailure l₀ N₀) ?_).trans hN₀.le
  intro u hu
  obtain ⟨k, hk, hwalk⟩ := hu
  have hk₀ : N₀ ≤ k := (le_max_left _ _).trans hk
  have hk₁ : N₁ ≤ k := (le_max_right _ _).trans hk
  have hbig : A < localDrift l₀ / 2 * k := by
    have hh := (div_lt_iff₀ (half_pos (localDrift_pos hl₀))).mp hN₁
    have hkR : (N₁ : ℝ) ≤ k := by exact_mod_cast hk₁
    nlinarith [localDrift_pos hl₀]
  refine ⟨k, hk₀, ?_⟩
  have hm : (localWalk l₀ u k : ℝ) ≤ localWalk l u k :=
    Int.cast_le.mpr (localWalk_mono (by linarith) hl u k)
  exact (hm.trans hwalk).trans_lt hbig

end HeightPaper.CountCoupling
