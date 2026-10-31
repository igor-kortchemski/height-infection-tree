module

public import HeightPaper.Probability.CountCouplingBounds
public import Mathlib.Data.Nat.Sqrt

/-!
# Uniform control of the entire local-to-finite walk gap

Independent coordinate intervals dominate the gap. Their Bernoulli exponential
moments, grouped into blocks of squared time divided by population, control all
times simultaneously with the source normalization `1 + k² / n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace HeightPaper.CountCoupling

noncomputable def gapIndicator (l : ℝ) (n k : ℕ) (u : ℕ → ℝ) : ℝ := by
  classical
  exact if u ∈ thresholdGap l n k then 1 else 0

noncomputable def gapCount (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, gapIndicator l n i u

theorem measurable_gapIndicator (l : ℝ) (n k : ℕ) : Measurable (gapIndicator l n k) :=
  measurable_const.ite (measurableSet_thresholdGap l n k) measurable_const

theorem gapIndicator_independent (l : ℝ) (n : ℕ) :
    iIndepFun (gapIndicator l n) uniformLaw := by
  classical
  have h := iIndepFun_infinitePi (P := fun _ : ℕ ↦ unitUniform) (X := fun k x ↦
    if finiteThreshold l n (n - k) < x ∧ x ≤ birthThreshold l then (1 : ℝ) else 0)
    (fun _ ↦ measurable_const.ite (measurableSet_Ioi.inter measurableSet_Iic) measurable_const)
  convert h using 1
  · funext k u
    by_cases hu : finiteThreshold l n (n - k) < u k ∧ u k ≤ birthThreshold l <;>
      simp [gapIndicator, thresholdGap, hu]
  · rfl

theorem gapIndicator_nonneg (l : ℝ) (n k : ℕ) (u : ℕ → ℝ) : 0 ≤ gapIndicator l n k u := by
  unfold gapIndicator
  split <;> norm_num

theorem gapCount_mono (l : ℝ) (n : ℕ) (u : ℕ → ℝ) : Monotone (gapCount l n u) := by
  intro k K hk
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
    (fun i _ _ ↦ gapIndicator_nonneg l n i u)

theorem gapCount_mem_Icc (l : ℝ) (n k : ℕ) (u : ℕ → ℝ) :
    gapCount l n u k ∈ Icc (0 : ℝ) k := by
  constructor
  · exact Finset.sum_nonneg (fun i _ ↦ gapIndicator_nonneg l n i u)
  · calc
      _ ≤ ∑ _i ∈ Finset.range k, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        unfold gapIndicator
        split <;> norm_num
      _ = _ := by simp

theorem measurable_gapCount (l : ℝ) (n k : ℕ) : Measurable (fun u ↦ gapCount l n u k) :=
  Finset.measurable_sum _ (fun i _ ↦ measurable_gapIndicator l n i)

theorem gapIndicator_mgf (l : ℝ) (n k : ℕ) :
    mgf (gapIndicator l n k) uniformLaw 1 =
      1 + (Real.exp 1 - 1) * uniformLaw.real (thresholdGap l n k) := by
  have heq : (fun u ↦ Real.exp (1 * gapIndicator l n k u)) =
      fun u ↦ 1 + (Real.exp 1 - 1) * (thresholdGap l n k).indicator (fun _ ↦ (1 : ℝ)) u := by
    funext u
    by_cases hu : u ∈ thresholdGap l n k <;> simp [gapIndicator, hu]
  unfold mgf
  rw [heq, integral_add (integrable_const 1)
    ((integrable_const (1 : ℝ)).indicator (measurableSet_thresholdGap l n k) |>.const_mul _),
    integral_const_mul, integral_indicator_const _ (measurableSet_thresholdGap l n k)]
  simp

theorem gapIndicator_mgf_le (l : ℝ) (n k : ℕ) :
    mgf (gapIndicator l n k) uniformLaw 1 ≤
      Real.exp ((Real.exp 1 - 1) * uniformLaw.real (thresholdGap l n k)) := by
  rw [gapIndicator_mgf]
  simpa only [add_comm] using Real.add_one_le_exp
    ((Real.exp 1 - 1) * uniformLaw.real (thresholdGap l n k))

theorem gapCount_mgf_le {l L : ℝ} (hl : 0 ≤ l) (hlL : l ≤ L)
    {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    mgf (fun u ↦ gapCount l n u k) uniformLaw 1 ≤
      Real.exp ((Real.exp 1 - 1) * L * (k : ℝ) ^ 2 / n) := by
  have he : (fun u ↦ gapCount l n u k) = ∑ i ∈ Finset.range k, gapIndicator l n i := by
    funext u
    simp [gapCount]
  rw [he, (gapIndicator_independent l n).mgf_sum (measurable_gapIndicator l n)]
  calc
    _ ≤ ∏ i ∈ Finset.range k,
        Real.exp ((Real.exp 1 - 1) * uniformLaw.real (thresholdGap l n i)) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ mgf_nonneg) (fun i _ ↦ gapIndicator_mgf_le l n i)
    _ = Real.exp ((Real.exp 1 - 1) *
        ∑ i ∈ Finset.range k, uniformLaw.real (thresholdGap l n i)) := by
      rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs : (∑ i ∈ Finset.range k, uniformLaw.real (thresholdGap l n i)) ≤
          L * (k : ℝ) ^ 2 / n := by
        calc
          _ ≤ ∑ _i ∈ Finset.range k, L * (k : ℝ) / n := by
            apply Finset.sum_le_sum
            intro i hi
            have hik : i ≤ k := (Finset.mem_range.mp hi).le
            apply (thresholdGap_probability_le hl hn (hik.trans hk)).trans
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
            exact mul_le_mul hlL (by exact_mod_cast hik) (Nat.cast_nonneg i) (hl.trans hlL)
          _ = _ := by simp [pow_two]; ring
      have he0 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hh := mul_le_mul_of_nonneg_left hs he0
      convert hh using 1
      ring

theorem gapCount_chernoff {l L : ℝ} (hl : 0 ≤ l) (hlL : l ≤ L)
    {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) (a : ℝ) :
    uniformLaw.real {u | a ≤ gapCount l n u k} ≤
      Real.exp ((Real.exp 1 - 1) * L * (k : ℝ) ^ 2 / n - a) := by
  have hi := integrable_exp_mul_of_mem_Icc (μ := uniformLaw) (t := 1)
    (measurable_gapCount l n k).aemeasurable
    (Filter.Eventually.of_forall (gapCount_mem_Icc l n k))
  calc
    _ ≤ Real.exp (-1 * a) * mgf (fun u ↦ gapCount l n u k) uniformLaw 1 :=
      measure_ge_le_exp_mul_mgf a zero_le_one hi
    _ ≤ Real.exp (-1 * a) * Real.exp ((Real.exp 1 - 1) * L * (k : ℝ) ^ 2 / n) :=
      mul_le_mul_of_nonneg_left (gapCount_mgf_le hl hlL hn hk) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem walkGap_le_gapCount {l : ℝ} (hl : 0 ≤ l) {n k : ℕ} (hk : k ≤ n)
    (u : ℕ → ℝ) :
    (localWalk l u k : ℝ) - finiteWalk l n u k ≤ 2 * gapCount l n u k := by
  have he : (localWalk l u k : ℝ) - finiteWalk l n u k =
      ∑ i ∈ Finset.range k, ((if localBirth l u i then (1 : ℝ) else -1) -
        (if finiteBirth l n u i then (1 : ℝ) else -1)) := by
    simp [localWalk, finiteWalk, Int.cast_sum, Int.cast_ite, Finset.sum_sub_distrib]
  rw [he, gapCount, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hsame : finiteBirth l n u i = localBirth l u i
  · rw [hsame, sub_self]
    exact mul_nonneg (by norm_num) (gapIndicator_nonneg l n i u)
  · have hgap : u ∈ thresholdGap l n i :=
      birth_disagreement_subset hl ((Finset.mem_range.mp hi).trans_le hk) u hsame
    rw [gapIndicator, ite_eq_left hgap]
    cases localBirth l u i <;> cases finiteBirth l n u i <;> norm_num

theorem walkGap_le_twice_time (l : ℝ) (n k : ℕ) (u : ℕ → ℝ) :
    (localWalk l u k : ℝ) - finiteWalk l n u k ≤ 2 * k := by
  have he : (localWalk l u k : ℝ) - finiteWalk l n u k =
      ∑ i ∈ Finset.range k, ((if localBirth l u i then (1 : ℝ) else -1) -
        (if finiteBirth l n u i then (1 : ℝ) else -1)) := by
    simp [localWalk, finiteWalk, Int.cast_sum, Int.cast_ite, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ _i ∈ Finset.range k, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      cases localBirth l u i <;> cases finiteBirth l n u i <;> norm_num
    _ = _ := by simp; ring

def gapBlockEnd (n ell : ℕ) : ℕ := min n (Nat.sqrt (n * ell))

theorem gapBlockEnd_le (n ell : ℕ) : gapBlockEnd n ell ≤ n := min_le_left _ _

theorem gapBlockEnd_square_le (n ell : ℕ) : (gapBlockEnd n ell) ^ 2 ≤ n * ell := by
  exact (Nat.pow_le_pow_left (min_le_right _ _) 2).trans (Nat.sqrt_le' _)

theorem gapBlock_chernoff {l L : ℝ} (hl : 0 ≤ l) (hlL : l ≤ L)
    {n : ℕ} (hn : 0 < n) (ell : ℕ) (A : ℝ) :
    uniformLaw.real {u | A * ell ≤ gapCount l n u (gapBlockEnd n ell)} ≤
      Real.exp (((Real.exp 1 - 1) * L - A) * ell) := by
  apply (gapCount_chernoff hl hlL hn (gapBlockEnd_le n ell) (A * ell)).trans
  apply Real.exp_le_exp.mpr
  have hs : ((gapBlockEnd n ell : ℕ) : ℝ) ^ 2 / n ≤ ell := by
    apply (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
    have hh := gapBlockEnd_square_le n ell
    exact_mod_cast (by simpa [mul_comm] using hh)
  have hc : 0 ≤ (Real.exp 1 - 1) * L :=
    mul_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)]) (hl.trans hlL)
  have hh := mul_le_mul_of_nonneg_left hs hc
  calc
    _ = ((Real.exp 1 - 1) * L) *
        (((gapBlockEnd n ell : ℕ) : ℝ) ^ 2 / n) - A * ell := by ring
    _ ≤ ((Real.exp 1 - 1) * L) * ell - A * ell := sub_le_sub_right hh _
    _ = _ := by ring

/-- A large normalized gap is witnessed at one squared-time block endpoint. -/
theorem walkGap_large_subset {l A : ℝ} (hl : 0 ≤ l) (hA : 1 ≤ A)
    {n : ℕ} (hn : 0 < n) :
    {u | ∃ k : ℕ, 2 * A * (1 + (k : ℝ) ^ 2 / n) <
        (localWalk l u k : ℝ) - finiteWalk l n u k} ⊆
      ⋃ j : ℕ, {u | A * (j + 1 : ℕ) ≤ gapCount l n u (gapBlockEnd n (j + 1))} := by
  intro u hu
  obtain ⟨k, hbad⟩ := hu
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkn : k ≤ n := by
    by_contra hkn
    have hkR : (n : ℝ) ≤ k := by exact_mod_cast (show n ≤ k by omega)
    have hsq : (k : ℝ) ≤ (k : ℝ) ^ 2 / n := by
      apply (le_div_iff₀ hnR).mpr
      nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
    have hb := walkGap_le_twice_time l n k u
    have hp : 0 ≤ 1 + (k : ℝ) ^ 2 / n := by positivity
    have hscale := mul_le_mul_of_nonneg_right hA hp
    nlinarith
  let j := k ^ 2 / n
  have hmod : k ^ 2 % n < n := Nat.mod_lt _ hn
  have hdiv : k ^ 2 % n + n * j = k ^ 2 := Nat.mod_add_div _ _
  have hceil : k ^ 2 ≤ n * (j + 1) := by nlinarith
  have hkB : k ≤ gapBlockEnd n (j + 1) :=
    le_min hkn (Nat.le_sqrt'.mpr hceil)
  have hj : ((j + 1 : ℕ) : ℝ) ≤ 1 + (k : ℝ) ^ 2 / n := by
    have hq : n * j ≤ k ^ 2 := by omega
    have hqR : (j : ℝ) ≤ (k : ℝ) ^ 2 / n := by
      apply (le_div_iff₀ hnR).mpr
      exact_mod_cast (by simpa [mul_comm] using hq)
    push_cast
    linarith
  refine mem_iUnion.mpr ⟨j, ?_⟩
  change A * ((j + 1 : ℕ) : ℝ) ≤ gapCount l n u (gapBlockEnd n (j + 1))
  have hgap := (walkGap_le_gapCount hl hkn u).trans
    (mul_le_mul_of_nonneg_left (gapCount_mono l n u hkB) (by norm_num : (0 : ℝ) ≤ 2))
  have hscale := mul_le_mul_of_nonneg_left hj (zero_le_one.trans hA)
  nlinarith

/-- Quantitative geometric-block bound. Its right side does not depend on the
population size or on the parameter in `[0,L]`. -/
theorem walkGap_scaled_tail {L : ℝ} (hL : 0 ≤ L) (m : ℕ)
    {l : ℝ} (hl : 0 ≤ l) (hlL : l ≤ L) {n : ℕ} (hn : 0 < n) :
    uniformLaw.real {u | ∃ k : ℕ,
      2 * ((Real.exp 1 - 1) * L + m + 1) * (1 + (k : ℝ) ^ 2 / n) <
        (localWalk l u k : ℝ) - finiteWalk l n u k} ≤
      Real.exp (-(m : ℝ)) * ∑' j : ℕ, Real.exp (-((j + 1 : ℕ) : ℝ)) := by
  let A := (Real.exp 1 - 1) * L + m + 1
  have he0 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hA : 1 ≤ A := by
    dsimp [A]
    have hc := mul_nonneg he0 hL
    linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  have hbase : Summable (fun j : ℕ ↦ Real.exp (-((j + 1 : ℕ) : ℝ))) :=
    Real.summable_exp_neg_nat.comp_injective (show Function.Injective (fun j : ℕ ↦ j + 1) from
      fun a b h ↦ Nat.add_right_cancel h)
  have hsum : Summable (fun j : ℕ ↦ Real.exp (-(m : ℝ)) * Real.exp (-((j + 1 : ℕ) : ℝ))) :=
    hbase.mul_left _
  have hblock (j : ℕ) :
      uniformLaw {u | A * (j + 1 : ℕ) ≤ gapCount l n u (gapBlockEnd n (j + 1))} ≤
        ENNReal.ofReal (Real.exp (-(m : ℝ)) * Real.exp (-((j + 1 : ℕ) : ℝ))) := by
    rw [← ofReal_measureReal (μ := uniformLaw)]
    apply ENNReal.ofReal_le_ofReal
    apply (gapBlock_chernoff hl hlL hn (j + 1) A).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [A]
    push_cast
    nlinarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m,
      show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
  have hb : uniformLaw {u | ∃ k : ℕ,
        2 * A * (1 + (k : ℝ) ^ 2 / n) < (localWalk l u k : ℝ) - finiteWalk l n u k} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ)) * ∑' j : ℕ, Real.exp (-((j + 1 : ℕ) : ℝ))) := by
    calc
      _ ≤ uniformLaw (⋃ j : ℕ, {u | A * (j + 1 : ℕ) ≤
          gapCount l n u (gapBlockEnd n (j + 1))}) :=
        measure_mono (walkGap_large_subset hl hA hn)
      _ ≤ ∑' j : ℕ, uniformLaw {u | A * (j + 1 : ℕ) ≤
          gapCount l n u (gapBlockEnd n (j + 1))} := measure_iUnion_le _
      _ ≤ ∑' j : ℕ, ENNReal.ofReal
          (Real.exp (-(m : ℝ)) * Real.exp (-((j + 1 : ℕ) : ℝ))) := ENNReal.tsum_le_tsum hblock
      _ = _ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hsum, tsum_mul_left]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

/-- Full simultaneous-time tightness of the source-normalized walk gap,
uniformly in both the population size and bounded nonnegative parameters. -/
theorem walkGap_uniform_tight {L : ℝ} (hL : 0 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ n : ℕ, 0 < n → ∀ l ∈ Icc (0 : ℝ) L,
      uniformLaw.real {u | ∃ k : ℕ, R <
        ((localWalk l u k : ℝ) - finiteWalk l n u k) / (1 + (k : ℝ) ^ 2 / n)} ≤ ε := by
  have ht := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    tendsto_natCast_atTop_atTop).mul_const (∑' j : ℕ, Real.exp (-((j + 1 : ℕ) : ℝ)))
  simp only [zero_mul] at ht
  obtain ⟨m, hm⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  refine ⟨2 * ((Real.exp 1 - 1) * L + m + 1), ?_, fun n hn l hl ↦ ?_⟩
  · have he0 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    positivity
  · have heq : {u | ∃ k : ℕ,
        2 * ((Real.exp 1 - 1) * L + m + 1) <
        ((localWalk l u k : ℝ) - finiteWalk l n u k) / (1 + (k : ℝ) ^ 2 / n)} =
        {u | ∃ k : ℕ, 2 * ((Real.exp 1 - 1) * L + m + 1) * (1 + (k : ℝ) ^ 2 / n) <
        (localWalk l u k : ℝ) - finiteWalk l n u k} := by
      ext u
      simp only [mem_ofPred_eq]
      apply exists_congr
      intro k
      exact lt_div_iff₀ (by positivity : (0 : ℝ) < 1 + (k : ℝ) ^ 2 / n)
    rw [heq]
    exact (walkGap_scaled_tail hL m hl.1 hl.2 hn).trans hm.le

end HeightPaper.CountCoupling
