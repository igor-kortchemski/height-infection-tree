module

public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Analysis.SpecificLimits.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Geometric-offspring branching generations

The generation law is constructed from an actual geometric offspring draw and
independent descendant-generation draws for its children. The probability of
an empty generation is derived from that probability kernel, not assumed as a
recursion. Its complement is the branching height tail at each integer level.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace HeightPaper.Branching

/-- The sum of `k` independent draws from a natural-valued law. -/
def independentSum (p : PMF ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | k + 1 => p.bind fun a ↦ (independentSum p k).map (fun b ↦ a + b)

theorem map_add_zero (q : PMF ℕ) (a : ℕ) :
    (q.map (fun b ↦ a + b)) 0 = if a = 0 then q 0 else 0 := by
  classical
  cases a with
  | zero => simp [PMF.map_apply, eq_comm]
  | succ a =>
      have hh (b : ℕ) : ¬0 = a + 1 + b := by omega
      simp only [PMF.map_apply, hh, ↓reduceIte, tsum_zero, Nat.succ_ne_zero]

theorem independentSum_zero (p : PMF ℕ) (k : ℕ) :
    independentSum p k 0 = (p 0) ^ k := by
  classical
  induction k with
  | zero => simp [independentSum]
  | succ k ih =>
      simp only [independentSum, PMF.bind_apply, map_add_zero]
      simp only [mul_ite, mul_zero, tsum_ite_eq, ih, pow_succ']

/-- The offspring count has the standard geometric law with success parameter
`p`; its mass at `k` is `(1-p)^k p` when `p ≠ 0`. -/
def offspringLaw (p : unitInterval) : PMF ℕ := (geometricMeasure p).toPMF

theorem offspringLaw_apply {p : unitInterval} (hp : p ≠ 0) (k : ℕ) :
    offspringLaw p k = ENNReal.ofReal (1 - (p : ℝ)) ^ k * ENNReal.ofReal (p : ℝ) := by
  rw [offspringLaw, Measure.toPMF_apply, geometricMeasure_singleton hp]
  rw [ENNReal.ofReal_mul (pow_nonneg (sub_nonneg.mpr p.property.2) k),
    ENNReal.ofReal_pow (sub_nonneg.mpr p.property.2)]

/-- Generation zero contains the ancestor. To construct generation `h+1`, draw
its geometric number of children and independently draw generation `h` below
each child. Thus every offspring choice has exactly the specified law. -/
def generationLaw (p : unitInterval) : ℕ → PMF ℕ
  | 0 => PMF.pure 1
  | h + 1 => (offspringLaw p).bind fun k ↦ independentSum (generationLaw p h) k

theorem generationLaw_zero_zero (p : unitInterval) : generationLaw p 0 0 = 0 := by
  simp [generationLaw]

/-- The geometric generating function evaluated at an empty-child probability. -/
theorem offspring_pgf {p : unitInterval} (hp : p ≠ 0) (a : ℝ≥0∞) :
    (∑' k : ℕ, offspringLaw p k * a ^ k) =
      ENNReal.ofReal (p : ℝ) * (1 - ENNReal.ofReal (1 - (p : ℝ)) * a)⁻¹ := by
  simp_rw [offspringLaw_apply hp]
  have heq (k : ℕ) : ENNReal.ofReal (1 - (p : ℝ)) ^ k * ENNReal.ofReal (p : ℝ) * a ^ k =
      ENNReal.ofReal (p : ℝ) * (ENNReal.ofReal (1 - (p : ℝ)) * a) ^ k := by
    rw [mul_pow]
    ac_rfl
  simp_rw [heq]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- The empty-generation recursion follows from the independent offspring
construction and the geometric probability generating function. -/
theorem generationLaw_succ_zero {p : unitInterval} (hp : p ≠ 0) (h : ℕ) :
    generationLaw p (h + 1) 0 = ENNReal.ofReal (p : ℝ) *
      (1 - ENNReal.ofReal (1 - (p : ℝ)) * generationLaw p h 0)⁻¹ := by
  simp only [generationLaw, PMF.bind_apply, independentSum_zero]
  exact offspring_pgf hp _

/-- Probability that generation `h` is empty. -/
def extinctionProbability (p : unitInterval) (h : ℕ) : ℝ := (generationLaw p h 0).toReal

theorem extinctionProbability_nonneg (p : unitInterval) (h : ℕ) :
    0 ≤ extinctionProbability p h := ENNReal.toReal_nonneg

theorem extinctionProbability_le_one (p : unitInterval) (h : ℕ) :
    extinctionProbability p h ≤ 1 := by
  exact (ENNReal.toReal_mono ENNReal.one_ne_top ((generationLaw p h).coe_le_one 0)).trans_eq
    ENNReal.toReal_one

@[simp] theorem extinctionProbability_zero (p : unitInterval) : extinctionProbability p 0 = 0 := by
  simp [extinctionProbability, generationLaw_zero_zero]

theorem extinctionProbability_succ {p : unitInterval} (hp : p ≠ 0) (h : ℕ) :
    extinctionProbability p (h + 1) =
      (p : ℝ) / (1 - (1 - (p : ℝ)) * extinctionProbability p h) := by
  have ha : ENNReal.ofReal (1 - (p : ℝ)) ≤ 1 := by
    exact ENNReal.ofReal_le_one.mpr (by linarith [p.property.1])
  have hprod : ENNReal.ofReal (1 - (p : ℝ)) * generationLaw p h 0 ≤ 1 := by
    simpa using mul_le_mul' ha ((generationLaw p h).coe_le_one 0)
  simp only [extinctionProbability, generationLaw_succ_zero hp, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_sub_of_le hprod ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_ofReal p.property.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr p.property.2), div_eq_mul_inv]

/-- The mean of the geometric offspring distribution. -/
def geometricMean (p : unitInterval) : ℝ := (1 - (p : ℝ)) / p

theorem geometricMean_pos {p : unitInterval} (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < geometricMean p := div_pos (sub_pos.mpr hp1) hp

theorem geometricMean_lt_one {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) :
    geometricMean p < 1 := by
  unfold geometricMean
  rw [div_lt_one (by linarith : 0 < (p : ℝ))]
  linarith

theorem one_sub_parameter_eq_mean_mul {p : unitInterval} (hp : 0 < (p : ℝ)) :
    1 - (p : ℝ) = geometricMean p * p := by
  simp [geometricMean, hp.ne']

theorem extinctionProbability_succ_mean {p : unitInterval} (hp : 0 < (p : ℝ)) (h : ℕ) :
    extinctionProbability p (h + 1) =
      1 / (1 + geometricMean p - geometricMean p * extinctionProbability p h) := by
  have hp0 : p ≠ 0 := by intro h; have := congrArg Subtype.val h; simpa using hp.ne' this
  have hm : 0 ≤ geometricMean p := div_nonneg (sub_nonneg.mpr p.property.2) hp.le
  have hq := extinctionProbability_le_one p h
  have hden : 0 < 1 - (1 - (p : ℝ)) * extinctionProbability p h := by
    have hmul := mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr p.property.2)
    nlinarith
  have hden' : 0 < 1 + geometricMean p - geometricMean p * extinctionProbability p h := by
    have hmul := mul_le_mul_of_nonneg_left hq hm
    linarith
  rw [extinctionProbability_succ hp0]
  apply (div_eq_div_iff hden.ne' hden'.ne').mpr
  have heq := one_sub_parameter_eq_mean_mul hp
  nlinarith

/-- Empty-generation probabilities increase with the generation index. -/
theorem extinctionProbability_mono {p : unitInterval} (hp : 0 < (p : ℝ)) :
    Monotone (extinctionProbability p) := by
  have hm : 0 ≤ geometricMean p :=
    div_nonneg (sub_nonneg.mpr p.property.2) hp.le
  have hd (k : ℕ) :
      0 < 1 + geometricMean p - geometricMean p * extinctionProbability p k := by
    have hq := extinctionProbability_le_one p k
    nlinarith [mul_le_mul_of_nonneg_left hq hm]
  apply monotone_nat_of_le_succ
  intro k
  induction k with
  | zero =>
      simpa only [extinctionProbability_zero] using
        extinctionProbability_nonneg p 1
  | succ k ih =>
      rw [extinctionProbability_succ_mean hp,
        extinctionProbability_succ_mean hp]
      apply one_div_le_one_div_of_le (hd (k + 1))
      nlinarith [mul_nonneg hm (sub_nonneg.mpr ih)]

/-- Exact extinction probability for any noncritical positive geometric
parameter, obtained from the branching kernel. -/
theorem extinctionProbability_eq_of_mean_ne_one {p : unitInterval}
    (hp : 0 < (p : ℝ)) (hm1 : geometricMean p ≠ 1) (h : ℕ) :
    extinctionProbability p h =
      (1 - geometricMean p ^ h) / (1 - geometricMean p ^ (h + 1)) := by
  have hm : 0 ≤ geometricMean p := div_nonneg (sub_nonneg.mpr p.property.2) hp.le
  have hpow (k : ℕ) : 1 - geometricMean p ^ (k + 1) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    exact hm1 ((pow_eq_one_iff_of_nonneg hm (Nat.succ_ne_zero k)).mp heq.symm)
  induction h with
  | zero => simp
  | succ h ih =>
      rw [extinctionProbability_succ_mean hp, ih]
      have hden : 0 < 1 + geometricMean p - geometricMean p *
          ((1 - geometricMean p ^ h) / (1 - geometricMean p ^ (h + 1))) := by
        rw [← ih]
        have := mul_le_mul_of_nonneg_left (extinctionProbability_le_one p h) hm
        linarith
      apply (div_eq_div_iff hden.ne' (hpow (h + 1))).mpr
      field_simp [hpow h]
      simp only [pow_succ]
      ring

/-- The subcritical specialization of the exact extinction formula. -/
theorem extinctionProbability_eq {p : unitInterval}
    (hp : 1 / 2 < (p : ℝ)) (_hp1 : (p : ℝ) < 1) (h : ℕ) :
    extinctionProbability p h =
      (1 - geometricMean p ^ h) / (1 - geometricMean p ^ (h + 1)) :=
  extinctionProbability_eq_of_mean_ne_one (by linarith) (geometricMean_lt_one hp).ne h

/-- Branching height at least `h` means that generation `h` is nonempty. -/
def heightTail (p : unitInterval) (h : ℕ) : ℝ :=
  (generationLaw p h).toMeasure.real {k | 0 < k}

theorem heightTail_eq_one_sub (p : unitInterval) (h : ℕ) :
    heightTail p h = 1 - extinctionProbability p h := by
  have hset : {k : ℕ | 0 < k} = ({0} : Set ℕ)ᶜ := by ext k; simp; omega
  rw [heightTail, hset, measureReal_compl (measurableSet_singleton 0), probReal_univ]
  congr 1
  exact congrArg ENNReal.toReal ((generationLaw p h).toMeasure_apply_singleton 0
    (measurableSet_singleton 0))

/-- The exact geometric-branching height tail, including height zero. -/
theorem heightTail_eq {p : unitInterval}
    (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (h : ℕ) :
    heightTail p h =
      (1 - geometricMean p) * geometricMean p ^ h / (1 - geometricMean p ^ (h + 1)) := by
  have hp0 : 0 < (p : ℝ) := by linarith
  have hm := geometricMean_pos hp0 hp1
  have hm1 := geometricMean_lt_one hp
  have hd : 1 - geometricMean p ^ (h + 1) ≠ 0 :=
    (sub_pos.mpr (pow_lt_one₀ hm.le hm1 (Nat.succ_ne_zero h))).ne'
  rw [heightTail_eq_one_sub, extinctionProbability_eq hp hp1]
  field_simp
  simp only [pow_succ]
  ring

/-- Uniform exponential lower and upper height tails, with constants that
depend only on the geometric offspring parameter. -/
theorem heightTail_bounds {p : unitInterval}
    (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (h : ℕ) :
    (1 - geometricMean p) * geometricMean p ^ h ≤ heightTail p h ∧
      heightTail p h ≤ geometricMean p ^ h := by
  have hp0 : 0 < (p : ℝ) := by linarith
  have hm := geometricMean_pos hp0 hp1
  have hm1 := geometricMean_lt_one hp
  have hpow : 0 ≤ geometricMean p ^ h := pow_nonneg hm.le h
  have hnext : 0 ≤ geometricMean p ^ (h + 1) := pow_nonneg hm.le (h + 1)
  have hd : 0 < 1 - geometricMean p ^ (h + 1) :=
    sub_pos.mpr (pow_lt_one₀ hm.le hm1 (Nat.succ_ne_zero h))
  have hnextle : geometricMean p ^ (h + 1) ≤ geometricMean p := by
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hm.le hm1.le) hm.le).trans_eq (one_mul _)
  rw [heightTail_eq hp hp1]
  constructor
  · apply (le_div_iff₀ hd).mpr
    have hnonneg := mul_nonneg (sub_nonneg.mpr hm1.le) hpow
    nlinarith [mul_nonneg hnonneg hnext]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_le_mul_of_nonneg_left hnextle hpow]

/-- The probability of a nonempty generation tends to zero in the subcritical
case. This follows from the constructed generation laws and their tail bound. -/
theorem tendsto_heightTail_zero {p : unitInterval}
    (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (heightTail p) atTop (𝓝 0) := by
  have hm := geometricMean_pos (by linarith : 0 < (p : ℝ)) hp1
  exact squeeze_zero (fun h ↦ measureReal_nonneg) (fun h ↦ (heightTail_bounds hp hp1 h).2)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hm.le (geometricMean_lt_one hp))

/-- The common form `1/p - 1` of the geometric mean in `lem:couplage`. -/
theorem geometricMean_eq_inv_sub_one {p : unitInterval} (hp : 0 < (p : ℝ)) :
    geometricMean p = 1 / (p : ℝ) - 1 := by
  unfold geometricMean
  field_simp

/-- In the supercritical case, writing the tail with inverse powers makes its
positive limiting survival probability explicit. -/
theorem heightTail_eq_supercritical {p : unitInterval} (hp : 0 < (p : ℝ))
    (hm1 : 1 < geometricMean p) (h : ℕ) :
    heightTail p h = (geometricMean p - 1) /
      (geometricMean p - (geometricMean p)⁻¹ ^ h) := by
  have hm : 0 < geometricMean p := lt_trans zero_lt_one hm1
  have hpow : geometricMean p ^ h ≠ 0 := pow_ne_zero h hm.ne'
  have hden : 1 - geometricMean p ^ (h + 1) ≠ 0 :=
    (sub_neg.mpr (one_lt_pow₀ hm1 (Nat.succ_ne_zero h))).ne
  have hinv : (geometricMean p)⁻¹ ^ h ≤ 1 :=
    pow_le_one₀ (inv_nonneg.mpr hm.le) (inv_le_one_of_one_le₀ hm1.le)
  have hden' : geometricMean p - (geometricMean p)⁻¹ ^ h ≠ 0 := by
    apply ne_of_gt
    linarith
  rw [heightTail_eq_one_sub, extinctionProbability_eq_of_mean_ne_one hp hm1.ne']
  apply (eq_div_iff hden').mpr
  rw [inv_pow]
  field_simp
  simp only [pow_succ]
  ring

theorem extinctionProbability_lt_one_of_mean_gt_one {p : unitInterval}
    (hp : 0 < (p : ℝ)) (hm1 : 1 < geometricMean p) (h : ℕ) :
    extinctionProbability p h < 1 := by
  have hm : 0 < geometricMean p := lt_trans zero_lt_one hm1
  have hpow : (geometricMean p)⁻¹ ^ h ≤ 1 :=
    pow_le_one₀ (inv_nonneg.mpr hm.le) (inv_le_one_of_one_le₀ hm1.le)
  have htail : 0 < heightTail p h := by
    rw [heightTail_eq_supercritical hp hm1]
    exact div_pos (sub_pos.mpr hm1) (by linarith)
  rw [heightTail_eq_one_sub] at htail
  linarith

/-- Supercritical survival probability, derived from the actual branching
generation laws. -/
theorem tendsto_heightTail_supercritical {p : unitInterval} (hp : 0 < (p : ℝ))
    (hm1 : 1 < geometricMean p) :
    Tendsto (heightTail p) atTop (𝓝 (1 - 1 / geometricMean p)) := by
  have hm : 0 < geometricMean p := lt_trans zero_lt_one hm1
  have hi : (geometricMean p)⁻¹ < 1 := (inv_lt_one₀ hm).mpr hm1
  have hz := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hm.le) hi
  have ht : Tendsto (fun h : ℕ ↦ (geometricMean p - 1) /
      (geometricMean p - (geometricMean p)⁻¹ ^ h)) atTop
      (𝓝 ((geometricMean p - 1) / geometricMean p)) := by
    convert tendsto_const_nhds.div (tendsto_const_nhds.sub hz)
      (show geometricMean p - 0 ≠ 0 by simpa using hm.ne') using 1
    simp only [sub_zero]
  have heq : (geometricMean p - 1) / geometricMean p = 1 - 1 / geometricMean p := by
    field_simp
  simpa only [← heightTail_eq_supercritical hp hm1, heq] using ht

/-- Geometric success probability giving any prescribed nonnegative mean. -/
def successParameter (m : ℝ) (hm : 0 ≤ m) : unitInterval :=
  ⟨1 / (1 + m), by constructor <;> first
    | positivity
    | exact (div_le_one (by positivity : 0 < 1 + m)).mpr (by linarith)⟩

theorem successParameter_pos (m : ℝ) (hm : 0 ≤ m) :
    0 < (successParameter m hm : ℝ) := by dsimp [successParameter]; positivity

@[simp] theorem geometricMean_successParameter (m : ℝ) (hm : 0 ≤ m) :
    geometricMean (successParameter m hm) = m := by
  unfold geometricMean successParameter
  dsimp
  field_simp
  ring

/-- The Bernoulli success parameter in the main theorem is the survival limit
of geometric-offspring branching with mean `l`. This does not yet identify the
epidemic's survival event with the branching event. -/
theorem tendsto_heightTail_mean_parameter {l : ℝ} (hl : 1 < l) :
    Tendsto (heightTail (successParameter l (by linarith))) atTop (𝓝 (1 - 1 / l)) := by
  simpa using tendsto_heightTail_supercritical
    (successParameter_pos l (show 0 ≤ l by linarith)) (by simpa using hl)

/-- The height distribution of a supercritical geometric Bienaymé tree,
conditioned on eventual extinction, is the height distribution of the
subcritical geometric tree with reciprocal mean. The equality is stated at
every finite generation, where extinction by generation `h` is a cylinder
event. The denominator `1 / l` is the eventual-extinction probability. -/
theorem extinctionProbability_supercritical_conditioned_eq_subcritical
    {l : ℝ} (hl : 1 < l) (h : ℕ) :
    extinctionProbability (successParameter l (by linarith)) h / (1 / l) =
      extinctionProbability (successParameter (1 / l) (by positivity)) h := by
  have hl0 : 0 < l := by linarith
  have hlinv : 0 < 1 / l := by positivity
  have hne : l ≠ 1 := by linarith
  have hne' : 1 / l ≠ 1 := by
    intro heq
    have := (div_eq_one_iff_eq hl0.ne').mp heq
    exact hne this.symm
  rw [extinctionProbability_eq_of_mean_ne_one
      (successParameter_pos l (by linarith)) (by simpa using hne) h,
    extinctionProbability_eq_of_mean_ne_one
      (successParameter_pos (1 / l) (by positivity)) (by simpa using hne') h]
  simp only [geometricMean_successParameter]
  have hpow : l ^ (h + 1) ≠ 1 := by
    exact (one_lt_pow₀ hl (Nat.succ_ne_zero h)).ne'
  have hinvpow : (1 / l) ^ (h + 1) ≠ 1 := by
    exact (pow_lt_one₀ hlinv.le (by exact (div_lt_one hl0).mpr hl) (Nat.succ_ne_zero h)).ne
  have hden : 1 - l ^ (h + 1) ≠ 0 := sub_ne_zero.mpr hpow.symm
  have hden' : 1 - (1 / l) ^ (h + 1) ≠ 0 := sub_ne_zero.mpr hinvpow.symm
  field_simp [hl0.ne', hden, hden']
  simp only [pow_succ]
  field_simp [hl0.ne']
  have hid : l ^ h * l⁻¹ ^ h = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hl0.ne', one_pow]
  linear_combination (1 - l) * hid

theorem tendsto_extinctionProbability_supercritical {l : ℝ} (hl : 1 < l) :
    Tendsto (extinctionProbability (successParameter l (by linarith)))
      atTop (𝓝 (1 / l)) := by
  have h := tendsto_heightTail_mean_parameter hl
  have h' : Tendsto (fun k : ℕ ↦
      1 - heightTail (successParameter l (by linarith)) k)
      atTop (𝓝 (1 - (1 - 1 / l))) := tendsto_const_nhds.sub h
  have heq (k : ℕ) :
      1 - heightTail (successParameter l (by linarith)) k =
        extinctionProbability (successParameter l (by linarith)) k := by
    rw [heightTail_eq_one_sub]
    ring
  simp_rw [heq] at h'
  convert h' using 1
  ring_nf

/-- The conditional upper tail of the supercritical height after excluding
infinite survival is exactly the subcritical height tail at every level. -/
theorem heightTail_supercritical_conditioned_eq_subcritical
    {l : ℝ} (hl : 1 < l) (h : ℕ) :
    (heightTail (successParameter l (by linarith)) h - (1 - 1 / l)) / (1 / l) =
      heightTail (successParameter (1 / l) (by positivity)) h := by
  rw [heightTail_eq_one_sub, heightTail_eq_one_sub]
  have heq := extinctionProbability_supercritical_conditioned_eq_subcritical hl h
  calc
    (1 - extinctionProbability (successParameter l (by linarith)) h -
      (1 - 1 / l)) / (1 / l) =
        1 - extinctionProbability (successParameter l (by linarith)) h / (1 / l) := by
          have hl0 : l ≠ 0 := by linarith
          field_simp [hl0]
          ring
    _ = 1 - extinctionProbability (successParameter (1 / l) (by positivity)) h := by
      rw [heq]

end HeightPaper.Branching
