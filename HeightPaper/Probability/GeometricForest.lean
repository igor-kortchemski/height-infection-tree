module

public import HeightPaper.Probability.GeometricBranching
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Independent forests of geometric-offspring branching processes

The population of a generation in a forest is the sum of independent branching
generation draws. Its zero probability is exactly a power, which yields the
exponential estimates for maximum height used by the dangling-tree argument.
No coupling of this forest to the epidemic is asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace HeightPaper.Branching

/-- Geometric offspring have a finite first moment for every positive success
parameter, including the degenerate parameter one. -/
theorem integrable_offspring {p : unitInterval} (hp : 0 < (p : ℝ)) :
    Integrable (fun k : ℕ ↦ (k : ℝ)) (offspringLaw p).toMeasure := by
  have hp0 : p ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    simpa using hp.ne' this
  have hr : ‖1 - (p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr p.property.2)]
    linarith
  rw [offspringLaw, Measure.toPMF_toMeasure, integrable_geometricMeasure_iff hp0]
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable.mul_left (p : ℝ)
  convert hs using 1
  ext k
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k)]
  ring

/-- The offspring parameter called `geometricMean` is indeed the expected
number of children under the constructed offspring law. -/
theorem integral_offspring_eq_mean {p : unitInterval} (hp : 0 < (p : ℝ)) :
    ∫ k : ℕ, (k : ℝ) ∂(offspringLaw p).toMeasure = geometricMean p := by
  have hp0 : p ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    simpa using hp.ne' this
  have hr : ‖1 - (p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr p.property.2)]
    linarith
  rw [offspringLaw, Measure.toPMF_toMeasure, integral_geometricMeasure hp0]
  simp only [smul_eq_mul]
  calc
    (∑' k : ℕ, ((1 - (p : ℝ)) ^ k * p) * (k : ℝ)) =
        (p : ℝ) * ∑' k : ℕ, (k : ℝ) * (1 - (p : ℝ)) ^ k := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      ring
    _ = geometricMean p := by
      rw [tsum_coe_mul_geometric_of_norm_lt_one hr]
      unfold geometricMean
      rw [sub_sub_cancel]
      field_simp

/-- Population at level `h` in `N` independent copies of the branching tree. -/
def forestGenerationLaw (p : unitInterval) (N h : ℕ) : PMF ℕ :=
  independentSum (generationLaw p h) N

/-- Probability that the whole forest has height below `h`. -/
def forestExtinctionProbability (p : unitInterval) (N h : ℕ) : ℝ :=
  (forestGenerationLaw p N h).toMeasure.real {0}

/-- Probability that at least one of the independent roots reaches level `h`. -/
def forestHeightTail (p : unitInterval) (N h : ℕ) : ℝ :=
  (forestGenerationLaw p N h).toMeasure.real {k | 0 < k}

theorem forestExtinctionProbability_eq (p : unitInterval) (N h : ℕ) :
    forestExtinctionProbability p N h = extinctionProbability p h ^ N := by
  rw [forestExtinctionProbability, measureReal_def,
    PMF.toMeasure_apply_singleton _ 0 (measurableSet_singleton 0)]
  simp only [forestGenerationLaw, independentSum_zero, ENNReal.toReal_pow, extinctionProbability]

theorem forestHeightTail_eq (p : unitInterval) (N h : ℕ) :
    forestHeightTail p N h = 1 - (1 - heightTail p h) ^ N := by
  have hset : {k : ℕ | 0 < k} = ({0} : Set ℕ)ᶜ := by ext k; simp; omega
  rw [forestHeightTail, hset, measureReal_compl (measurableSet_singleton 0), probReal_univ]
  change 1 - forestExtinctionProbability p N h = _
  rw [forestExtinctionProbability_eq, heightTail_eq_one_sub, sub_sub_cancel]

/-- The union bound follows here from the exact independent-forest law. -/
theorem forestHeightTail_le_mul (p : unitInterval) (N h : ℕ) :
    forestHeightTail p N h ≤ (N : ℝ) * heightTail p h := by
  have he := one_add_mul_sub_le_pow
    (show (-1 : ℝ) ≤ extinctionProbability p h by
      linarith [extinctionProbability_nonneg p h]) N
  rw [forestHeightTail_eq, heightTail_eq_one_sub]
  simp only [sub_sub_cancel]
  linarith

/-- The probability that all independent roots fail to reach a level is
bounded by the exponential of minus the expected number that reach it. -/
theorem forestExtinctionProbability_le_exp (p : unitInterval) (N h : ℕ) :
    forestExtinctionProbability p N h ≤ Real.exp (-(N : ℝ) * heightTail p h) := by
  have hq : extinctionProbability p h ≤ Real.exp (-heightTail p h) := by
    calc
      extinctionProbability p h = 1 - heightTail p h := by
        rw [heightTail_eq_one_sub, sub_sub_cancel]
      _ ≤ _ := Real.one_sub_le_exp_neg _
  rw [forestExtinctionProbability_eq]
  have hpow := pow_le_pow_left₀ (extinctionProbability_nonneg p h) hq N
  rw [← Real.exp_nat_mul] at hpow
  convert hpow using 1
  congr 1
  ring

/-- Upper bound for the maximum of `N` independent subcritical tree heights. -/
theorem forestHeightTail_le_geometric {p : unitInterval}
    (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (N h : ℕ) :
    forestHeightTail p N h ≤ (N : ℝ) * geometricMean p ^ h :=
  (forestHeightTail_le_mul p N h).trans
    (mul_le_mul_of_nonneg_left (heightTail_bounds hp hp1 h).2 (Nat.cast_nonneg N))

/-- Lower-tail estimate for the maximum of `N` independent subcritical tree
heights. The positive factor `1-m` is uniform in the height and forest size. -/
theorem forestExtinctionProbability_le_geometric_exp {p : unitInterval}
    (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (N h : ℕ) :
    forestExtinctionProbability p N h ≤
      Real.exp (-(N : ℝ) * ((1 - geometricMean p) * geometricMean p ^ h)) := by
  apply (forestExtinctionProbability_le_exp p N h).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (heightTail_bounds hp hp1 h).1
    (neg_nonpos.mpr (Nat.cast_nonneg N))

/-- The upper maximum-height probability vanishes whenever the expected
geometric upper count vanishes. -/
theorem tendsto_forestHeightTail_zero {ι : Type*} {ℓ : Filter ι}
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (N H : ι → ℕ)
    (hscale : Tendsto (fun n ↦ (N n : ℝ) * geometricMean p ^ H n) ℓ (𝓝 0)) :
    Tendsto (fun n ↦ forestHeightTail p (N n) (H n)) ℓ (𝓝 0) :=
  squeeze_zero (fun _ ↦ measureReal_nonneg)
    (fun n ↦ forestHeightTail_le_geometric hp hp1 (N n) (H n)) hscale

/-- The lower maximum-height probability vanishes whenever the expected
geometric lower count diverges. -/
theorem tendsto_forestExtinctionProbability_zero {ι : Type*} {ℓ : Filter ι}
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (N H : ι → ℕ)
    (hscale : Tendsto (fun n ↦ (N n : ℝ) * geometricMean p ^ H n) ℓ atTop) :
    Tendsto (fun n ↦ forestExtinctionProbability p (N n) (H n)) ℓ (𝓝 0) := by
  have hm1 := geometricMean_lt_one hp
  have hexp : Tendsto
      (fun n ↦ Real.exp (-(1 - geometricMean p) * ((N n : ℝ) * geometricMean p ^ H n)))
      ℓ (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (Tendsto.const_mul_atTop_of_neg (by linarith : -(1 - geometricMean p) < 0) hscale)
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hexp
  intro n
  have heq : -(N n : ℝ) * ((1 - geometricMean p) * geometricMean p ^ H n) =
      -(1 - geometricMean p) * ((N n : ℝ) * geometricMean p ^ H n) := by ring
  simpa only [heq, forestExtinctionProbability] using
    forestExtinctionProbability_le_geometric_exp hp hp1 (N n) (H n)

end HeightPaper.Branching
