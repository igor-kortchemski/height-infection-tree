module

public import HeightPaper.Model.Urn
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The deterministic infinite product in the urn criterion

The paper's product is the limit of its finite products. We retain this meaning
explicitly, including the case of a nonsummable squared relative increment.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology BigOperators

namespace HeightPaper.Urn

/-- Squared relative increment, with the post-draw total in the denominator. -/
noncomputable def relativeSquare (D : Schedule) (k : ℕ) : ℝ :=
  (D.increment k : ℝ) ^ 2 / (D.total (k + 1) : ℝ) ^ 2

@[simp] theorem retention_eq (D : Schedule) (k : ℕ) :
    retention D k = 1 - relativeSquare D k := rfl

theorem relativeSquare_nonneg (D : Schedule) (k : ℕ) : 0 ≤ relativeSquare D k := by
  unfold relativeSquare
  positivity

theorem relativeSquare_le_one (D : Schedule) (k : ℕ) : relativeSquare D k ≤ 1 := by
  have h0 := D.positive k
  have h1 := D.positive (k + 1)
  have he := D.next k
  have hx := D.increment_ge k
  have ha : |D.increment k| ≤ D.total (k + 1) := abs_le.mpr ⟨by omega, by omega⟩
  have har : |(D.increment k : ℝ)| ≤ D.total (k + 1) := by exact_mod_cast ha
  have hs : (0 : ℝ) < D.total (k + 1) := Int.cast_pos.mpr h1
  unfold relativeSquare
  apply (div_le_one (sq_pos_of_pos hs)).mpr
  exact (sq_le_sq).mpr (by simpa [abs_of_pos hs] using har)

theorem retention_nonneg (D : Schedule) (k : ℕ) : 0 ≤ retention D k := by
  rw [retention_eq]
  exact sub_nonneg.mpr (relativeSquare_le_one D k)

theorem retention_le_one (D : Schedule) (k : ℕ) : retention D k ≤ 1 := by
  rw [retention_eq]
  linarith [relativeSquare_nonneg D k]

theorem retention_pos_of_total_ge_two (D : Schedule) (k : ℕ)
    (h : 2 ≤ D.total (k + 1)) : 0 < retention D k := by
  have h0 := D.positive k
  have he := D.next k
  have hx := D.increment_ge k
  have ha : |D.increment k| < D.total (k + 1) := abs_lt.mpr ⟨by omega, by omega⟩
  have har : |(D.increment k : ℝ)| < D.total (k + 1) := by exact_mod_cast ha
  have hs : (0 : ℝ) < D.total (k + 1) := Int.cast_pos.mpr (D.positive _)
  rw [retention_eq, sub_pos]
  apply (div_lt_one (sq_pos_of_pos hs)).mpr
  exact (sq_lt_sq).mpr (by simpa [abs_of_pos hs] using har)

theorem retention_eq_zero_of_hit_one (D : Schedule) (k : ℕ)
    (hprev : 2 ≤ D.total k) (hnext : D.total (k + 1) = 1) : retention D k = 0 := by
  have he := D.next k
  have hx := D.increment_ge k
  have hx' : D.increment k = -1 := by omega
  simp [retention, hnext, hx']

/-- Finite products decrease, remain nonnegative, and start at one. -/
noncomputable def retentionProduct (D : Schedule) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, retention D k

@[simp] theorem retentionProduct_zero (D : Schedule) : retentionProduct D 0 = 1 := by
  simp [retentionProduct]

theorem retentionProduct_succ (D : Schedule) (n : ℕ) :
    retentionProduct D (n + 1) = retentionProduct D n * retention D n :=
  Finset.prod_range_succ _ _

theorem retentionProduct_nonneg (D : Schedule) (n : ℕ) : 0 ≤ retentionProduct D n :=
  Finset.prod_nonneg (fun _ _ ↦ retention_nonneg D _)

theorem retentionProduct_antitone (D : Schedule) : Antitone (retentionProduct D) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [retentionProduct_succ]
  exact mul_le_of_le_one_right (retentionProduct_nonneg D n) (retention_le_one D n)

theorem retentionProduct_le_one (D : Schedule) (n : ℕ) : retentionProduct D n ≤ 1 := by
  simpa using retentionProduct_antitone D (Nat.zero_le n)

/-- The product appearing in `prop urnes`, defined by ordered finite products. -/
noncomputable def retentionLimit (D : Schedule) : ℝ := ⨅ n, retentionProduct D n

theorem retentionProduct_tendsto (D : Schedule) :
    Tendsto (retentionProduct D) atTop (𝓝 (retentionLimit D)) :=
  tendsto_atTop_ciInf (retentionProduct_antitone D)
    ⟨0, fun _ ⟨n, hn⟩ ↦ hn ▸ retentionProduct_nonneg D n⟩

theorem retentionLimit_nonneg (D : Schedule) : 0 ≤ retentionLimit D :=
  ge_of_tendsto (retentionProduct_tendsto D) (Eventually.of_forall (retentionProduct_nonneg D))

theorem retentionLimit_le_product (D : Schedule) (n : ℕ) :
    retentionLimit D ≤ retentionProduct D n :=
  ciInf_le ⟨0, fun _ ⟨n, hn⟩ ↦ hn ▸ retentionProduct_nonneg D n⟩ n

theorem retentionProduct_eq_zero_of_total_one (D : Schedule) (h0 : 2 ≤ D.total 0)
    (n : ℕ) (hn : D.total n = 1) : retentionProduct D n = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [retentionProduct_succ]
      by_cases h : D.total n = 1
      · rw [ih h, zero_mul]
      · have hpos := D.positive n
        rw [retention_eq_zero_of_hit_one D n (by omega) hn, mul_zero]

/-- If the urn ever has only one ball, the limiting product is zero. -/
theorem retentionLimit_eq_zero_of_total_one (D : Schedule) (h0 : 2 ≤ D.total 0)
    (n : ℕ) (hn : D.total n = 1) : retentionLimit D = 0 := by
  apply le_antisymm _ (retentionLimit_nonneg D)
  simpa [retentionProduct_eq_zero_of_total_one D h0 n hn] using retentionLimit_le_product D n


/-- Exponential domination of the finite product by its squared-increment sum. -/
theorem retentionProduct_le_exp (D : Schedule) (n : ℕ) :
    retentionProduct D n ≤ Real.exp (-∑ k ∈ Finset.range n, relativeSquare D k) := by
  calc
    retentionProduct D n ≤ ∏ k ∈ Finset.range n, Real.exp (-relativeSquare D k) := by
      apply Finset.prod_le_prod₀ (fun _ _ ↦ retention_nonneg D _)
      intro k _
      rw [retention_eq]
      linarith [Real.add_one_le_exp (-relativeSquare D k)]
    _ = _ := by rw [← Real.exp_sum, Finset.sum_neg_distrib]

/-- Divergence of the squared relative increments forces the product to vanish. -/
theorem retentionLimit_eq_zero_of_not_summable (D : Schedule)
    (h : ¬ Summable (relativeSquare D)) : retentionLimit D = 0 := by
  have hs := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (relativeSquare_nonneg D)).mp h
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
  have hp : Tendsto (retentionProduct D) atTop (𝓝 0) :=
    squeeze_zero (retentionProduct_nonneg D) (retentionProduct_le_exp D) he
  exact tendsto_nhds_unique (retentionProduct_tendsto D) hp

/-- A summable squared relative increment and the absence of single-ball urns
make the limiting product strictly positive. -/
theorem retentionLimit_pos (D : Schedule) (hsize : ∀ k, 2 ≤ D.total k)
    (hsum : Summable (relativeSquare D)) : 0 < retentionLimit D := by
  have hlog : Summable (fun k ↦ Real.log (retention D k)) := by
    simpa only [retention_eq, sub_eq_add_neg] using
      Real.summable_log_one_add_of_summable hsum.neg
  have hp := Real.hasProd_of_hasSum_log
    (fun k ↦ retention_pos_of_total_ge_two D k (hsize _)) hlog.hasSum
  have heq : retentionLimit D = Real.exp (∑' k, Real.log (retention D k)) :=
    tendsto_nhds_unique (retentionProduct_tendsto D) hp.tendsto_prod_nat
  rw [heq]
  exact Real.exp_pos _

/-- The deterministic product criterion in the equivalent formulation of `prop urnes`.
The initial total is at least two because both initial colours are present. -/
theorem retentionLimit_pos_iff (D : Schedule) (h0 : 2 ≤ D.total 0) :
    0 < retentionLimit D ↔
      (∀ k, 2 ≤ D.total k) ∧ Summable (relativeSquare D) := by
  constructor
  · intro h
    constructor
    · intro k
      by_contra hk
      have hp := D.positive k
      have hz := retentionLimit_eq_zero_of_total_one D h0 k (by omega)
      linarith
    · by_contra hn
      have hz := retentionLimit_eq_zero_of_not_summable D hn
      linarith
  · rintro ⟨hsize, hsum⟩
    exact retentionLimit_pos D hsize hsum


theorem retentionLimit_le_one (D : Schedule) : retentionLimit D ≤ 1 := by
  simpa using retentionLimit_le_product D 0

/-- The finite second moments converge to the expression used in the urn appendix. -/
theorem integral_proportion_sq_law_tendsto (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) :
    Tendsto (fun n ↦ ∫ r, (proportion (D.total n) r) ^ 2 ∂(law D r₀ n).toMeasure)
      atTop (𝓝 (proportion (D.total 0) r₀ +
        ((proportion (D.total 0) r₀) ^ 2 - proportion (D.total 0) r₀) * retentionLimit D)) := by
  have h := ((retentionProduct_tendsto D).const_mul
    ((proportion (D.total 0) r₀) ^ 2 - proportion (D.total 0) r₀)).const_add
      (proportion (D.total 0) r₀)
  exact h.congr (fun n ↦ (integral_proportion_sq_law D r₀ hr₀ hr₀s n).symm)

theorem integral_mixed_law_tendsto (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) :
    Tendsto (fun n ↦ ∫ r, proportion (D.total n) r * (1 - proportion (D.total n) r)
      ∂(law D r₀ n).toMeasure) atTop
      (𝓝 (proportion (D.total 0) r₀ * (1 - proportion (D.total 0) r₀) * retentionLimit D)) := by
  have h := (retentionProduct_tendsto D).const_mul
    (proportion (D.total 0) r₀ * (1 - proportion (D.total 0) r₀))
  exact h.congr (fun n ↦ (integral_mixed_law D r₀ hr₀ hr₀s n).symm)

/-- For a variable in `[0,1]`, its mixed-colour moment detects positive interior mass. -/
theorem integral_mixed_pos_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (Z : Ω → ℝ) (hZ : AEStronglyMeasurable Z μ)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1) :
    0 < (∫ ω, Z ω * (1 - Z ω) ∂μ) ↔ 0 < μ {ω | 0 < Z ω ∧ Z ω < 1} := by
  have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ Z ω * (1 - Z ω) := hbound.mono fun _ h ↦
    mul_nonneg h.1 (sub_nonneg.mpr h.2)
  have hi : Integrable (fun ω ↦ Z ω * (1 - Z ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (hZ.mul (aestronglyMeasurable_const.sub hZ)) ?_
    filter_upwards [hbound, hnonneg] with ω h hn
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    nlinarith
  have heq : μ (Function.support (fun ω ↦ Z ω * (1 - Z ω))) =
      μ {ω | 0 < Z ω ∧ Z ω < 1} := by
    apply measure_congr
    filter_upwards [hbound] with ω h
    apply propext
    change Z ω * (1 - Z ω) ≠ 0 ↔ 0 < Z ω ∧ Z ω < 1
    constructor
    · intro hn
      have hz0 : Z ω ≠ 0 := by intro hz; simp [hz] at hn
      have hz1 : Z ω ≠ 1 := by intro hz; simp [hz] at hn
      exact ⟨lt_of_le_of_ne h.1 hz0.symm, lt_of_le_of_ne h.2 hz1⟩
    · rintro ⟨h0, h1⟩
      exact ne_of_gt (mul_pos h0 (sub_pos.mpr h1))
  rw [← heq]
  exact integral_pos_iff_support_of_nonneg_ae hnonneg hi

end HeightPaper.Urn
