module

public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.PSeries
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# A strong law for bounded martingale differences

Weighted differences have uniformly bounded second moments, hence an almost-sure
limit. Summation by parts and Cesàro convergence remove the weights. This is the
bounded martingale strong-law route used for recorded urn draw frequencies.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace HeightPaper

variable {Ω : Type*}

noncomputable def weightedDifferenceSum (D : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ ↦ 0
  | n + 1 => fun ω ↦ weightedDifferenceSum D n ω + D n ω / (n + 1 : ℕ)

@[simp] theorem weightedDifferenceSum_zero (D : ℕ → Ω → ℝ) (ω : Ω) :
    weightedDifferenceSum D 0 ω = 0 := rfl

theorem weightedDifferenceSum_succ (D : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    weightedDifferenceSum D (n + 1) ω =
      weightedDifferenceSum D n ω + D n ω / (n + 1 : ℕ) := rfl

/-- Finite summation by parts for the reciprocal weights, including time zero. -/
theorem sum_differences_eq_weighted (D : ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) :
    ∑ i ∈ Finset.range n, D i ω =
      (n : ℝ) * weightedDifferenceSum D n ω -
        ∑ i ∈ Finset.range n, weightedDifferenceSum D i ω := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, weightedDifferenceSum_succ]
      push_cast
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring

/-- The deterministic Kronecker step: convergence of weighted sums implies
vanishing Cesàro averages of the original differences. -/
theorem tendsto_average_of_weighted_tendsto (D : ℕ → Ω → ℝ) (ω : Ω) {L : ℝ}
    (h : Tendsto (fun n ↦ weightedDifferenceSum D n ω) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, D i ω) atTop (𝓝 0) := by
  have ht := h.sub h.cesaro
  simp only [sub_self] at ht
  apply ht.congr
  intro n
  rw [sum_differences_eq_weighted D ω n]
  by_cases hn : n = 0
  · subst n
    simp
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp

variable [MeasurableSpace Ω]

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
  (D : ℕ → Ω → ℝ)
  (hmeas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (D n))
  (hbound : ∀ n, ∀ᵐ ω ∂μ, ‖D n ω‖ ≤ 1)

include hmeas in
theorem weightedDifferenceSum_stronglyAdapted : StronglyAdapted ℱ (weightedDifferenceSum D) := by
  intro n
  induction n with
  | zero => exact stronglyMeasurable_const
  | succ n ih =>
      have he : weightedDifferenceSum D (n + 1) = weightedDifferenceSum D n +
          (fun ω ↦ D n ω * (((n + 1 : ℕ) : ℝ)⁻¹)) := by
        funext ω
        change weightedDifferenceSum D n ω + D n ω / (n + 1 : ℕ) = _
        simp only [Pi.add_apply, div_eq_mul_inv]
      rw [he]
      exact (ih.mono (ℱ.mono (Nat.le_succ n))).add
        ((hmeas n).mul_const (((n + 1 : ℕ) : ℝ)⁻¹))

include hbound in
omit [IsProbabilityMeasure μ] in
theorem ae_norm_weightedDifferenceSum_le (n : ℕ) :
    ∀ᵐ ω ∂μ, ‖weightedDifferenceSum D n ω‖ ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      filter_upwards [ih, hbound n] with ω hw hd
      have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hh : ‖D n ω / (n + 1 : ℕ)‖ ≤ 1 := by
        rw [norm_div, Real.norm_of_nonneg (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by positivity)]
        exact (div_le_one (by positivity)).mpr (hd.trans hn)
      simpa only [weightedDifferenceSum_succ, Nat.cast_add, Nat.cast_one] using
        (norm_add_le (weightedDifferenceSum D n ω) (D n ω / (n + 1 : ℕ))).trans (add_le_add hw hh)

include hmeas hbound

theorem integrable_difference (n : ℕ) : Integrable (D n) μ :=
  (integrable_const (1 : ℝ)).mono' ((hmeas n).mono (ℱ.le _)).aestronglyMeasurable (hbound n)

theorem integrable_weightedDifferenceSum (n : ℕ) : Integrable (weightedDifferenceSum D n) μ :=
  (integrable_const (n : ℝ)).mono'
    ((weightedDifferenceSum_stronglyAdapted ℱ D hmeas n).mono (ℱ.le _)).aestronglyMeasurable
    (ae_norm_weightedDifferenceSum_le μ D hbound n)

theorem integrable_weightedDifferenceSum_sq (n : ℕ) :
    Integrable (fun ω ↦ (weightedDifferenceSum D n ω) ^ 2) μ := by
  refine (integrable_const ((n : ℝ) ^ 2)).mono'
    (((weightedDifferenceSum_stronglyAdapted ℱ D hmeas n).mono (ℱ.le _)).pow 2).aestronglyMeasurable ?_
  filter_upwards [ae_norm_weightedDifferenceSum_le μ D hbound n] with ω h
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem integrable_difference_sq (n : ℕ) : Integrable (fun ω ↦ (D n ω) ^ 2) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (((hmeas n).mono (ℱ.le _)).pow 2).aestronglyMeasurable ?_
  filter_upwards [hbound n] with ω h
  simpa only [norm_pow, one_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2

variable (hzero : ∀ n, μ[D n | ℱ n] =ᵐ[μ] 0)

include hzero

/-- The weighted partial sums are themselves an actual martingale. -/
theorem weightedDifferenceSum_martingale :
    Martingale (weightedDifferenceSum D) ℱ μ := by
  apply martingale_nat (weightedDifferenceSum_stronglyAdapted ℱ D hmeas)
    (integrable_weightedDifferenceSum μ ℱ D hmeas hbound)
  intro n
  have hmul := condExp_smul (μ := μ) ((n + 1 : ℕ) : ℝ)⁻¹ (D n) (ℱ n)
  have hsum := condExp_add (integrable_weightedDifferenceSum μ ℱ D hmeas hbound n)
    ((integrable_difference μ ℱ D hmeas hbound n).div_const ((n + 1 : ℕ) : ℝ)) (ℱ n)
  have hself := condExp_of_stronglyMeasurable (ℱ.le n)
    (weightedDifferenceSum_stronglyAdapted ℱ D hmeas n)
    (integrable_weightedDifferenceSum μ ℱ D hmeas hbound n)
  filter_upwards [hsum, hmul, hzero n] with ω hs hm hz
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hs hm hz
  have he : (fun ω ↦ D n ω / (n + 1 : ℕ)) =
      (((n + 1 : ℕ) : ℝ)⁻¹ • D n) := by funext x; simp [div_eq_mul_inv, mul_comm]
  rw [he] at hs
  rw [hm, hz, mul_zero, add_zero, hself] at hs
  have hstep : weightedDifferenceSum D (n + 1) =
      weightedDifferenceSum D n + (((n + 1 : ℕ) : ℝ)⁻¹ • D n) := by
    funext x
    simp only [weightedDifferenceSum_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      div_eq_mul_inv, mul_comm]
  rw [hstep]
  exact hs.symm

/-- The mixed term in the square expansion vanishes by the conditional-mean identity. -/
theorem integral_weighted_mul_difference_eq_zero (n : ℕ) :
    (∫ ω, weightedDifferenceSum D n ω * D n ω ∂μ) = 0 := by
  have hce := condExp_stronglyMeasurable_mul_of_bound (ℱ.le n)
    (weightedDifferenceSum_stronglyAdapted ℱ D hmeas n)
    (integrable_difference μ ℱ D hmeas hbound n) (n : ℝ)
    (ae_norm_weightedDifferenceSum_le μ D hbound n)
  have hz : μ[(fun ω ↦ weightedDifferenceSum D n ω * D n ω) | ℱ n] =ᵐ[μ] 0 := by
    filter_upwards [hce, hzero n] with ω hc hz
    change μ[weightedDifferenceSum D n * D n | ℱ n] ω = 0
    simpa only [Pi.mul_apply, hz, Pi.zero_apply, mul_zero] using hc
  rw [← integral_condExp (ℱ.le n)]
  exact (integral_congr_ae hz).trans (by simp)


omit hzero in
theorem integrable_weighted_mul_difference (n : ℕ) :
    Integrable (fun ω ↦ weightedDifferenceSum D n ω * D n ω) μ := by
  refine (integrable_const (n : ℝ)).mono'
    ((((weightedDifferenceSum_stronglyAdapted ℱ D hmeas n).mono (ℱ.le _)).mul
      ((hmeas n).mono (ℱ.le _))).aestronglyMeasurable) ?_
  filter_upwards [ae_norm_weightedDifferenceSum_le μ D hbound n, hbound n] with ω hw hd
  rw [norm_mul]
  simpa using mul_le_mul hw hd (norm_nonneg _) (Nat.cast_nonneg n)

theorem integral_weightedDifferenceSum_sq_succ_le (n : ℕ) :
    (∫ ω, (weightedDifferenceSum D (n + 1) ω) ^ 2 ∂μ) ≤
      (∫ ω, (weightedDifferenceSum D n ω) ^ 2 ∂μ) + 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have hi := integrable_weightedDifferenceSum_sq μ ℱ D hmeas hbound n
  have hc := integrable_weighted_mul_difference μ ℱ D hmeas hbound n
  have hd := integrable_difference_sq μ ℱ D hmeas hbound n
  have heq : (fun ω ↦ (weightedDifferenceSum D (n + 1) ω) ^ 2) =
      (fun ω ↦ (weightedDifferenceSum D n ω) ^ 2 +
        (2 / ((n + 1 : ℕ) : ℝ)) * (weightedDifferenceSum D n ω * D n ω) +
        (D n ω) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    funext ω
    rw [weightedDifferenceSum_succ]
    ring
  rw [heq, integral_add (f := fun ω ↦ (weightedDifferenceSum D n ω)^2 +
      (2 / ((n + 1 : ℕ) : ℝ)) * (weightedDifferenceSum D n ω * D n ω))
      (g := fun ω ↦ (D n ω)^2 / ((n + 1 : ℕ) : ℝ)^2)
      (hi.add (hc.const_mul _)) (hd.div_const _),
    integral_add (f := fun ω ↦ (weightedDifferenceSum D n ω)^2)
      (g := fun ω ↦ (2 / ((n + 1 : ℕ) : ℝ)) * (weightedDifferenceSum D n ω * D n ω))
      hi (hc.const_mul _), integral_const_mul, integral_div,
    integral_weighted_mul_difference_eq_zero μ ℱ D hmeas hbound hzero n,
    mul_zero, add_zero]
  have hdle : (∫ ω, (D n ω)^2 ∂μ) ≤ 1 := by
    calc
      (∫ ω, (D n ω) ^ 2 ∂μ) ≤ ∫ _, (1 : ℝ) ∂μ := by
        apply integral_mono_ae hd (integrable_const _)
        filter_upwards [hbound n] with ω h
        have := pow_le_pow_left₀ (norm_nonneg _) h 2
        simpa only [Real.norm_eq_abs, sq_abs, one_pow] using this
      _ = 1 := by simp
  have hdiv := div_le_div_of_nonneg_right hdle (sq_nonneg (((n + 1 : ℕ) : ℝ)))
  linarith

theorem integral_weightedDifferenceSum_sq_le (n : ℕ) :
    (∫ ω, (weightedDifferenceSum D n ω) ^ 2 ∂μ) ≤
      ∑ i ∈ Finset.range n, 1 / ((i + 1 : ℕ) : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hs := integral_weightedDifferenceSum_sq_succ_le μ ℱ D hmeas hbound hzero n
      linarith

/-- A bounded martingale-difference sequence obeys the strong law. Independence
is not required; the conditional mean uses the full preceding filtration. -/
theorem bounded_martingale_difference_strongLaw :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, D i ω)
      atTop (𝓝 0) := by
  have hsum : Summable (fun i : ℕ ↦ 1 / ((i + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  let C : ℝ := 1 + ∑' i : ℕ, 1 / ((i + 1 : ℕ) : ℝ) ^ 2
  have hnorm : ∀ n, (∫ ω, ‖weightedDifferenceSum D n ω‖ ∂μ) ≤ C := by
    intro n
    have hi := integrable_weightedDifferenceSum μ ℱ D hmeas hbound n
    have hs := integrable_weightedDifferenceSum_sq μ ℱ D hmeas hbound n
    calc
      (∫ ω, ‖weightedDifferenceSum D n ω‖ ∂μ) ≤
          ∫ ω, 1 + (weightedDifferenceSum D n ω) ^ 2 ∂μ := by
        apply integral_mono hi.norm ((integrable_const _).add hs)
        intro ω
        change ‖weightedDifferenceSum D n ω‖ ≤ 1 + (weightedDifferenceSum D n ω)^2
        rw [Real.norm_eq_abs]
        have := sq_nonneg (|weightedDifferenceSum D n ω| - 1)
        nlinarith [sq_abs (weightedDifferenceSum D n ω)]
      _ = 1 + ∫ ω, (weightedDifferenceSum D n ω) ^ 2 ∂μ := by
        rw [integral_add (integrable_const _) hs]
        simp
      _ ≤ 1 + ∑ i ∈ Finset.range n, 1 / ((i + 1 : ℕ) : ℝ) ^ 2 := by
        have hs := integral_weightedDifferenceSum_sq_le μ ℱ D hmeas hbound hzero n
        linarith
      _ ≤ C := by
        have hs := hsum.sum_le_tsum (Finset.range n) (fun _ _ ↦ by positivity)
        dsimp [C]
        linarith
  have hLp : ∀ n, eLpNorm (weightedDifferenceSum D n) 1 μ ≤ ENNReal.ofReal C := by
    intro n
    have hi := integrable_weightedDifferenceSum μ ℱ D hmeas hbound n
    rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hi]
    exact ENNReal.ofReal_le_ofReal (hnorm n)
  have ht := (weightedDifferenceSum_martingale μ ℱ D hmeas hbound hzero).submartingale.exists_ae_tendsto_of_bdd hLp
  filter_upwards [ht] with ω hω
  obtain ⟨L, hL⟩ := hω
  exact tendsto_average_of_weighted_tendsto D ω hL

end HeightPaper
