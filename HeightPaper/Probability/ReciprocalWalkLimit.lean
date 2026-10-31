module

public import HeightPaper.Probability.MartingaleStrongLaw
public import HeightPaper.Probability.UniformWalkDeviation
public import HeightPaper.Analysis.ReciprocalWalk
public import HeightPaper.Analysis.HarmonicScale
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Convergence of the centered harmonic martingale

Bounded, centered martingale differences give an actual measurable almost-sure
limit for their harmonic series. The second moment estimates are uniform in
the probability space and in the law of the differences.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal Classical

namespace HeightPaper

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The measurable martingale limit of harmonic weighted differences. -/
noncomputable def weightedDifferenceLimit (μ : Measure Ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (D : ℕ → Ω → ℝ) : Ω → ℝ :=
  ℱ.limitProcess (weightedDifferenceSum D) μ

omit [MeasurableSpace Ω] in
theorem weightedDifferenceSum_eq_sum (D : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    weightedDifferenceSum D n ω = ∑ k ∈ Finset.range n, D k ω / (k + 1 : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [weightedDifferenceSum_succ, Finset.sum_range_succ, ih]

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
  (D : ℕ → Ω → ℝ)
  (hmeas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (D n))
  (hbound : ∀ n, ∀ᵐ ω ∂μ, ‖D n ω‖ ≤ 1)
  (hzero : ∀ n, μ[D n | ℱ n] =ᵐ[μ] 0)

include hmeas hbound hzero

/-- The harmonic weighted martingale converges almost surely, before the
Kronecker step used in the existing strong-law theorem. -/
theorem ae_tendsto_weightedDifferenceSum :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ weightedDifferenceSum D n ω) atTop
      (𝓝 (weightedDifferenceLimit μ ℱ D ω)) := by
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
  exact (weightedDifferenceSum_martingale μ ℱ D hmeas hbound hzero).submartingale.ae_tendsto_limitProcess hLp

/-- The finite second moment bound uses a single summable numerical series. -/
theorem integral_weightedDifferenceSum_sq_le_tsum (n : ℕ) :
    (∫ ω, (weightedDifferenceSum D n ω) ^ 2 ∂μ) ≤
      ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
  have hs : Summable (fun k : ℕ ↦ 1 / ((k + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  exact (integral_weightedDifferenceSum_sq_le μ ℱ D hmeas hbound hzero n).trans
    (hs.sum_le_tsum (Finset.range n) (fun _ _ ↦ by positivity))

/-- Uniform L² norm bound for all harmonic partial sums. -/
theorem eLpNorm_weightedDifferenceSum_two_le (n : ℕ) :
    eLpNorm (weightedDifferenceSum D n) 2 μ ≤
      ENNReal.ofReal ((∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ)⁻¹) := by
  have hmem : MemLp (weightedDifferenceSum D n) 2 μ :=
    MemLp.of_bound
      ((weightedDifferenceSum_stronglyAdapted ℱ D hmeas n).mono (ℱ.le n)).aestronglyMeasurable
      n (ae_norm_weightedDifferenceSum_le μ D hbound n)
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow (integral_nonneg fun _ ↦ sq_nonneg _)
    (integral_weightedDifferenceSum_sq_le_tsum μ ℱ D hmeas hbound hzero n) (by positivity)

/-- The harmonic-series limit is an L² random variable. -/
theorem memLp_weightedDifferenceLimit_two : MemLp (weightedDifferenceLimit μ ℱ D) 2 μ := by
  exact (weightedDifferenceSum_martingale μ ℱ D hmeas hbound hzero).submartingale.memLp_limitProcess
    (eLpNorm_weightedDifferenceSum_two_le μ ℱ D hmeas hbound hzero)

/-- The same L² bound passes to the actual measurable limit. -/
theorem eLpNorm_weightedDifferenceLimit_two_le :
    eLpNorm (weightedDifferenceLimit μ ℱ D) 2 μ ≤
      ENNReal.ofReal ((∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ)⁻¹) := by
  apply (Lp.eLpNorm_lim_le_liminf_eLpNorm
    (fun n ↦ ((weightedDifferenceSum_stronglyAdapted ℱ D hmeas n).mono (ℱ.le n)).aestronglyMeasurable)
    (weightedDifferenceLimit μ ℱ D)
    (memLp_weightedDifferenceLimit_two μ ℱ D hmeas hbound hzero).aestronglyMeasurable
    (ae_tendsto_weightedDifferenceSum μ ℱ D hmeas hbound hzero)).trans
  simp_rw [liminf_eq, eventually_atTop]
  exact sSup_le fun b ⟨a, ha⟩ ↦ (ha a le_rfl).trans
    (eLpNorm_weightedDifferenceSum_two_le μ ℱ D hmeas hbound hzero a)

/-- Truncating the martingale differences gives the exact common L² tail
bound, without assuming independence or a stochastic remainder estimate. -/
theorem eLpNorm_weightedDifference_tail_two_le (N : ℕ) :
    eLpNorm (fun ω ↦ weightedDifferenceLimit μ ℱ D ω - weightedDifferenceSum D N ω) 2 μ ≤
      ENNReal.ofReal ((∑' k : ℕ, 1 / ((k + N + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ)⁻¹) := by
  let DN : ℕ → Ω → ℝ := fun k ω ↦ if N ≤ k then D k ω else 0
  let g : ℕ → ℝ := fun k ↦ if N ≤ k then 1 / ((k + 1 : ℕ) : ℝ) ^ 2 else 0
  have hm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (DN k) := by
    intro k
    by_cases hk : N ≤ k
    · simpa only [DN, ite_eq_left hk] using hmeas k
    · simpa only [DN, ite_eq_right hk] using (stronglyMeasurable_const (b := (0 : ℝ)))
  have hb : ∀ k, ∀ᵐ ω ∂μ, ‖DN k ω‖ ≤ 1 := by
    intro k
    by_cases hk : N ≤ k
    · simpa only [DN, ite_eq_left hk] using hbound k
    · simp [DN, hk]
  have hz : ∀ k, μ[DN k | ℱ k] =ᵐ[μ] 0 := by
    intro k
    by_cases hk : N ≤ k
    · simpa only [DN, ite_eq_left hk] using hzero k
    · simp only [DN, ite_eq_right hk]
      change μ[(0 : Ω → ℝ) | ℱ k] =ᵐ[μ] 0
      rw [condExp_zero]
  have hg0 (k : ℕ) : 0 ≤ g k := by dsimp only [g]; split <;> positivity
  have hsum : Summable (fun k : ℕ ↦ 1 / ((k + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  have hg : Summable g := by
    apply hsum.of_norm_bounded
    intro k
    by_cases hk : N ≤ k
    · simp only [g, ite_eq_left hk, Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ 2)]
      exact le_rfl
    · simp only [g, ite_eq_right hk, norm_zero]
      positivity
  have hgt : (∑' k, g k) = ∑' k : ℕ, 1 / ((k + N + 1 : ℕ) : ℝ) ^ 2 := by
    rw [← hg.sum_add_tsum_nat_add N]
    have hp : ∑ k ∈ Finset.range N, g k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact ite_eq_right (Nat.not_le.mpr (Finset.mem_range.mp hk))
    rw [hp, zero_add]
    apply tsum_congr
    intro k
    exact ite_eq_left (by omega : N ≤ k + N)
  have hsq : ∀ n, (∫ ω, (weightedDifferenceSum DN n ω) ^ 2 ∂μ) ≤
      ∑ k ∈ Finset.range n, g k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        by_cases hn : N ≤ n
        · simpa only [g, ite_eq_left hn] using
            (integral_weightedDifferenceSum_sq_succ_le μ ℱ DN hm hb hz n).trans
              (add_le_add ih le_rfl)
        · have he : weightedDifferenceSum DN (n + 1) = weightedDifferenceSum DN n := by
            funext ω
            simp only [weightedDifferenceSum_succ, DN, ite_eq_right hn, zero_div, add_zero]
          rw [he]
          simpa only [g, ite_eq_right hn, add_zero] using ih
  have hLp : ∀ n, eLpNorm (weightedDifferenceSum DN n) 2 μ ≤
      ENNReal.ofReal ((∑' k : ℕ, 1 / ((k + N + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ)⁻¹) := by
    intro n
    have hmem : MemLp (weightedDifferenceSum DN n) 2 μ := MemLp.of_bound
      ((weightedDifferenceSum_stronglyAdapted ℱ DN hm n).mono (ℱ.le n)).aestronglyMeasurable
      n (ae_norm_weightedDifferenceSum_le μ DN hb n)
    rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow (integral_nonneg fun _ ↦ sq_nonneg _) _ (by positivity)
    rw [← hgt]
    exact (hsq n).trans (hg.sum_le_tsum (Finset.range n) (fun k _ ↦ hg0 k))
  have heq (n : ℕ) (hn : N ≤ n) (ω : Ω) :
      weightedDifferenceSum DN n ω = weightedDifferenceSum D n ω - weightedDifferenceSum D N ω := by
    simp only [weightedDifferenceSum_eq_sum, DN, ite_div, zero_div]
    rw [← Finset.sum_filter]
    have hf : (Finset.range n).filter (fun k ↦ N ≤ k) = Finset.Ico N n := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hf, Finset.sum_Ico_eq_sub _ hn]
  have hc : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ weightedDifferenceSum DN n ω) atTop
      (𝓝 (weightedDifferenceLimit μ ℱ D ω - weightedDifferenceSum D N ω)) := by
    filter_upwards [ae_tendsto_weightedDifferenceSum μ ℱ D hmeas hbound hzero] with ω hω
    apply (hω.sub_const (weightedDifferenceSum D N ω)).congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (heq n hn ω).symm
  have hlimm : AEStronglyMeasurable
      (fun ω ↦ weightedDifferenceLimit μ ℱ D ω - weightedDifferenceSum D N ω) μ :=
    (memLp_weightedDifferenceLimit_two μ ℱ D hmeas hbound hzero).aestronglyMeasurable.sub
      ((weightedDifferenceSum_stronglyAdapted ℱ D hmeas N).mono (ℱ.le N)).aestronglyMeasurable
  apply (Lp.eLpNorm_lim_le_liminf_eLpNorm
    (fun n ↦ ((weightedDifferenceSum_stronglyAdapted ℱ DN hm n).mono (ℱ.le n)).aestronglyMeasurable)
    _ hlimm hc).trans
  simp_rw [liminf_eq, eventually_atTop]
  exact sSup_le fun b ⟨a, ha⟩ ↦ (ha a le_rfl).trans (hLp a)

/-- A common bound for the first moments of all weighted partial sums. -/
theorem integral_norm_weightedDifferenceSum_le (n : ℕ) :
    (∫ ω, ‖weightedDifferenceSum D n ω‖ ∂μ) ≤
      1 + ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
  have hi := integrable_weightedDifferenceSum μ ℱ D hmeas hbound n
  have hs := integrable_weightedDifferenceSum_sq μ ℱ D hmeas hbound n
  calc
    (∫ ω, ‖weightedDifferenceSum D n ω‖ ∂μ) ≤
        ∫ ω, 1 + (weightedDifferenceSum D n ω) ^ 2 ∂μ := by
      apply integral_mono hi.norm ((integrable_const _).add hs)
      intro ω
      change ‖weightedDifferenceSum D n ω‖ ≤ 1 + (weightedDifferenceSum D n ω) ^ 2
      rw [Real.norm_eq_abs]
      nlinarith [sq_nonneg (|weightedDifferenceSum D n ω| - 1),
        sq_abs (weightedDifferenceSum D n ω)]
    _ = 1 + ∫ ω, (weightedDifferenceSum D n ω) ^ 2 ∂μ := by
      rw [integral_add (integrable_const _) hs]
      simp
    _ ≤ _ := add_le_add le_rfl (integral_weightedDifferenceSum_sq_le_tsum μ ℱ D hmeas hbound hzero n)

/-- Doob's inequality controls the supremum over every finite horizon,
with a numerical constant independent of the law of the bounded differences. -/
theorem weightedDifferenceSum_maximal_measure_le {A : ℝ} (hA : 0 < A) :
    μ.real {ω | ∃ n, A ≤ |weightedDifferenceSum D n ω|} ≤
      (1 + ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) / A := by
  let C : ℝ := 1 + ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let f : ℕ → Ω → ℝ := fun n ω ↦ ‖weightedDifferenceSum D n ω‖
  have hmart := weightedDifferenceSum_martingale μ ℱ D hmeas hbound hzero
  have hsub : Submartingale f ℱ μ := by
    apply submartingale_nat
      (fun n ↦ (weightedDifferenceSum_stronglyAdapted ℱ D hmeas n).norm)
      (fun n ↦ (integrable_weightedDifferenceSum μ ℱ D hmeas hbound n).norm)
    intro n
    filter_upwards [norm_condExp_le (μ := μ) (m := ℱ n) (weightedDifferenceSum D (n + 1)),
      hmart.condExp_ae_eq (Nat.le_succ n)] with ω hn he
    simpa only [he] using hn
  let E : ℕ → Set Ω := fun n ↦ {ω | ∃ k ≤ n, A ≤ ‖weightedDifferenceSum D k ω‖}
  have hfinite (n : ℕ) : μ (E n) ≤ ENNReal.ofReal (C / A) := by
    let a : ℝ≥0 := ⟨A, hA.le⟩
    have hmax := maximal_ineq hsub (fun n ω ↦ norm_nonneg _) (ε := a) n
    have he : {ω | (a : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ f k ω)} = E n := by
      ext ω
      simp only [Finset.le_sup'_iff, Finset.mem_range, E, Set.mem_ofPred_eq, f, a]
      constructor <;> rintro ⟨k, hk, hbound⟩ <;> exact ⟨k, by omega, hbound⟩
    rw [he] at hmax
    have hi : (∫ ω in E n, f n ω ∂μ) ≤ C :=
      (setIntegral_le_integral (integrable_weightedDifferenceSum μ ℱ D hmeas hbound n).norm
        (Eventually.of_forall (fun ω ↦ norm_nonneg (weightedDifferenceSum D n ω)))).trans
          (integral_norm_weightedDifferenceSum_le μ ℱ D hmeas hbound hzero n)
    have hh := hmax.trans (ENNReal.ofReal_le_ofReal hi)
    rw [ENNReal.ofReal_div_of_pos hA]
    apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hA).ne')
      (Or.inl ENNReal.ofReal_ne_top)).mpr
    have ha : (a : ℝ≥0∞) = ENNReal.ofReal A := (ENNReal.ofReal_eq_coe_nnreal hA.le).symm
    rw [ha] at hh
    simpa only [mul_comm] using hh
  have hmono : Monotone E := by
    intro n m hnm ω hω
    obtain ⟨k, hk, hb⟩ := hω
    exact ⟨k, hk.trans hnm, hb⟩
  have he : {ω | ∃ n, A ≤ |weightedDifferenceSum D n ω|} = ⋃ n, E n := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, E, Real.norm_eq_abs]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, n, le_rfl, hn⟩
    · rintro ⟨n, k, _, hk⟩
      exact ⟨k, hk⟩
  have hh : μ {ω | ∃ n, A ≤ |weightedDifferenceSum D n ω|} ≤ ENNReal.ofReal (C / A) := by
    rw [he, hmono.measure_iUnion]
    exact iSup_le hfinite
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  simpa only [Measure.real, ENNReal.toReal_ofReal (div_nonneg hC hA.le), C] using hr

end HeightPaper

namespace HeightPaper

variable {Ω : Type*} [MeasurableSpace Ω]


/-- A common vanishing L² bound gives convergence in probability uniformly
over an arbitrary parameter set. The parameters do not carry a measure. -/
theorem uniform_measureReal_abs_lt_of_eLpNorm_bound
    {Λ : Type*} (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : ℕ → Λ → Ω → ℝ) (b : ℕ → ℝ≥0∞)
    (hb : Tendsto b atTop (𝓝 0))
    (hF : ∀ n a, eLpNorm (F n a) 2 μ ≤ b n)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a, μ.real {ω | ε ≤ |F n a ω|} < η := by
  let ℓ : Filter (ℕ × Λ) := Filter.comap Prod.fst atTop
  have hnum : Tendsto (fun q : ℕ × Λ ↦ b q.1) ℓ (𝓝 0) := hb.comp tendsto_comap
  have hnorm : Tendsto (fun q : ℕ × Λ ↦ eLpNorm (F q.1 q.2) 2 μ) ℓ (𝓝 0) :=
    by
      rw [ENNReal.tendsto_nhds_zero] at hnum ⊢
      intro δ hδ
      exact (hnum δ hδ).mono (fun q hq ↦ (hF q.1 q.2).trans hq)
  have hm : TendstoInMeasure μ (fun q : ℕ × Λ ↦ F q.1 q.2) ℓ (fun _ ↦ (0 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    simpa only [Pi.sub_def, sub_zero] using hnorm
  have he := ((tendstoInMeasure_iff_measureReal_norm.mp hm) ε hε).eventually (Iio_mem_nhds hη)
  have he' : ∀ᶠ n : ℕ in atTop, ∀ a, μ.real {ω | ε ≤ |F n a ω|} < η := by
    rw [eventually_comap] at he
    filter_upwards [he] with n hn
    intro a
    simpa only [sub_zero, Real.norm_eq_abs] using hn (n, a) rfl
  exact eventually_atTop.mp he'

/-- The information available strictly before draw `n`. -/
def independentPastFiltration (D : ℕ → Ω → ℝ) (hmeas : ∀ n, StronglyMeasurable (D n)) :
    Filtration ℕ ‹MeasurableSpace Ω› where
  seq n := ⨆ k < n, MeasurableSpace.comap (D k) inferInstance
  mono' _ _ hij := biSup_mono fun _ hk ↦ hk.trans_le hij
  le' n := by
    refine iSup₂_le ?_
    intro k _
    exact (hmeas k).measurable.comap_le

theorem stronglyMeasurable_independentPastFiltration (D : ℕ → Ω → ℝ)
    (hmeas : ∀ n, StronglyMeasurable (D n)) (n : ℕ) :
    StronglyMeasurable[independentPastFiltration D hmeas (n + 1)] (D n) := by
  exact (comap_measurable (D n)).stronglyMeasurable.mono
    (le_iSup_of_le n (le_iSup_of_le (Nat.lt_succ_self n) le_rfl))

theorem condExp_independentPastFiltration_eq_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hmeas : ∀ n, StronglyMeasurable (D n))
    (hindep : iIndepFun D μ) (hmean : ∀ n, (∫ ω, D n ω ∂μ) = 0) (n : ℕ) :
    μ[D n | independentPastFiltration D hmeas n] =ᵐ[μ] 0 := by
  have hi : Indep (MeasurableSpace.comap (D n) inferInstance)
      (independentPastFiltration D hmeas n) μ := by
    have hh := indep_iSup_of_disjoint (fun k ↦ (hmeas k).measurable.comap_le) hindep
      (show Disjoint ({n} : Set ℕ) {k | k < n} by simp)
    simpa only [iSup_singleton, independentPastFiltration, Set.mem_ofPred_eq] using hh
  have hc := condExp_indep_eq (hmeas n).measurable.comap_le
    ((independentPastFiltration D hmeas).le n) (comap_measurable (D n)).stronglyMeasurable hi
  simpa only [hmean n, Pi.zero_def] using hc

/-- A genuine convergence theorem for independent centered bounded draws.
Its hypotheses refer to the actual joint law, with no limit assumption. -/
theorem independent_bounded_harmonic_convergence (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hmeas : ∀ n, StronglyMeasurable (D n))
    (hindep : iIndepFun D μ) (hmean : ∀ n, (∫ ω, D n ω ∂μ) = 0)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, ‖D n ω‖ ≤ 1) :
    ∃ Z : Ω → ℝ, MemLp Z 2 μ ∧
      eLpNorm Z 2 μ ≤ ENNReal.ofReal
        ((∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ)⁻¹) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∑ k ∈ Finset.range n, D k ω / (k + 1 : ℕ))
        atTop (𝓝 (Z ω)) := by
  let ℱ := independentPastFiltration D hmeas
  have hm := stronglyMeasurable_independentPastFiltration D hmeas
  have hz := condExp_independentPastFiltration_eq_zero μ D hmeas hindep hmean
  refine ⟨weightedDifferenceLimit μ ℱ D,
    memLp_weightedDifferenceLimit_two μ ℱ D hm hbound hz,
    eLpNorm_weightedDifferenceLimit_two_le μ ℱ D hm hbound hz, ?_⟩
  simpa only [weightedDifferenceSum_eq_sum] using
    ae_tendsto_weightedDifferenceSum μ ℱ D hm hbound hz

end HeightPaper

namespace HeightPaper.CountCoupling

/-- The centered Bernoulli birth variable on the common uniform probability space. -/
noncomputable def centeredLocalBirth (l : ℝ) (k : ℕ) (u : ℕ → ℝ) : ℝ :=
  (if localBirth l u k then 1 else 0) - birthThreshold l

theorem measurable_centeredLocalBirth (l : ℝ) (k : ℕ) : Measurable (centeredLocalBirth l k) :=
  (measurable_of_countable (fun b : Bool ↦ (if b then (1 : ℝ) else 0) - birthThreshold l)).comp
    (measurable_localBirth l k)

theorem centeredLocalBirth_independent (l : ℝ) : iIndepFun (centeredLocalBirth l) uniformLaw :=
  (localBirth_independent l).comp
    (fun _ b ↦ (if b then (1 : ℝ) else 0) - birthThreshold l)
    (fun _ ↦ measurable_of_countable _)

theorem norm_centeredLocalBirth_le_one {l : ℝ} (hl : 0 ≤ l) (k : ℕ) (u : ℕ → ℝ) :
    ‖centeredLocalBirth l k u‖ ≤ 1 := by
  have hp0 := birthThreshold_nonneg hl
  have hp1 := birthThreshold_le_one hl
  rw [Real.norm_eq_abs, abs_le]
  unfold centeredLocalBirth
  split <;> constructor <;> linarith

theorem integral_centeredLocalBirth {l : ℝ} (hl : 0 ≤ l) (k : ℕ) :
    (∫ u, centeredLocalBirth l k u ∂uniformLaw) = 0 := by
  let A : Set (ℕ → ℝ) := {u | localBirth l u k = true}
  have hA : MeasurableSet A := (measurable_localBirth l k) (measurableSet_singleton true)
  have heq : centeredLocalBirth l k = fun u ↦ A.indicator (fun _ ↦ (1 : ℝ)) u - birthThreshold l := by
    funext u
    simp only [centeredLocalBirth, A, Set.indicator, Set.mem_ofPred_eq]
  rw [heq, integral_sub ((integrable_const (1 : ℝ)).indicator hA) (integrable_const _),
    integral_indicator_const _ hA]
  simp only [smul_eq_mul, mul_one, integral_const, probReal_univ, one_mul]
  rw [Measure.real, localBirth_probability hl k, ENNReal.toReal_ofReal (birthThreshold_nonneg hl)]
  exact sub_self _

/-- The actual iid birth draws have a convergent harmonic centered series.
The first source event is draw `0`, with denominator `1`. -/
theorem localBirth_harmonic_convergence {l : ℝ} (hl : 0 ≤ l) :
    ∃ Z : (ℕ → ℝ) → ℝ, MemLp Z 2 uniformLaw ∧
      eLpNorm Z 2 uniformLaw ≤ ENNReal.ofReal
        ((∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ)⁻¹) ∧
      ∀ᵐ u ∂uniformLaw, Tendsto (fun n ↦ ∑ k ∈ Finset.range n,
        centeredLocalBirth l k u / (k + 1 : ℕ)) atTop (𝓝 (Z u)) :=
  independent_bounded_harmonic_convergence uniformLaw (centeredLocalBirth l)
    (fun k ↦ (measurable_centeredLocalBirth l k).stronglyMeasurable)
    (centeredLocalBirth_independent l) (integral_centeredLocalBirth hl)
    (fun k ↦ Eventually.of_forall (norm_centeredLocalBirth_le_one hl k))

/-- The centered harmonic birth series with exactly the source coefficient
`γ = λ / (λ - 1)` and drift `(λ - 1) / (1 + λ)`. -/
theorem sourceBirth_harmonic_convergence {l : ℝ} (hl : 1 < l) :
    ∃ Z' : (ℕ → ℝ) → ℝ, MemLp Z' 2 uniformLaw ∧
      eLpNorm Z' 2 uniformLaw ≤ ‖(localDrift l)⁻¹‖ₑ * ENNReal.ofReal
        ((∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ)⁻¹) ∧
      ∀ᵐ u ∂uniformLaw, Tendsto (fun n ↦ ∑ k ∈ Finset.range n,
        ((if localBirth l u k then (1 : ℝ) else 0) / localDrift l - l / (l - 1)) /
          (k + 1 : ℕ)) atTop (𝓝 (Z' u)) := by
  obtain ⟨Z, hZ, hnorm, hlim⟩ := localBirth_harmonic_convergence (zero_le_one.trans hl.le)
  refine ⟨fun u ↦ Z u / localDrift l, ?_, ?_, ?_⟩
  · simpa only [div_eq_mul_inv] using hZ.mul_const (localDrift l)⁻¹
  · have hnorm' := (eLpNorm_const_smul_le (c := (localDrift l)⁻¹)
      (f := Z) (p := 2) (μ := uniformLaw)).trans (mul_le_mul le_rfl hnorm zero_le zero_le)
    change eLpNorm (fun u ↦ (localDrift l)⁻¹ * Z u) 2 uniformLaw ≤ _ at hnorm'
    simpa only [div_eq_mul_inv, mul_comm] using hnorm'
  · have hγ : birthThreshold l / localDrift l = l / (l - 1) := by
      unfold birthThreshold localDrift
      have hplus : 1 + l ≠ 0 := by linarith
      have hminus : l - 1 ≠ 0 := by linarith
      field_simp
    filter_upwards [hlim] with u hu
    apply (hu.div_const (localDrift l)).congr
    intro n
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [← hγ]
    unfold centeredLocalBirth
    ring

/-- The inverse drift is bounded by the same constant over a supercritical
half-line; this makes the preceding L² estimate uniform in the parameter. -/
theorem localDrift_inv_uniform_le {l₀ l : ℝ} (hl₀ : 1 < l₀) (hl : l₀ ≤ l) :
    ‖(localDrift l)⁻¹‖ₑ ≤ ENNReal.ofReal ((localDrift l₀)⁻¹) := by
  have hd₀ := localDrift_pos hl₀
  have hd := localDrift_pos (hl₀.trans_le hl)
  have hm : localDrift l₀ ≤ localDrift l := by
    unfold localDrift
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 1 + l₀)
      (by linarith : (0 : ℝ) < 1 + l)]
    nlinarith
  rw [Real.enorm_eq_ofReal (inv_nonneg.mpr hd.le)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [one_div] using one_div_le_one_div_of_le hd₀ hm

/-- A single L² bound applies to the centered birth limits for every parameter
above a fixed supercritical lower endpoint. -/
theorem sourceBirth_harmonic_convergence_uniform_l2 {l₀ : ℝ} (hl₀ : 1 < l₀)
    (l : ℝ) (hl : l₀ ≤ l) :
    ∃ Z' : (ℕ → ℝ) → ℝ, MemLp Z' 2 uniformLaw ∧
      eLpNorm Z' 2 uniformLaw ≤ ENNReal.ofReal ((localDrift l₀)⁻¹) * ENNReal.ofReal
        ((∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ)⁻¹) ∧
      ∀ᵐ u ∂uniformLaw, Tendsto (fun n ↦ ∑ k ∈ Finset.range n,
        ((if localBirth l u k then (1 : ℝ) else 0) / localDrift l - l / (l - 1)) /
          (k + 1 : ℕ)) atTop (𝓝 (Z' u)) := by
  obtain ⟨Z', hm, hb, ht⟩ := sourceBirth_harmonic_convergence (hl₀.trans_le hl)
  exact ⟨Z', hm, hb.trans (mul_le_mul (localDrift_inv_uniform_le hl₀ hl) le_rfl zero_le zero_le), ht⟩


/-- Exact centered Bernoulli harmonic sum occurring in the source. -/
noncomputable def sourceBirthCenteredSum (l : ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    ((if localBirth l u k then (1 : ℝ) else 0) / localDrift l - l / (l - 1)) /
      (k + 1 : ℕ)

theorem sourceBirthCenteredSum_eq {l : ℝ} (hl : 1 < l) (u : ℕ → ℝ) (n : ℕ) :
    sourceBirthCenteredSum l u n = weightedDifferenceSum (centeredLocalBirth l) n u / localDrift l := by
  have hγ : birthThreshold l / localDrift l = l / (l - 1) := by
    unfold birthThreshold localDrift
    have hplus : 1 + l ≠ 0 := by linarith
    have hminus : l - 1 ≠ 0 := by linarith
    field_simp
  unfold sourceBirthCenteredSum
  rw [weightedDifferenceSum_eq_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [← hγ]
  unfold centeredLocalBirth
  ring

theorem centeredLocalBirth_maximal_measure_le {l : ℝ} (hl : 0 ≤ l) {B : ℝ} (hB : 0 < B) :
    uniformLaw.real {u | ∃ n, B ≤ |weightedDifferenceSum (centeredLocalBirth l) n u|} ≤
      (1 + ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) / B := by
  let D := centeredLocalBirth l
  have hm : ∀ n, StronglyMeasurable (D n) := fun n ↦
    (measurable_centeredLocalBirth l n).stronglyMeasurable
  let ℱ := independentPastFiltration D hm
  exact weightedDifferenceSum_maximal_measure_le uniformLaw ℱ D
    (stronglyMeasurable_independentPastFiltration D hm)
    (fun k ↦ Eventually.of_forall (norm_centeredLocalBirth_le_one hl k))
    (condExp_independentPastFiltration_eq_zero uniformLaw D hm
      (centeredLocalBirth_independent l) (integral_centeredLocalBirth hl)) hB

/-- The whole sequence of centered birth partial sums is tight uniformly
over a supercritical half-line, by Doob's maximal inequality. -/
theorem sourceBirthCenteredSum_uniform_tight {l₀ : ℝ} (hl₀ : 1 < l₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ l ≥ l₀,
      uniformLaw.real {u | ∃ n, A < |sourceBirthCenteredSum l u n|} ≤ ε := by
  let C : ℝ := 1 + ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let B : ℝ := (C + 1) / ε
  have hB : 0 < B := div_pos (by linarith) hε
  have hd₀ := localDrift_pos hl₀
  refine ⟨(localDrift l₀)⁻¹ * B, by positivity, ?_⟩
  intro l hl
  have hl1 := hl₀.trans_le hl
  have hd := localDrift_pos hl1
  have hinv : (localDrift l)⁻¹ ≤ (localDrift l₀)⁻¹ := by
    have hh := localDrift_inv_uniform_le hl₀ hl
    rw [Real.enorm_eq_ofReal (inv_nonneg.mpr hd.le)] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (inv_nonneg.mpr hd₀.le)).mp hh
  have hsub : {u | ∃ n, (localDrift l₀)⁻¹ * B < |sourceBirthCenteredSum l u n|} ⊆
      {u | ∃ n, B ≤ |weightedDifferenceSum (centeredLocalBirth l) n u|} := by
    intro u hu
    obtain ⟨n, hn⟩ := hu
    refine ⟨n, ?_⟩
    by_contra hb
    have hb' := (lt_of_not_ge hb).le
    have hh : |sourceBirthCenteredSum l u n| ≤ (localDrift l₀)⁻¹ * B := by
      rw [sourceBirthCenteredSum_eq hl1, abs_div, abs_of_pos hd, div_eq_mul_inv]
      exact (mul_le_mul hb' hinv (inv_nonneg.mpr hd.le) hB.le).trans_eq (mul_comm _ _)
    exact not_lt_of_ge hh hn
  apply (measureReal_mono (h₂ := measure_ne_top _ _) hsub).trans
  apply (centeredLocalBirth_maximal_measure_le (zero_le_one.trans hl1.le) hB).trans
  change C / B ≤ ε
  apply (div_le_iff₀ hB).mpr
  dsimp only [B]
  rw [mul_comm ε _, div_mul_cancel₀ _ hε.ne']
  linarith


/-- Pathwise bound up to a finite surviving horizon. Infinite survival is
not assumed, which is essential for transferring the bound to the epidemic. -/
theorem localCenteredReciprocal_bound {l M Y B : ℝ} (hl : 1 < l)
    (hM : 0 ≤ M) (hY : 0 ≤ Y) (u : ℕ → ℝ) (n : ℕ)
    (hsurv : ∀ i ≤ n, 0 < (localWalk l u i : ℝ))
    (hratio : ∀ k, positiveReciprocal l u k ≤ M)
    (hdev : ∀ k ≥ 1, |(localWalk l u k : ℝ) - k * localDrift l| ≤
      Y * (k : ℝ) ^ (3 / 4 : ℝ))
    (hcenter : |sourceBirthCenteredSum l u n| ≤ B) :
    |(∑ k ∈ Finset.range n,
        (if localBirth l u k then (1 : ℝ) else 0) / (localWalk l u (k + 1) : ℝ)) -
      l / (l - 1) * Real.log n| ≤
      (localDrift l)⁻¹ * M * Y *
        (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) + B + l / (l - 1) := by
  let S : ℕ → ℝ := fun k ↦ (localWalk l u k : ℝ)
  let w : ℕ → ℝ := fun i ↦ if localBirth l u (i - 1) then 1 else 0
  let C : ℝ := (localDrift l)⁻¹ * M * Y
  have hd := localDrift_pos hl
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (inv_nonneg.mpr hd.le) hM) hY
  have herr : |∑ k ∈ Finset.range n, reciprocalWalkError S (localDrift l) k * w (k + 1)| ≤
      C * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, |reciprocalWalkError S (localDrift l) k * w (k + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, C * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkn := Finset.mem_range.mp hk
        have hs : 0 < S (k + 1) := hsurv (k + 1) (by omega)
        have hsInt : 0 < localWalk l u (k + 1) := by
          have hh : (0 : ℝ) < (localWalk l u (k + 1) : ℝ) := hs
          exact_mod_cast hh
        have hr : ((k + 1 : ℕ) : ℝ) / S (k + 1) ≤ M := by
          simpa only [positiveReciprocal, ite_eq_left hsInt] using hratio (k + 1)
        have hy : |S (k + 1) - localDrift l * (k + 1 : ℕ)| ≤
            Y * ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
          simpa only [S, mul_comm] using hdev (k + 1) (by omega)
        have hw : |w (k + 1)| ≤ 1 := by dsimp only [w]; split <;> norm_num
        rw [abs_mul]
        apply (mul_le_of_le_one_right (abs_nonneg _) hw).trans
        exact abs_reciprocal_sub_linear_le hs hd (by positivity) hM hr hy
      _ = C * ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (summable_reciprocalWalk_envelope.sum_le_tsum (Finset.range n)
          (fun k _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)) hC
  have hb : |∑ k ∈ Finset.range n,
      (w (k + 1) / localDrift l - l / (l - 1)) / (k + 1 : ℕ)| ≤ B := by
    simpa only [sourceBirthCenteredSum, w, Nat.add_sub_cancel] using hcenter
  have hγ : 0 ≤ l / (l - 1) := div_nonneg (zero_le_one.trans hl.le) (sub_nonneg.mpr hl.le)
  have hH : |l / (l - 1) * ((harmonic n : ℝ) - Real.log n)| ≤ l / (l - 1) := by
    rw [abs_mul, abs_of_nonneg hγ, abs_of_nonneg (harmonic_sub_log_bounds n).1]
    exact mul_le_of_le_one_right hγ (harmonic_sub_log_bounds n).2
  have ht : |(∑ k ∈ Finset.range n, w (k + 1) / S (k + 1)) -
      l / (l - 1) * Real.log n| ≤ C *
        (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) + B + l / (l - 1) := by
    rw [sum_weighted_reciprocal_centered_eq S w (localDrift l) (l / (l - 1)) n]
    exact (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans
      (add_le_add (add_le_add herr hb) hH))
  simpa only [S, w, Nat.add_sub_cancel, C] using ht

/-- The centered reciprocal birth sum remains uniformly tight over all finite
surviving horizons and all parameters above a supercritical lower endpoint. -/
theorem localCenteredReciprocal_uniform_tight {l₀ : ℝ} (hl₀ : 1 < l₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ l ≥ l₀,
      uniformLaw.real {u | ∃ n : ℕ,
        (∀ i ≤ n, 0 < (localWalk l u i : ℝ)) ∧
        A < |(∑ k ∈ Finset.range n,
          (if localBirth l u k then (1 : ℝ) else 0) / (localWalk l u (k + 1) : ℝ)) -
          l / (l - 1) * Real.log n|} ≤ ε := by
  have hsmall : 0 < ε / 3 := by positivity
  obtain ⟨M, hM, hMtight⟩ := positiveReciprocal_uniform_tight hl₀ hsmall
  obtain ⟨Y, hY, hYtight⟩ := localWalk_power_deviation_uniform_tight hsmall
  obtain ⟨B, hB, hBtight⟩ := sourceBirthCenteredSum_uniform_tight hl₀ hsmall
  let Zeta : ℝ := ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)
  have hZeta : 0 ≤ Zeta := tsum_nonneg (fun k ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hd₀ := localDrift_pos hl₀
  let A : ℝ := (localDrift l₀)⁻¹ * M * Y * Zeta + B + (localDrift l₀)⁻¹
  refine ⟨A, by dsimp only [A]; positivity, ?_⟩
  intro l hl
  have hl1 := hl₀.trans_le hl
  have hd := localDrift_pos hl1
  have hinv : (localDrift l)⁻¹ ≤ (localDrift l₀)⁻¹ := by
    have hh := localDrift_inv_uniform_le hl₀ hl
    rw [Real.enorm_eq_ofReal (inv_nonneg.mpr hd.le)] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (inv_nonneg.mpr hd₀.le)).mp hh
  have hγ : l / (l - 1) ≤ (localDrift l₀)⁻¹ := by
    have hγeq : birthThreshold l / localDrift l = l / (l - 1) := by
      unfold birthThreshold localDrift
      have hplus : 1 + l ≠ 0 := by linarith
      have hminus : l - 1 ≠ 0 := by linarith
      field_simp
    rw [← hγeq]
    exact (div_le_div_of_nonneg_right (birthThreshold_le_one (zero_le_one.trans hl1.le)) hd.le).trans
      (by simpa only [one_div] using hinv)
  let F₁ : Set (ℕ → ℝ) := {u | ∃ k, M < positiveReciprocal l u k}
  let F₂ : Set (ℕ → ℝ) := {u | ∃ (k : ℕ), 1 ≤ k ∧
    Y * (k : ℝ) ^ (3 / 4 : ℝ) < |(localWalk l u k : ℝ) - k * localDrift l|}
  let F₃ : Set (ℕ → ℝ) := {u | ∃ n, B < |sourceBirthCenteredSum l u n|}
  have hsub : {u | ∃ n : ℕ, (∀ i ≤ n, 0 < (localWalk l u i : ℝ)) ∧
      A < |(∑ k ∈ Finset.range n,
        (if localBirth l u k then (1 : ℝ) else 0) / (localWalk l u (k + 1) : ℝ)) -
        l / (l - 1) * Real.log n|} ⊆ F₁ ∪ F₂ ∪ F₃ := by
    intro u hu
    by_cases h₁ : u ∈ F₁
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : u ∈ F₂
    · exact Or.inl (Or.inr h₂)
    by_cases h₃ : u ∈ F₃
    · exact Or.inr h₃
    obtain ⟨n, hs, hn⟩ := hu
    have hr : ∀ k, positiveReciprocal l u k ≤ M := by
      intro k
      exact le_of_not_gt (fun hk ↦ h₁ ⟨k, hk⟩)
    have hy : ∀ k ≥ 1, |(localWalk l u k : ℝ) - k * localDrift l| ≤
        Y * (k : ℝ) ^ (3 / 4 : ℝ) := by
      intro k hk
      exact le_of_not_gt (fun hh ↦ h₂ ⟨k, hk, hh⟩)
    have hb : |sourceBirthCenteredSum l u n| ≤ B :=
      le_of_not_gt (fun hh ↦ h₃ ⟨n, hh⟩)
    have hpath := localCenteredReciprocal_bound hl1 hM hY.le u n hs hr hy hb
    have hcoeff : (localDrift l)⁻¹ * M * Y * Zeta ≤
        (localDrift l₀)⁻¹ * M * Y * Zeta :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinv hM) hY.le) hZeta
    have hupper : (localDrift l)⁻¹ * M * Y * Zeta + B + l / (l - 1) ≤ A :=
      add_le_add (add_le_add hcoeff le_rfl) hγ
    exact False.elim (not_lt_of_ge (hpath.trans hupper) hn)
  apply (measureReal_mono (h₂ := measure_ne_top _ _) hsub).trans
  have hbound : uniformLaw.real (F₁ ∪ F₂ ∪ F₃) ≤
      uniformLaw.real F₁ + uniformLaw.real F₂ + uniformLaw.real F₃ :=
    (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
  apply hbound.trans
  have h₁ := hMtight l hl
  have h₂ := hYtight l (zero_le_one.trans hl1.le)
  have h₃ := hBtight l hl
  linarith

/-- The source's `Z''`: the absolutely convergent reciprocal error on infinite
survival, and zero elsewhere. Draw zero supplies the birth at walk time one. -/
noncomputable def localBirthReciprocalCorrection (l : ℝ) (u : ℕ → ℝ) : ℝ :=
  survivalReciprocalCorrection (fun k ↦ (localWalk l u k : ℝ))
    (fun i ↦ if localBirth l u (i - 1) then 1 else 0) (localDrift l)

theorem measurable_localBirthReciprocalCorrection (l : ℝ) :
    Measurable (localBirthReciprocalCorrection l) := by
  have hsurv : MeasurableSet {u : ℕ → ℝ | ∀ i, 0 < (localWalk l u i : ℝ)} := by
    have hh := MeasurableSet.iInter (fun i ↦
      measurableSet_lt (measurable_const : Measurable (fun _ : ℕ → ℝ ↦ (0 : ℝ)))
        (measurable_localWalk_real l i))
    convert hh using 1
    ext u
    simp
  unfold localBirthReciprocalCorrection survivalReciprocalCorrection
  apply Measurable.ite hsurv _ measurable_const
  apply Measurable.tsum
  intro k
  apply Measurable.mul
  · exact (measurable_const.div (measurable_localWalk_real l (k + 1))).sub measurable_const
  · exact (measurable_of_countable (fun b : Bool ↦ if b then (1 : ℝ) else 0)).comp
      (measurable_localBirth l (k + 1 - 1))

/-- The actual local-walk reciprocal sum converges almost surely, with the
source's birth indicators, logarithmic coefficient, and initial-time survival
condition. The limit corrects the source's omitted survival multiplier and
Euler--Mascheroni shift. The centered component has an explicit L² bound. -/
theorem localWalk_survival_birth_reciprocal_convergence {l : ℝ} (hl : 1 < l) :
    ∃ Z' : (ℕ → ℝ) → ℝ, MemLp Z' 2 uniformLaw ∧
      eLpNorm Z' 2 uniformLaw ≤ ‖(localDrift l)⁻¹‖ₑ * ENNReal.ofReal
        ((∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ)⁻¹) ∧
      ∀ᵐ u ∂uniformLaw, Tendsto (fun n ↦
        (if ∀ i ≤ n, 0 < (localWalk l u i : ℝ) then (1 : ℝ) else 0) *
          ((∑ k ∈ Finset.range n,
            (if localBirth l u k then (1 : ℝ) else 0) / (localWalk l u (k + 1) : ℝ)) -
            l / (l - 1) * Real.log n)) atTop
        (𝓝 ((if ∀ i, 0 < (localWalk l u i : ℝ) then (1 : ℝ) else 0) *
          (Z' u + l / (l - 1) * Real.eulerMascheroniConstant) +
          localBirthReciprocalCorrection l u)) := by
  obtain ⟨Z', hZ', hnorm, hcenter⟩ := sourceBirth_harmonic_convergence hl
  refine ⟨Z', hZ', hnorm, ?_⟩
  filter_upwards [hcenter, positiveReciprocal_ae_uniform_bounded hl,
    localWalk_ae_power_deviation (zero_le_one.trans hl.le)] with u hcenter hratio hdev
  obtain ⟨M, hM⟩ := hratio
  obtain ⟨Y, _, hY⟩ := hdev
  let S : ℕ → ℝ := fun k ↦ (localWalk l u k : ℝ)
  let w : ℕ → ℝ := fun i ↦ if localBirth l u (i - 1) then 1 else 0
  have hr : (∀ i, 0 < S i) → ∀ k, ((k + 1 : ℕ) : ℝ) / S (k + 1) ≤ max M 0 := by
    intro hs k
    have hk : 0 < localWalk l u (k + 1) := by
      have hs' : (0 : ℝ) < (localWalk l u (k + 1) : ℝ) := hs (k + 1)
      exact_mod_cast hs' 
    have hh := (hM l le_rfl (k + 1)).trans (le_max_left M 0)
    simpa only [positiveReciprocal, ite_eq_left hk] using hh
  have hd : (∀ i, 0 < S i) → ∀ k,
      |S (k + 1) - localDrift l * (k + 1 : ℕ)| ≤
        Y * ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
    intro _ k
    simpa only [S, mul_comm] using hY (k + 1) (by omega)
  have hw : ∀ k, |w (k + 1)| ≤ 1 := by
    intro k
    dsimp only [w]
    split <;> norm_num
  have hc : Tendsto (fun n ↦ ∑ k ∈ Finset.range n,
      (w (k + 1) / localDrift l - l / (l - 1)) / (k + 1 : ℕ)) atTop (𝓝 (Z' u)) := by
    simpa only [w, Nat.add_sub_cancel] using hcenter
  have ht := tendsto_survival_weighted_reciprocal_sub_log S w (localDrift_pos hl)
    (le_max_right M 0) hr hd hw hc
  simpa only [S, w, Nat.add_sub_cancel, localBirthReciprocalCorrection] using ht

end HeightPaper.CountCoupling
