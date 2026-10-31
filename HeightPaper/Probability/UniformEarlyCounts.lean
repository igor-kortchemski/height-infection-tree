module

public import HeightPaper.Probability.ReciprocalRemainder

/-!
# Parameter-uniform early stochastic controls for the epidemic

All constants below are chosen before the infection parameter, population,
and full observation horizon. The geometric estimate applies to the actual
epidemic history, including histories that become extinct. This supplies the
early part of the count and safe-cutoff controls; a separate macroscopic
estimate is still needed beyond the uniformly supercritical window.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace HeightPaper.Model

/-- A common positive time window has uniformly supercritical pressure for
every parameter above a fixed supercritical lower bound. -/
theorem exists_uniform_early_pressure {L : ℝ} (hL : 1 < L) :
    ∃ δ R : ℝ, 0 < δ ∧ δ < 1 ∧ 1 < R ∧
      ∀ (l : ℝ≥0), L ≤ (l : ℝ) → ∀ n early : ℕ, 0 < n →
        (early : ℝ) ≤ δ * n → R ≤ ((l / n : ℝ≥0) : ℝ) * (n - early : ℕ) := by
  have hL0 : 0 < L := zero_lt_one.trans hL
  obtain ⟨R, hR1, hRL⟩ := exists_between hL
  let δ := 1 - R / L
  have hδ : 0 < δ := sub_pos.mpr ((div_lt_one hL0).mpr hRL)
  have hδ1 : δ < 1 := by
    have : 0 < R / L := div_pos (zero_lt_one.trans hR1) hL0
    dsimp [δ]
    linarith
  refine ⟨δ, R, hδ, hδ1, hR1, ?_⟩
  intro l hl n early hn he
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heN : early ≤ n := by
    have hstrict : (early : ℝ) < n :=
      he.trans_lt (by simpa using mul_lt_mul_of_pos_right hδ1 hnR)
    exact_mod_cast hstrict.le
  rw [NNReal.coe_div, NNReal.coe_natCast, Nat.cast_sub heN]
  have hremain : (1 - δ) * n ≤ (n : ℝ) - early := by nlinarith
  have hnonneg : 0 ≤ (n : ℝ) - early := sub_nonneg.mpr (by exact_mod_cast heN)
  have hratio : 1 - δ ≤ ((n : ℝ) - early) / n :=
    (le_div_iff₀ hnR).mpr hremain
  have hbase : R = L * (1 - δ) := by dsimp [δ]; field_simp; ring
  calc
    R = L * (1 - δ) := hbase
    _ ≤ L * (((n : ℝ) - early) / n) := mul_le_mul_of_nonneg_left hratio hL0.le
    _ ≤ (l : ℝ) * (((n : ℝ) - early) / n) :=
      mul_le_mul_of_nonneg_right hl (div_nonneg hnonneg hnR.le)
    _ = (l : ℝ) / n * ((n : ℝ) - early) := by ring

/-- An exponential lower-count barrier with constants independent of the
parameter and the entire observation horizon. -/
theorem exists_uniform_early_count_bound {L : ℝ} (hL : 1 < L) :
    ∃ δ c A ρ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < c ∧ 0 < A ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ (l : ℝ≥0), L ≤ (l : ℝ) → ∀ n early horizon K : ℕ,
        0 < n → early ≤ horizon → (early : ℝ) ≤ δ * n →
        (pathMeasure (l / n) n horizon).real
          (earlySmallActiveOnFull c K early horizon) ≤ A * ρ ^ K := by
  obtain ⟨δ, R, hδ, hδ1, hR1, hp⟩ := exists_uniform_early_pressure hL
  have hR : 0 < R := zero_lt_one.trans hR1
  obtain ⟨q, hqlo, hq1⟩ := exists_between ((div_lt_one hR).mpr hR1)
  have hq : 0 < q := (one_div_pos.mpr hR).trans hqlo
  have hRq : 1 < R * q := by have := (div_lt_iff₀ hR).mp hqlo; nlinarith
  obtain ⟨c, hc, hcg⟩ := exists_positive_count_slope hR.le hq hq1 hRq
  let ρ := geometricContraction R q / q ^ c
  have hρ : 0 ≤ ρ := div_nonneg (geometricContraction_pos hR.le hq).le
    (Real.rpow_pos_of_pos hq c).le
  have hρ1 : ρ < 1 := (div_lt_one (Real.rpow_pos_of_pos hq c)).mpr hcg
  refine ⟨δ, c, q / (1 - ρ), ρ, hδ, hδ1, hc, div_pos hq (sub_pos.mpr hρ1), hρ, hρ1, ?_⟩
  intro l hl n early horizon K hn he hwindow
  have h := pathMeasure_earlySmallActiveOnFull_le (l / n) n early horizon K he c
    hR.le hq hq1.le hcg (hp l hl n early hn hwindow)
  convert h using 1
  dsimp [ρ]
  ring

/-- Off the lower-count exception, all positive early count ratios are bounded
by one deterministic constant, including the finite initial segment. -/
theorem early_count_ratio_le_of_no_small {c : ℝ} (hc : 0 < c)
    (K early horizon : ℕ) (p : FinitePath horizon)
    (hp : p ∉ earlySmallActiveOnFull c K early horizon)
    {k : ℕ} (hk : k ≤ early) :
    (k : ℝ) / infectious (p.eval k) ≤ max (K : ℝ) (1 / c) := by
  by_cases hi : infectious (p.eval k) = 0
  · simp only [hi, Nat.cast_zero, div_zero]
    exact (Nat.cast_nonneg K).trans (le_max_left _ _)
  have hi1 : (1 : ℝ) ≤ infectious (p.eval k) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
  by_cases hK : k < K
  · apply le_trans (div_le_self (Nat.cast_nonneg k) hi1)
    exact (by exact_mod_cast hK.le : (k : ℝ) ≤ K).trans (le_max_left _ _)
  · have hb : c * k < (infectious (p.eval k) : ℝ) := by
      apply lt_of_not_ge
      intro h
      exact hp (mem_iUnion₂.mpr ⟨k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩,
        Nat.pos_of_ne_zero hi, h⟩)
    apply le_trans _ (le_max_right _ _)
    apply (div_le_iff₀ (zero_lt_one.trans_le hi1)).mpr
    have hdiv : (k : ℝ) ≤ (infectious (p.eval k) : ℝ) / c :=
      (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb.le)
    simpa only [one_div_mul_eq_div] using hdiv

/-- Genuine tightness, uniform over all supercritical parameters above `L`,
all positive population sizes, and all longer observation horizons. The
supremum over early event times is inside the probability. -/
theorem uniform_early_count_ratio_tight {L : ℝ} (hL : 1 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ ε > (0 : ℝ), ∃ M : ℝ, 0 < M ∧
      ∀ (l : ℝ≥0), L ≤ (l : ℝ) → ∀ n early horizon : ℕ,
        0 < n → early ≤ horizon → (early : ℝ) ≤ δ * n →
        (pathMeasure (l / n) n horizon).real
          {p | ∃ k ≤ early, M < (k : ℝ) / infectious (p.eval k)} < ε := by
  obtain ⟨δ, c, A, ρ, hδ, hδ1, hc, hA, hρ, hρ1, hbound⟩ :=
    exists_uniform_early_count_bound hL
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro ε hε
  have hlim : Tendsto (fun K : ℕ ↦ A * ρ ^ K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul A
  obtain ⟨K, hK⟩ := (hlim.eventually (Iio_mem_nhds hε)).exists
  refine ⟨max (K : ℝ) (1 / c), (one_div_pos.mpr hc).trans_le (le_max_right _ _), ?_⟩
  intro l hl n early horizon hn he hw
  apply lt_of_le_of_lt _ hK
  apply le_trans (measureReal_mono ?_) (hbound l hl n early horizon K hn he hw)
  intro p hp
  obtain ⟨k, hk, hbad⟩ := hp
  by_contra hgood
  exact not_lt_of_ge (early_count_ratio_le_of_no_small hc K early horizon p hgood hk) hbad

/-- Positive counts exceeding any fixed safe-product threshold after a common
random initial segment, with probability uniform in population and parameter.
The event ignores zero counts, so it also applies before conditioning on survival. -/
theorem uniform_early_safe_count_tight {L : ℝ} (hL : 1 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ B : ℝ, ∀ ε > (0 : ℝ), ∃ K : ℕ,
      ∀ (l : ℝ≥0), L ≤ (l : ℝ) → ∀ n early horizon : ℕ,
        0 < n → early ≤ horizon → (early : ℝ) ≤ δ * n →
        (pathMeasure (l / n) n horizon).real {p | ∃ k,
          K ≤ k ∧ k ≤ early ∧ 0 < infectious (p.eval k) ∧
            (infectious (p.eval k) : ℝ) ≤ B} < ε := by
  obtain ⟨δ, c, A, ρ, hδ, hδ1, hc, hA, hρ, hρ1, hbound⟩ :=
    exists_uniform_early_count_bound hL
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro B ε hε
  have hlim : Tendsto (fun K : ℕ ↦ A * ρ ^ K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul A
  have hlinear : Tendsto (fun K : ℕ ↦ c * (K : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  obtain ⟨K, hK, hKB⟩ := ((hlim.eventually (Iio_mem_nhds hε)).and
    (hlinear.eventually (eventually_ge_atTop B))).exists
  refine ⟨K, ?_⟩
  intro l hl n early horizon hn he hw
  apply lt_of_le_of_lt _ hK
  apply le_trans (measureReal_mono ?_) (hbound l hl n early horizon K hn he hw)
  intro p hp
  obtain ⟨k, hkK, hk, hi, hB⟩ := hp
  refine mem_iUnion₂.mpr ⟨k, Finset.mem_Ico.mpr ⟨hkK, by omega⟩, hi, ?_⟩
  exact hB.trans (hKB.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hkK) hc.le))

/-- The reciprocal-square tail bound also holds when the short path is a
prefix of a longer observation. -/
theorem early_reciprocalSquare_tail_le_of_no_small {c : ℝ} (hc : 0 < c)
    (K early horizon : ℕ) (p : FinitePath horizon)
    (hp : p ∉ earlySmallActiveOnFull c (K + 1) early horizon) :
    (∑ k ∈ Finset.Ioo K (early + 1), ((infectious (p.eval k) : ℝ) ^ 2)⁻¹) ≤
      2 / (c ^ 2 * (K + 1)) := by
  let shortPath : FinitePath early := ⟨fun i ↦ p.eval i.val⟩
  have heval (k : ℕ) (hk : k ≤ early) : shortPath.eval k = p.eval k := by
    change p.eval (min k early) = p.eval k
    rw [Nat.min_eq_left hk]
  have hprefix : shortPath ∉ earlySmallActivePaths c (K + 1) early := by
    intro h
    obtain ⟨k, hk, hm⟩ := mem_iUnion₂.mp h
    have hke : k ≤ early := by have := (Finset.mem_Ico.mp hk).2; omega
    change shortPath.eval k ∈ smallActiveCount c k at hm
    rw [heval k hke] at hm
    exact hp (mem_iUnion₂.mpr ⟨k, hk, hm⟩)
  have htail := reciprocalSquare_tail_le_of_no_small c hc K early shortPath hprefix
  convert htail using 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [heval k (by have := (Finset.mem_Ioo.mp hk).2; omega)]

/-- The early quadratic reciprocal remainder vanishes as its starting time
increases, uniformly over parameters, populations, and observation horizons.
Both the error tolerance and the probability tolerance are arbitrary. -/
theorem uniform_early_reciprocal_square_tail {L : ℝ} (hL : 1 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ ε > (0 : ℝ), ∀ η > (0 : ℝ), ∃ K : ℕ,
      ∀ (l : ℝ≥0), L ≤ (l : ℝ) → ∀ n early horizon : ℕ,
        0 < n → early ≤ horizon → (early : ℝ) ≤ δ * n →
        (pathMeasure (l / n) n horizon).real {p | ε <
          ∑ k ∈ Finset.Ioo K (early + 1), ((infectious (p.eval k) : ℝ) ^ 2)⁻¹} < η := by
  obtain ⟨δ, c, A, ρ, hδ, hδ1, hc, hA, hρ, hρ1, hbound⟩ :=
    exists_uniform_early_count_bound hL
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro ε hε η hη
  have hlim : Tendsto (fun K : ℕ ↦ A * ρ ^ (K + 1)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).comp
      (tendsto_add_atTop_nat 1)).const_mul A
  have htail : Tendsto (fun K : ℕ ↦ 2 / (c ^ 2 * ((K : ℝ) + 1))) atTop (𝓝 0) := by
    have h := ((tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun k : ℕ ↦ (1 : ℝ) / k) atTop (𝓝 0)).comp
        (tendsto_add_atTop_nat 1)).const_mul (2 / c ^ 2)
    convert h using 1
    · funext K
      simp only [Function.comp_apply]
      push_cast
      simp only [div_eq_mul_inv, mul_inv]
      ring
    · simp
  obtain ⟨K, hK, htailK⟩ := ((hlim.eventually (Iio_mem_nhds hη)).and
    (htail.eventually (Iio_mem_nhds hε))).exists
  refine ⟨K, ?_⟩
  intro l hl n early horizon hn he hw
  apply lt_of_le_of_lt _ hK
  apply le_trans (measureReal_mono ?_) (hbound l hl n early horizon (K + 1) hn he hw)
  intro p hp
  by_contra hgood
  have h := early_reciprocalSquare_tail_le_of_no_small hc K early horizon p hgood
  exact not_lt_of_ge h (htailK.trans hp)

end HeightPaper.Model
