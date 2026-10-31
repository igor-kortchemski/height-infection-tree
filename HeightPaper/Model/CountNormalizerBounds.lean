module

public import HeightPaper.Model.PolynomialNormalizer
public import HeightPaper.Model.BirthHarmonic
public import HeightPaper.Analysis.ReciprocalBounds
public import Mathlib.Analysis.PSeries

/-!
# Product normalizer bounds from linear count barriers

The early count barriers yield logarithmic reciprocal bounds with constants
independent of the terminal index. Harmonic telescoping turns these into the
uniform polynomial product estimates used by finite profile moments.
-/

public section

open scoped BigOperators

namespace HeightPaper.Model

/-- Reciprocal pinching with an arbitrary fixed initial segment. -/
theorem count_reciprocal_log_bounds (S : ℕ → ℕ) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi) {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N)
    (hpos : ∀ k < N, 0 < S k)
    (hlower : ∀ k ∈ Finset.Ico K N, lo * k ≤ (S k : ℝ))
    (hupper : ∀ k ∈ Finset.Ico K N, (S k : ℝ) ≤ hi * k) :
    (Real.log N - ((harmonic K : ℝ) + 1)) / hi ≤
        ∑ k ∈ Finset.range N, 1 / (S k : ℝ) ∧
      (∑ k ∈ Finset.range N, 1 / (S k : ℝ)) ≤
        K + (Real.log N + 1) / lo := by
  have hpinch : (∑ k ∈ Finset.Ico K N, 1 / (k : ℝ)) / hi ≤
      ∑ k ∈ Finset.Ico K N, 1 / (S k : ℝ) ∧
      (∑ k ∈ Finset.Ico K N, 1 / (S k : ℝ)) ≤
        (∑ k ∈ Finset.Ico K N, 1 / (k : ℝ)) / lo := by
    constructor <;> rw [Finset.sum_div] <;> apply Finset.sum_le_sum
    · intro k hk
      have hSk : (0 : ℝ) < S k := by exact_mod_cast hpos k (Finset.mem_Ico.mp hk).2
      have hh := one_div_le_one_div_of_le hSk (hupper k hk)
      simpa only [div_div, mul_comm] using hh
    · intro k hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := (Finset.mem_Ico.mp hk).1; omega)
      have hh := one_div_le_one_div_of_le (mul_pos hlo hk0) (hlower k hk)
      simpa only [div_div, mul_comm] using hh
  have hprefix : (∑ k ∈ Finset.range K, 1 / (S k : ℝ)) ≤ (K : ℝ) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hh : (1 : ℝ) ≤ S k := by exact_mod_cast hpos k ((Finset.mem_range.mp hk).trans_le hKN)
        simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hh
      _ = _ := by simp
  have hprefix0 : 0 ≤ ∑ k ∈ Finset.range K, 1 / (S k : ℝ) := by positivity
  have hh := reciprocal_Ico_log_bounds hKN
  rw [← Finset.sum_range_add_sum_Ico _ hKN]
  constructor
  · exact (div_le_div_of_nonneg_right hh.1 hhi.le).trans (hpinch.1.trans (le_add_of_nonneg_left hprefix0))
  · exact add_le_add hprefix (hpinch.2.trans (div_le_div_of_nonneg_right hh.2 hlo.le))

/-- A linear lower count barrier makes the quadratic product error uniformly bounded. -/
theorem count_reciprocalSquare_bound (S : ℕ → ℕ) {lo : ℝ}
    (hlo : 0 < lo) {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N)
    (hpos : ∀ k < N, 0 < S k)
    (hlower : ∀ k ∈ Finset.Ico K N, lo * k ≤ (S k : ℝ)) :
    (∑ k ∈ Finset.range N, (1 / (S k : ℝ)) ^ 2) ≤ K + 2 / lo ^ 2 := by
  have hprefix : (∑ k ∈ Finset.range K, (1 / (S k : ℝ)) ^ 2) ≤ (K : ℝ) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hh : (1 : ℝ) ≤ S k := by exact_mod_cast hpos k ((Finset.mem_range.mp hk).trans_le hKN)
        have hu : 1 / (S k : ℝ) ≤ 1 := by
          simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hh
        simpa only [one_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (S k : ℝ)) hu 2
      _ = _ := by simp
  have htail : (∑ k ∈ Finset.Ico K N, (1 / (S k : ℝ)) ^ 2) ≤ 2 / lo ^ 2 := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico K N, (lo ^ 2)⁻¹ * ((k : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum
        intro k hk
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := (Finset.mem_Ico.mp hk).1; omega)
        have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (S k : ℝ))
          (one_div_le_one_div_of_le (mul_pos hlo hk0) (hlower k hk)) 2
        simpa only [div_pow, one_pow, one_div, mul_pow, mul_inv, inv_pow] using hh
      _ = (lo ^ 2)⁻¹ * ∑ k ∈ Finset.Ico K N, ((k : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (lo ^ 2)⁻¹ * ∑ k ∈ Finset.Ioo 0 N, ((k : ℝ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          have hh := Finset.mem_Ico.mp hk
          exact Finset.mem_Ioo.mpr ⟨by omega, hh.2⟩
        · intro k _ _
          positivity
      _ ≤ (lo ^ 2)⁻¹ * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 N)
      _ = _ := by ring
  rw [← Finset.sum_range_add_sum_Ico _ hKN]
  exact add_le_add hprefix htail

/-- The constants in the early polynomial bounds do not depend on the event
word or on its terminal index. -/
theorem exists_count_normalizer_constants {lo hi w : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi) (hw : 1 ≤ w) (K : ℕ) (hK : 1 ≤ K) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (events : ℕ → Bool) (N : ℕ), K ≤ N →
      (∀ k ≤ N, 0 < prescribedWalk events 1 k) →
      (∀ k ∈ Finset.Icc K N, lo * k ≤ (prescribedWalk events 1 k : ℝ)) →
      (∀ k ∈ Finset.Icc K N, (prescribedWalk events 1 k : ℝ) ≤ hi * k) →
      A * (N : ℝ) ^ ((w - 1) * ((1 + 1 / hi) / 2)) ≤ realNormalizer w events 1 N ∧
      realNormalizer w events 1 N ≤ B * (N : ℝ) ^ ((w - 1) * ((1 + 1 / lo) / 2)) := by
  let D : ℝ := K + 2 / lo ^ 2
  let CL : ℝ := (1 - Real.log lo + ((harmonic K : ℝ) + 1) / hi + D) / 2
  let CU : ℝ := (Real.log hi + K + 1 / lo) / 2
  let C := max CL CU
  refine ⟨Real.exp (-((w - 1) * C + (w - 1) ^ 2 * D)),
    Real.exp ((w - 1) * C + (w - 1) ^ 2 * D), Real.exp_pos _, Real.exp_pos _, ?_⟩
  intro events N hKN hpos hlow hupp
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrecip := count_reciprocal_log_bounds (prescribedWalk events 1) hlo hhi hK hKN
    (fun k hk ↦ hpos k hk.le)
    (fun k hk ↦ hlow k (Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2.le⟩))
    (fun k hk ↦ hupp k (Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2.le⟩))
  have hsquare := count_reciprocalSquare_bound (prescribedWalk events 1) hlo hK hKN
    (fun k hk ↦ hpos k hk.le)
    (fun k hk ↦ hlow k (Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2.le⟩))
  have hSN : (0 : ℝ) < prescribedWalk events 1 N := by exact_mod_cast hpos N le_rfl
  have hlN := hlow N (Finset.mem_Icc.mpr ⟨hKN, le_rfl⟩)
  have huN := hupp N (Finset.mem_Icc.mpr ⟨hKN, le_rfl⟩)
  have hlLog := Real.log_le_log (mul_pos hlo hNR) hlN
  have huLog := Real.log_le_log hSN huN
  rw [Real.log_mul hlo.ne' hNR.ne'] at hlLog
  rw [Real.log_mul hhi.ne' hNR.ne'] at huLog
  have hharm := harmonic_sub_log_bounds (prescribedWalk events 1 N)
  have herr := sum_birthReciprocal_error_bounds events 1 N (fun k hk ↦ hpos k hk.le)
  have hhone : (harmonic 1 : ℝ) = 1 := by norm_num [harmonic]
  rw [hhone] at herr
  have hbirthsquare : (∑ k ∈ Finset.range N, (birthReciprocal events 1 k) ^ 2) ≤ D := by
    apply le_trans _ hsquare
    apply Finset.sum_le_sum
    intro k hk
    exact pow_le_pow_left₀ (birthReciprocal_nonneg events 1 k)
      (birthReciprocal_le_count_inv events 1 k (hpos k (Finset.mem_range.mp hk).le)) 2
  simp only [one_div] at herr hsquare
  ring_nf at hsquare
  apply realNormalizer_polynomial_bounds hw hNR events 1 N _ _ hbirthsquare
  · have hC : CL ≤ C := le_max_left _ _
    dsimp [CL, D] at hC
    simp only [div_eq_mul_inv] at hC hrecip ⊢
    ring_nf at hC hrecip ⊢
    nlinarith only [herr.2, hsquare, hharm.1, hlLog, hrecip.1, hC]
  · have hC : CU ≤ C := le_max_right _ _
    dsimp [CU] at hC
    simp only [div_eq_mul_inv] at hC hrecip ⊢
    ring_nf at hC hrecip ⊢
    nlinarith only [herr.1, hharm.2, huLog, hrecip.2, hC]

end HeightPaper.Model
