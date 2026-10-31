module

public import HeightPaper.Model.ComplexNormalizer
public import HeightPaper.Model.ReciprocalCoupling

/-! # Finite normalizer errors from centered sums and count ratios -/

@[expose] public section

open scoped BigOperators

namespace HeightPaper.Model

theorem birthReciprocal_le_one (events : ℕ → Bool) (i₀ i : ℕ) :
    birthReciprocal events i₀ i ≤ 1 := by
  unfold birthReciprocal
  split_ifs
  · apply (div_le_one (by positivity : (0 : ℝ) < (prescribedWalk events i₀ i : ℝ) + 1)).mpr
    have h : (0 : ℝ) ≤ (prescribedWalk events i₀ i : ℝ) := Nat.cast_nonneg _
    linarith
  · norm_num

/-- Removing a bounded prefix changes a centered birth-reciprocal sum by at
most the length of that prefix. -/
theorem birthReciprocal_Ico_centered_bound (events : ℕ → Bool) (i₀ j k K : ℕ)
    {γ B : ℝ} (hjk : j ≤ k) (hjK : j ≤ K)
    (hcenter : |(∑ i ∈ Finset.range k, birthReciprocal events i₀ i) -
      γ * Real.log k| ≤ B) :
    |(∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) - γ * Real.log k| ≤ B + K := by
  have hprefix0 : 0 ≤ ∑ i ∈ Finset.range j, birthReciprocal events i₀ i :=
    Finset.sum_nonneg (fun i _ ↦ birthReciprocal_nonneg events i₀ i)
  have hprefix : (∑ i ∈ Finset.range j, birthReciprocal events i₀ i) ≤ K := by
    calc
      _ ≤ ∑ _i ∈ Finset.range j, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ ↦ birthReciprocal_le_one events i₀ i)
      _ = (j : ℝ) := by simp
      _ ≤ K := by exact_mod_cast hjK
  have heq := Finset.sum_range_add_sum_Ico (birthReciprocal events i₀) hjk
  have htri := abs_sub
    ((∑ i ∈ Finset.range k, birthReciprocal events i₀ i) - γ * Real.log k)
    (∑ i ∈ Finset.range j, birthReciprocal events i₀ i)
  rw [abs_of_nonneg hprefix0] at htri
  have hrewrite : (∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) - γ * Real.log k =
      ((∑ i ∈ Finset.range k, birthReciprocal events i₀ i) - γ * Real.log k) -
        ∑ i ∈ Finset.range j, birthReciprocal events i₀ i := by linarith
  rw [hrewrite]
  exact htri.trans (add_le_add hcenter hprefix)

/-- A common linear count-ratio bound controls every quadratic remainder. -/
theorem birthReciprocal_Ico_square_bound (events : ℕ → Bool) (i₀ j k : ℕ)
    {M : ℝ}
    (hbound : ∀ i < k, birthReciprocal events i₀ i ≤ M / ((i + 1 : ℕ) : ℝ)) :
    (∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2) ≤ 2 * M ^ 2 := by
  calc
    _ ≤ ∑ i ∈ Finset.range k, (birthReciprocal events i₀ i) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
      · intro i _ _
        positivity
    _ ≤ ∑ i ∈ Finset.range k, M ^ 2 * (1 / ((i + 1 : ℕ) : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [div_pow, mul_one_div] using
        pow_le_pow_left₀ (birthReciprocal_nonneg events i₀ i)
          (hbound i (Finset.mem_range.mp hi)) 2
    _ = M ^ 2 * ∑ i ∈ Finset.range k, 1 / ((i + 1 : ℕ) : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ M ^ 2 * 2 := mul_le_mul_of_nonneg_left
      (HeightPaper.CountCoupling.sum_succ_reciprocal_square_le_two k) (sq_nonneg M)
    _ = _ := by ring

/-- The explicit complex error, rather than a choice of a global logarithm,
has the source's uniform quadratic bound. -/
theorem norm_normalizerCenteredLogFrom_le (events : ℕ → Bool) (i₀ j k : ℕ)
    {γ B Q R : ℝ} (hR : 0 ≤ R)
    (hcenter : |(∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) - γ * Real.log k| ≤ B)
    (hsquare : (∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2) ≤ Q)
    (w : ℂ) (hw : ‖w - 1‖ ≤ R)
    (hsmall : ∀ i ∈ Finset.Ico j k,
      ‖w - 1‖ * birthReciprocal events i₀ i ≤ 1 / 2) :
    ‖normalizerCenteredLogFrom events i₀ j k γ w‖ ≤ R * B + R ^ 2 * Q := by
  have hQ0 : 0 ≤ ∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2 :=
    Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  unfold normalizerCenteredLogFrom
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hw hcenter (abs_nonneg _) hR
  · exact (norm_normalizerRemainderFrom_le w events i₀ j k hsmall).trans
      (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hw 2) hsquare hQ0 (sq_nonneg R))

/-- A common error bound for the real logarithm of every moment ratio. -/
theorem normalizerFrom_momentRatio_centered_bound (events : ℕ → Bool) (i₀ j k : ℕ)
    {γ B Q R V P v p : ℝ} (hR : 0 ≤ R) (hV : 0 ≤ V) (hP : 0 ≤ P)
    (hv : 1 ≤ v) (hvV : v - 1 ≤ V) (hp : |p| ≤ P)
    (hcenter : |(∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) - γ * Real.log k| ≤ B)
    (hsquare : (∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2) ≤ Q)
    (w : ℂ) (hw : ‖w - 1‖ ≤ R)
    (hsmall : ∀ i ∈ Finset.Ico j k,
      ‖w - 1‖ * birthReciprocal events i₀ i ≤ 1 / 2) :
    |Real.log (realNormalizerFrom v events i₀ j k /
        ‖prescribedNormalizerFrom w events i₀ j k‖ ^ p) -
      γ * (v - 1 - p * (w.re - 1)) * Real.log k| ≤
      (V + P * R) * B + (V ^ 2 + P * R ^ 2) * Q := by
  have hre : |w.re - 1| ≤ R := by
    simpa only [Complex.sub_re, Complex.one_re] using
      (Complex.abs_re_le_norm (w - 1)).trans hw
  have hcoef : |v - 1 - p * (w.re - 1)| ≤ V + P * R := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hv), abs_mul]
    exact add_le_add hvV (mul_le_mul hp hre (abs_nonneg _) hP)
  have hquad : (v - 1) ^ 2 + |p| * ‖w - 1‖ ^ 2 ≤ V ^ 2 + P * R ^ 2 :=
    add_le_add (pow_le_pow_left₀ (sub_nonneg.mpr hv) hvV 2)
      (mul_le_mul hp (pow_le_pow_left₀ (norm_nonneg _) hw 2) (sq_nonneg _) hP)
  have hQ0 : 0 ≤ ∑ i ∈ Finset.Ico j k, (birthReciprocal events i₀ i) ^ 2 :=
    Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hrem := normalizerFrom_momentRatio_log_remainder hv w p events i₀ j k hsmall
  have heq : Real.log (realNormalizerFrom v events i₀ j k /
        ‖prescribedNormalizerFrom w events i₀ j k‖ ^ p) -
      γ * (v - 1 - p * (w.re - 1)) * Real.log k =
      (Real.log (realNormalizerFrom v events i₀ j k /
        ‖prescribedNormalizerFrom w events i₀ j k‖ ^ p) -
        (v - 1 - p * (w.re - 1)) * ∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) +
      (v - 1 - p * (w.re - 1)) *
        ((∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) - γ * Real.log k) := by ring
  rw [heq]
  apply (abs_add_le _ _).trans
  have h₁ := hrem.trans (mul_le_mul hquad hsquare hQ0 (by positivity))
  have h₂ : |(v - 1 - p * (w.re - 1)) *
      ((∑ i ∈ Finset.Ico j k, birthReciprocal events i₀ i) - γ * Real.log k)| ≤
      (V + P * R) * B := by
    rw [abs_mul]
    exact mul_le_mul hcoef hcenter (abs_nonneg _) (by positivity)
  linarith

end HeightPaper.Model
