module

public import HeightPaper.Model.RealNormalizer
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Harmonic telescoping for birth reciprocals

The reciprocal after a birth differs from the reciprocal before the event by
a summable quadratic error. Harmonic increments separate births from recoveries,
giving the exact deterministic input for the profile normalizer coefficient.
-/

@[expose] public section

open scoped BigOperators

namespace HeightPaper.Model

noncomputable def eventReciprocal (events : ℕ → Bool) (i₀ k : ℕ) : ℝ :=
  if events k then 1 / ((prescribedWalk events i₀ k : ℝ) + 1)
  else 1 / (prescribedWalk events i₀ k : ℝ)

theorem birthReciprocal_le_count_inv (events : ℕ → Bool) (i₀ k : ℕ)
    (hi : 0 < prescribedWalk events i₀ k) :
    birthReciprocal events i₀ k ≤ 1 / (prescribedWalk events i₀ k : ℝ) := by
  have hI : (0 : ℝ) < prescribedWalk events i₀ k := by exact_mod_cast hi
  unfold birthReciprocal
  split_ifs
  · exact one_div_le_one_div_of_le hI (by linarith)
  · positivity

private theorem harmonic_succ_real (i : ℕ) :
    (harmonic (i + 1) : ℝ) = (harmonic i : ℝ) + 1 / ((i : ℝ) + 1) := by
  have h := congrArg (fun q : ℚ ↦ (q : ℝ)) (harmonic_succ i)
  push_cast at h
  simpa only [one_div] using h

theorem prescribedWalk_harmonic_step (events : ℕ → Bool) (i₀ k : ℕ)
    (hi : 0 < prescribedWalk events i₀ k) :
    (harmonic (prescribedWalk events i₀ (k + 1)) : ℝ) -
      harmonic (prescribedWalk events i₀ k) =
      2 * birthReciprocal events i₀ k - eventReciprocal events i₀ k := by
  cases he : events k with
  | true =>
      simp only [prescribedWalk, prescribedActiveCount, he, ↓reduceIte,
        birthReciprocal, eventReciprocal, harmonic_succ_real]
      ring
  | false =>
      have hn : prescribedWalk events i₀ k - 1 + 1 = prescribedWalk events i₀ k := by omega
      have hh := harmonic_succ_real (prescribedWalk events i₀ k - 1)
      rw [hn, Nat.cast_sub (by omega : 1 ≤ prescribedWalk events i₀ k), Nat.cast_one,
        sub_add_cancel] at hh
      simp only [prescribedWalk, prescribedActiveCount, he, Bool.false_eq_true, ↓reduceIte,
        birthReciprocal, eventReciprocal, mul_zero, zero_sub]
      linarith

/-- Exact harmonic identity for every positive pre-event count. -/
theorem sum_birthReciprocal_eq_harmonic (events : ℕ → Bool) (i₀ N : ℕ)
    (hpos : ∀ k < N, 0 < prescribedWalk events i₀ k) :
    2 * ∑ k ∈ Finset.range N, birthReciprocal events i₀ k =
      (harmonic (prescribedWalk events i₀ N) : ℝ) - harmonic i₀ +
        ∑ k ∈ Finset.range N, eventReciprocal events i₀ k := by
  induction N with
  | zero => simp [prescribedWalk]
  | succ N ih =>
      have hprev := ih (fun k hk ↦ hpos k (by omega))
      have hstep := prescribedWalk_harmonic_step events i₀ N (hpos N (by omega))
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith

theorem eventReciprocal_error_bounds (events : ℕ → Bool) (i₀ k : ℕ)
    (hi : 0 < prescribedWalk events i₀ k) :
    0 ≤ 1 / (prescribedWalk events i₀ k : ℝ) - eventReciprocal events i₀ k ∧
      1 / (prescribedWalk events i₀ k : ℝ) - eventReciprocal events i₀ k ≤
        (1 / (prescribedWalk events i₀ k : ℝ)) ^ 2 := by
  have hI : (0 : ℝ) < prescribedWalk events i₀ k := by exact_mod_cast hi
  cases he : events k with
  | false => simp [eventReciprocal, he]
  | true =>
      simp only [eventReciprocal, he, ↓reduceIte]
      have hplus : 0 < (prescribedWalk events i₀ k : ℝ) + 1 := by positivity
      constructor
      · exact sub_nonneg.mpr (one_div_le_one_div_of_le hI (by linarith))
      · rw [div_pow, one_pow]
        apply (le_div_iff₀ (sq_pos_of_pos hI)).mpr
        field_simp
        nlinarith

/-- The reciprocal-count sum determines the birth sum up to a quadratic
error and the exact harmonic boundary term. -/
theorem sum_birthReciprocal_error_bounds (events : ℕ → Bool) (i₀ N : ℕ)
    (hpos : ∀ k < N, 0 < prescribedWalk events i₀ k) :
    0 ≤ (harmonic (prescribedWalk events i₀ N) : ℝ) - harmonic i₀ +
        (∑ k ∈ Finset.range N, 1 / (prescribedWalk events i₀ k : ℝ)) -
        2 * ∑ k ∈ Finset.range N, birthReciprocal events i₀ k ∧
    (harmonic (prescribedWalk events i₀ N) : ℝ) - harmonic i₀ +
        (∑ k ∈ Finset.range N, 1 / (prescribedWalk events i₀ k : ℝ)) -
        2 * ∑ k ∈ Finset.range N, birthReciprocal events i₀ k ≤
      ∑ k ∈ Finset.range N, (1 / (prescribedWalk events i₀ k : ℝ)) ^ 2 := by
  rw [sum_birthReciprocal_eq_harmonic events i₀ N hpos]
  have heq : (harmonic (prescribedWalk events i₀ N) : ℝ) - harmonic i₀ +
      (∑ k ∈ Finset.range N, 1 / (prescribedWalk events i₀ k : ℝ)) -
      ((harmonic (prescribedWalk events i₀ N) : ℝ) - harmonic i₀ +
        ∑ k ∈ Finset.range N, eventReciprocal events i₀ k) =
      ∑ k ∈ Finset.range N,
        (1 / (prescribedWalk events i₀ k : ℝ) - eventReciprocal events i₀ k) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [heq]
  exact ⟨Finset.sum_nonneg (fun k hk ↦
      (eventReciprocal_error_bounds events i₀ k (hpos k (Finset.mem_range.mp hk))).1),
    Finset.sum_le_sum (fun k hk ↦
      (eventReciprocal_error_bounds events i₀ k (hpos k (Finset.mem_range.mp hk))).2)⟩

end HeightPaper.Model
