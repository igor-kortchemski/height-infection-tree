module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Exponential bounds for finite height profiles

These deterministic inequalities isolate an alternative route to the weak
profile estimate needed by `thm:main`. They apply to arbitrary finite
nonnegative weights and real depths. Turning them into epidemic asymptotics
still requires proving the real Laplace-transform estimates for that model.
-/

public section

open scoped BigOperators

namespace HeightPaper.Profile

variable {α : Type*}

/-- The Laplace transform of a finite weighted depth profile. -/
@[expose] noncomputable def laplaceSum (s : Finset α) (w d : α → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, w i * Real.exp (t * d i)

/-- Total weight of vertices at or above a real height threshold. -/
@[expose] noncomputable def tailMass (s : Finset α) (w d : α → ℝ) (a : ℝ) : ℝ := by
  classical
  exact ∑ i ∈ s, if a ≤ d i then w i else 0

/-- Total weight of vertices in the closed height interval `[a,b]`. -/
@[expose] noncomputable def binMass (s : Finset α) (w d : α → ℝ) (a b : ℝ) : ℝ := by
  classical
  exact ∑ i ∈ s, if a ≤ d i ∧ d i ≤ b then w i else 0

theorem laplaceSum_nonneg (s : Finset α) (w d : α → ℝ) (t : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ laplaceSum s w d t := by
  exact Finset.sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (Real.exp_nonneg _)

theorem binMass_nonneg (s : Finset α) (w d : α → ℝ) (a b : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ binMass s w d a b := by
  classical
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact hw i hi
  · exact le_rfl

/-- Exponential Markov bound for a finite profile; no probability-space
normalization is required. -/
theorem exp_mul_tailMass_le_laplaceSum (s : Finset α) (w d : α → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (a : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    Real.exp (t * a) * tailMass s w d a ≤ laplaceSum s w d t := by
  classical
  unfold tailMass laplaceSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : a ≤ d i
  · simp only [ite_eq_left h]
    rw [mul_comm (Real.exp (t * a))]
    apply mul_le_mul_of_nonneg_left _ (hw i hi)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h ht)
  · simp only [ite_eq_right h, mul_zero]
    exact mul_nonneg (hw i hi) (Real.exp_nonneg _)

theorem tailMass_le_exp_neg_mul_laplaceSum (s : Finset α) (w d : α → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (a : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    tailMass s w d a ≤ Real.exp (-t * a) * laplaceSum s w d t := by
  have h := exp_mul_tailMass_le_laplaceSum s w d ht a hw
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_nonneg (-t * a))
  have hexp : Real.exp (-t * a) * Real.exp (t * a) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simpa only [← mul_assoc, hexp, one_mul] using hmul

theorem binMass_le_tailMass (s : Finset α) (w d : α → ℝ) (a b : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : binMass s w d a b ≤ tailMass s w d a := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  by_cases hlo : a ≤ d i
  · by_cases hhi : d i ≤ b
    · simp only [hlo, hhi, and_self, ite_true, le_refl]
    · simp only [hlo, hhi, and_false, ite_false, ite_true]
      exact hw i hi
  · simp only [hlo, false_and, ite_false, le_refl]

/-- The Laplace transform at `t` is bounded by the contribution from the bin
and two exponentially discounted transforms at nearby tilts. -/
theorem laplaceSum_le_bin_and_nearby (s : Finset α) (w d : α → ℝ)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (a b : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    laplaceSum s w d t ≤ Real.exp (t * b) * binMass s w d a b +
      Real.exp (ε * a) * laplaceSum s w d (t - ε) +
      Real.exp (-ε * b) * laplaceSum s w d (t + ε) := by
  classical
  unfold laplaceSum binMass
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hlower_nonneg : 0 ≤ Real.exp (ε * a) * (w i * Real.exp ((t - ε) * d i)) :=
    mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hw i hi) (Real.exp_nonneg _))
  have hupper_nonneg : 0 ≤ Real.exp (-ε * b) * (w i * Real.exp ((t + ε) * d i)) :=
    mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hw i hi) (Real.exp_nonneg _))
  by_cases hbin : a ≤ d i ∧ d i ≤ b
  · simp only [ite_eq_left hbin]
    have hm : w i * Real.exp (t * d i) ≤ Real.exp (t * b) * w i := by
      rw [mul_comm (Real.exp (t * b))]
      apply mul_le_mul_of_nonneg_left _ (hw i hi)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbin.2 ht)
    linarith
  · simp only [ite_eq_right hbin, mul_zero, zero_add]
    by_cases hlo : d i < a
    · have hexp : Real.exp (t * d i) ≤
          Real.exp (ε * a) * Real.exp ((t - ε) * d i) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hε (sub_nonneg.mpr hlo.le)]
      have hm := mul_le_mul_of_nonneg_left hexp (hw i hi)
      nlinarith
    · have hhi : b < d i := lt_of_not_ge (fun h ↦ hbin ⟨le_of_not_gt hlo, h⟩)
      have hexp : Real.exp (t * d i) ≤
          Real.exp (-ε * b) * Real.exp ((t + ε) * d i) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hε (sub_nonneg.mpr hhi.le)]
      have hm := mul_le_mul_of_nonneg_left hexp (hw i hi)
      nlinarith

/-- A direct lower bin-mass bound obtained from the two neighboring Laplace
transforms. This is the deterministic exponential-tilting estimate. -/
theorem exp_neg_mul_laplace_gap_le_binMass (s : Finset α) (w d : α → ℝ)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (a b : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    Real.exp (-t * b) * (laplaceSum s w d t -
      Real.exp (ε * a) * laplaceSum s w d (t - ε) -
      Real.exp (-ε * b) * laplaceSum s w d (t + ε)) ≤ binMass s w d a b := by
  have h := laplaceSum_le_bin_and_nearby s w d ht hε a b hw
  have hgap : laplaceSum s w d t -
      Real.exp (ε * a) * laplaceSum s w d (t - ε) -
      Real.exp (-ε * b) * laplaceSum s w d (t + ε) ≤
      Real.exp (t * b) * binMass s w d a b := by linarith
  have hmul := mul_le_mul_of_nonneg_left hgap (Real.exp_nonneg (-t * b))
  have hexp : Real.exp (-t * b) * Real.exp (t * b) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simpa only [← mul_assoc, hexp, one_mul] using hmul

/-- If the discounted neighboring transforms occupy at most a fraction `q`
of the transform at `t`, the bin contains the remaining tilted mass. -/
theorem one_sub_mul_laplace_le_binMass (s : Finset α) (w d : α → ℝ)
    {t ε q : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (a b : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsmall : Real.exp (ε * a) * laplaceSum s w d (t - ε) +
      Real.exp (-ε * b) * laplaceSum s w d (t + ε) ≤ q * laplaceSum s w d t) :
    Real.exp (-t * b) * ((1 - q) * laplaceSum s w d t) ≤ binMass s w d a b := by
  apply le_trans _ (exp_neg_mul_laplace_gap_le_binMass s w d ht hε a b hw)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  nlinarith

/-- With unit weights, the profile mass is precisely the number of vertices
in the bin. -/
theorem binMass_one_eq_card (s : Finset α) (d : α → ℝ) (a b : ℝ) :
    binMass s (fun _ ↦ 1) d a b =
      ((s.filter fun i ↦ a ≤ d i ∧ d i ≤ b).card : ℝ) := by
  classical
  simp [binMass]

/-- Strict dominance of the central transform forces positive bin mass. -/
theorem binMass_pos_of_nearby_small (s : Finset α) (w d : α → ℝ)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (a b : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsmall : Real.exp (ε * a) * laplaceSum s w d (t - ε) +
      Real.exp (-ε * b) * laplaceSum s w d (t + ε) < laplaceSum s w d t) :
    0 < binMass s w d a b := by
  have hbound := laplaceSum_le_bin_and_nearby s w d ht hε a b hw
  have hexp := Real.exp_pos (t * b)
  have hpos : 0 < Real.exp (t * b) * binMass s w d a b := by linarith
  exact (mul_pos_iff_of_pos_left hexp).mp hpos

end HeightPaper.Profile
