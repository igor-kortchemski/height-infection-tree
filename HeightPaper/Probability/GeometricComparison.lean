module

public import HeightPaper.Probability.GeometricBranching

/-!
# Comparing geometric branching height tails

Increasing the geometric success probability decreases the height tail. The
uniform comparison constant here supplies the distributional tail estimates
in `lem:couplage`; coupling epidemic outgrowths to these laws remains separate.
-/

@[expose] public section

open MeasureTheory

namespace HeightPaper.Branching

theorem heightTail_nonneg (p : unitInterval) (h : ℕ) : 0 ≤ heightTail p h :=
  measureReal_nonneg

theorem heightTail_le_one (p : unitInterval) (h : ℕ) : heightTail p h ≤ 1 := by
  rw [heightTail_eq_one_sub]
  linarith [extinctionProbability_nonneg p h]

@[simp] theorem heightTail_zero (p : unitInterval) : heightTail p 0 = 1 := by
  rw [heightTail_eq_one_sub, extinctionProbability_zero, sub_zero]

/-- Tail recursion derived from the offspring construction. -/
theorem heightTail_succ {p : unitInterval} (hp : 0 < (p : ℝ)) (h : ℕ) :
    heightTail p (h + 1) = geometricMean p * heightTail p h /
      (1 + geometricMean p * heightTail p h) := by
  have hm : 0 ≤ geometricMean p := div_nonneg (sub_nonneg.mpr p.property.2) hp.le
  have hd : 0 < 1 + geometricMean p * heightTail p h := by
    have := mul_nonneg hm (heightTail_nonneg p h)
    linarith
  rw [heightTail_eq_one_sub p (h + 1), extinctionProbability_succ_mean hp]
  have heq : 1 + geometricMean p - geometricMean p * extinctionProbability p h =
      1 + geometricMean p * heightTail p h := by rw [heightTail_eq_one_sub]; ring
  rw [heq]
  field_simp
  ring

theorem geometricMean_antitone {p q : unitInterval} (hp : 0 < (p : ℝ))
    (hq : 0 < (q : ℝ)) (hpq : (p : ℝ) ≤ q) : geometricMean q ≤ geometricMean p := by
  rw [geometricMean_eq_inv_sub_one hp, geometricMean_eq_inv_sub_one hq]
  exact sub_le_sub_right (one_div_le_one_div_of_le hp hpq) 1

/-- The comparison is between actual generation probabilities, not independent
numerical tail sequences. -/
theorem heightTail_antitone_parameter {p q : unitInterval} (hp : 0 < (p : ℝ))
    (hq : 0 < (q : ℝ)) (hpq : (p : ℝ) ≤ q) (h : ℕ) : heightTail q h ≤ heightTail p h := by
  have hm := geometricMean_antitone hp hq hpq
  have hmp : 0 ≤ geometricMean p := div_nonneg (sub_nonneg.mpr p.property.2) hp.le
  have hmq : 0 ≤ geometricMean q := div_nonneg (sub_nonneg.mpr q.property.2) hq.le
  induction h with
  | zero => simp
  | succ h ih =>
      rw [heightTail_succ hp, heightTail_succ hq]
      have hprod := mul_le_mul hm ih (heightTail_nonneg q h) hmp
      have hdp : 0 < 1 + geometricMean p * heightTail p h := by
        have := mul_nonneg hmp (heightTail_nonneg p h)
        linarith
      have hdq : 0 < 1 + geometricMean q * heightTail q h := by
        have := mul_nonneg hmq (heightTail_nonneg q h)
        linarith
      exact (div_le_div_iff₀ hdq hdp).mpr (by nlinarith)

/-- The exponential tail comparison in `lem:couplage` for the two constructed
geometric branching laws. The constant depends only on their parameters. -/
theorem exists_uniform_tail_comparison {p q : unitInterval}
    (hp : 1 / 2 < (p : ℝ)) (hpq : (p : ℝ) ≤ q) (hq1 : (q : ℝ) < 1) :
    ∃ C > (0 : ℝ), ∀ h : ℕ,
      (1 / C) * (1 / (q : ℝ) - 1) ^ h ≤ heightTail q h ∧
      heightTail q h ≤ heightTail p h ∧
      heightTail p h ≤ C * (1 / (p : ℝ) - 1) ^ h := by
  have hp0 : 0 < (p : ℝ) := by linarith
  have hq : 1 / 2 < (q : ℝ) := hp.trans_le hpq
  have hq0 : 0 < (q : ℝ) := by linarith
  have hp1 : (p : ℝ) < 1 := hpq.trans_lt hq1
  have hmq := geometricMean_pos hq0 hq1
  have hmq1 := geometricMean_lt_one hq
  let C : ℝ := 1 / (1 - geometricMean q)
  have hCpos : 0 < C := one_div_pos.mpr (sub_pos.mpr hmq1)
  have hC : 1 ≤ C := (one_le_div (sub_pos.mpr hmq1)).mpr (by linarith)
  refine ⟨C, hCpos, fun h ↦ ?_⟩
  rw [← geometricMean_eq_inv_sub_one hp0, ← geometricMean_eq_inv_sub_one hq0]
  refine ⟨?_, heightTail_antitone_parameter hp0 hq0 hpq h, ?_⟩
  · simpa [C] using (heightTail_bounds hq hq1 h).1
  · apply (heightTail_bounds hp hp1 h).2.trans
    have hpow := pow_nonneg (geometricMean_pos hp0 hp1).le h
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) hpow]

end HeightPaper.Branching
