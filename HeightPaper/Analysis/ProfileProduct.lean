module

public import HeightPaper.Analysis.Parameters
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Real profile-product estimates

For positive real tilts, all normalizer factors are at least one. A global
quadratic logarithm remainder controls their product without a complex
logarithm or a zero-avoidance cutoff. The stochastic reciprocal-count sums
still have to be supplied when applying these estimates to an epidemic.
-/

@[expose] public section

open Filter Set
open scoped Topology BigOperators

namespace HeightPaper

/-- Global quadratic remainder for nonnegative factors. -/
theorem abs_log_one_add_sub_le_sq {x : ℝ} (hx : 0 ≤ x) :
    |Real.log (1 + x) - x| ≤ x ^ 2 := by
  have hupper := Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith)
  have hlower := Real.le_log_one_add_of_nonneg hx
  have hpoly : x - x ^ 2 ≤ 2 * x / (x + 2) := by
    apply (le_div_iff₀ (show 0 < x + 2 by linarith)).mpr
    nlinarith [mul_nonneg hx (sq_nonneg x)]
  rw [abs_le]
  constructor <;> linarith [sq_nonneg x]

/-- Finite real products differ from their linear logarithm sum by at most a
quadratic reciprocal-count sum. No small-factor restriction is needed. -/
theorem abs_log_prod_one_add_sub_le {ι : Type*} (S : Finset ι) (u : ι → ℝ)
    {a : ℝ} (ha : 0 ≤ a) (hu : ∀ i ∈ S, 0 ≤ u i) :
    |Real.log (∏ i ∈ S, (1 + a * u i)) - a * ∑ i ∈ S, u i| ≤
      a ^ 2 * ∑ i ∈ S, (u i) ^ 2 := by
  have hpos : ∀ i ∈ S, 0 < 1 + a * u i := by
    intro i hi
    have := mul_nonneg ha (hu i hi)
    linarith
  rw [Real.log_prod (fun i hi ↦ (hpos i hi).ne'), Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, |Real.log (1 + a * u i) - a * u i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, (a * u i) ^ 2 := Finset.sum_le_sum (fun i hi ↦
      abs_log_one_add_sub_le_sq (mul_nonneg ha (hu i hi)))
    _ = _ := by simp only [mul_pow, Finset.mul_sum]

/-- Two normalizers satisfy the moment-ratio logarithm estimate with an
explicit deterministic error. -/
theorem abs_log_prod_ratio_remainder_le {ι : Type*} (S : Finset ι) (u : ι → ℝ)
    {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : ∀ i ∈ S, 0 ≤ u i) :
    |Real.log (∏ i ∈ S, (1 + b * u i)) - p * Real.log (∏ i ∈ S, (1 + a * u i)) -
      (b - p * a) * ∑ i ∈ S, u i| ≤
        (b ^ 2 + |p| * a ^ 2) * ∑ i ∈ S, (u i) ^ 2 := by
  have ha' := abs_log_prod_one_add_sub_le S u ha hu
  have hb' := abs_log_prod_one_add_sub_le S u hb hu
  have heq : Real.log (∏ i ∈ S, (1 + b * u i)) - p * Real.log (∏ i ∈ S, (1 + a * u i)) -
      (b - p * a) * ∑ i ∈ S, u i =
      (Real.log (∏ i ∈ S, (1 + b * u i)) - b * ∑ i ∈ S, u i) -
        p * (Real.log (∏ i ∈ S, (1 + a * u i)) - a * ∑ i ∈ S, u i) := by ring
  rw [heq]
  have htri := abs_sub
    (Real.log (∏ i ∈ S, (1 + b * u i)) - b * ∑ i ∈ S, u i)
    (p * (Real.log (∏ i ∈ S, (1 + a * u i)) - a * ∑ i ∈ S, u i))
  rw [abs_mul] at htri
  have hmul := mul_le_mul_of_nonneg_left ha' (abs_nonneg p)
  nlinarith only [htri, hb', hmul]

/-- Transfer of deterministic reciprocal-sum limits to normalizer logarithms.
The two input limits remain explicit; this does not assert them for SIR paths. -/
theorem tendsto_log_prod_one_add_div {ι : Type*}
    (S : ℕ → Finset ι) (u : ℕ → ι → ℝ) (scale : ℕ → ℝ)
    {a γ : ℝ} (ha : 0 ≤ a) (hu : ∀ n i, i ∈ S n → 0 ≤ u n i)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hsum : Tendsto (fun n ↦ (∑ i ∈ S n, u n i) / scale n) atTop (𝓝 γ))
    (hsquare : Tendsto (fun n ↦ (∑ i ∈ S n, (u n i) ^ 2) / scale n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ Real.log (∏ i ∈ S n, (1 + a * u n i)) / scale n)
      atTop (𝓝 (a * γ)) := by
  have herror : Tendsto (fun n ↦
      (Real.log (∏ i ∈ S n, (1 + a * u n i)) - a * ∑ i ∈ S n, u n i) / scale n)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    have hb := hsquare.const_mul (a ^ 2)
    rw [mul_zero] at hb
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hb
    filter_upwards [hscale] with n hn
    rw [abs_div, abs_of_pos hn]
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (abs_log_prod_one_add_sub_le (S n) (u n) ha (hu n)) hn.le
  have ht := herror.add (hsum.const_mul a)
  rw [zero_add] at ht
  convert ht using 1
  funext n
  ring

end HeightPaper
