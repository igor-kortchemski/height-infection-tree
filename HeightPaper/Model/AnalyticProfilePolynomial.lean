module

public import HeightPaper.Model.AnalyticProfileLimit

/-!
# An analytic version from the explicit profile power bounds

The count and normalizer estimates give geometric moment tails along dyadic
times. Cauchy's formula then produces one locally uniform analytic limit on
the actual prescribed-tree trajectory law.
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology BigOperators ENNReal

namespace HeightPaper.Model

theorem summable_dyadic_moment_root {C q p : ℝ} (hC : 0 ≤ C)
    (hq : q < 0) (hp : 0 < p) :
    Summable (fun m : ℕ => (C * ((2 : ℝ) ^ m) ^ q) ^ p⁻¹) := by
  have hratio : (2 : ℝ) ^ (q * p⁻¹) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (mul_neg_of_neg_of_pos hq (inv_pos.mpr hp))
  have hs := (summable_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hratio).mul_left (C ^ p⁻¹)
  convert hs using 1
  ext m
  rw [Real.mul_rpow hC (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]

/-- The concrete moment-tail interface used by the local count-word law. -/
theorem prescribedTrajectory_exists_analytic_dyadic_limit_of_moment_decay
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) (z₀ : ℂ) {R : ℝ} (hR : 0 < R)
    (hC : ∀ k ≥ J, ∀ z ∈ closedBall z₀ R,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0)
    {p D η : ℝ} (hp : 1 ≤ p) (hD : 0 ≤ D) (hη : 0 < η)
    (hbound : ∀ j k : ℕ, J ≤ j → 1 ≤ j → j ≤ k → ∀ z ∈ sphere z₀ R,
      (∫ ω, ‖prescribedNormalizedProfile (Complex.exp z) events s₀ J k (ω k) -
          prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)‖ ^ p
        ∂prescribedTrajectoryMeasure events s₀) ≤ D * (j : ℝ) ^ (-η)) :
    ∃ L : (ℕ → State) → ℂ → ℂ,
      ∀ᵐ ω ∂prescribedTrajectoryMeasure events s₀,
        ∀ r : ℝ, 0 ≤ r → r < R →
          TendstoUniformlyOn
            (fun m z => prescribedNormalizedProfile (Complex.exp z) events s₀ J
              (J + 2 ^ m) (ω (J + 2 ^ m))) (L ω) atTop (closedBall z₀ r) ∧
            DifferentiableOn ℂ (L ω) (ball z₀ r) := by
  have htimes : Monotone (fun m : ℕ => J + 2 ^ m) := by
    intro i j hij
    exact Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) hij) J
  apply prescribedTrajectory_exists_analytic_sequence_limit_of_moments events s₀ J
    z₀ hR (fun m => J + 2 ^ m) htimes (fun _ => Nat.le_add_right _ _) hC hp
    (fun m => D * ((2 : ℝ) ^ m) ^ (-η))
    (summable_dyadic_moment_root hD (neg_neg_of_pos hη) (lt_of_lt_of_le zero_lt_one hp))
  intro m z hz
  have hj : 1 ≤ J + 2 ^ m := Nat.one_le_two_pow.trans (Nat.le_add_left _ _)
  refine (hbound _ _ (Nat.le_add_right _ _) hj (htimes (Nat.le_succ m)) z hz).trans ?_
  apply mul_le_mul_of_nonneg_left _ hD
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hη.le)
  exact_mod_cast Nat.le_add_left (2 ^ m) J

/-- Uniform deterministic power bounds on a surrounding circle produce a
common analytic limit along `J + 2^m`, uniformly on every smaller disk. -/
theorem prescribedTrajectory_exists_analytic_dyadic_limit_of_polynomial
    {p A B c a b W : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hA : 0 < A) (hB : 0 ≤ B) (hc : 0 < c) (hW : 0 ≤ W)
    (hexp : b - p * (a + 1) < -1)
    (events : ℕ → Bool) (n J : ℕ) (z₀ : ℂ) {R : ℝ} (hR : 0 < R)
    (hpos : ∀ i, 0 < prescribedWalk events 1 i)
    (hC : ∀ k ≥ J, ∀ z ∈ closedBall z₀ R,
      prescribedNormalizerFrom (Complex.exp z) events 1 J k ≠ 0)
    (hw : ∀ z ∈ sphere z₀ R, 1 ≤ ‖Complex.exp z‖ ∧ ‖Complex.exp z‖ ≤ W)
    (hClower : ∀ z ∈ sphere z₀ R, ∀ k ≥ J,
      A * ((k + 1 : ℕ) : ℝ) ^ a ≤
        ‖prescribedNormalizerFrom (Complex.exp z) events 1 J (k + 1)‖)
    (hCupper : ∀ z ∈ sphere z₀ R, ∀ k ≥ J,
      realNormalizer (‖Complex.exp z‖ ^ p) events 1 k ≤ B * ((k + 1 : ℕ) : ℝ) ^ b)
    (hcount : ∀ k ≥ J, c * (k + 1 : ℕ) ≤ (prescribedWalk events 1 (k + 1) : ℝ)) :
    ∃ L : (ℕ → State) → ℂ → ℂ,
      ∀ᵐ ω ∂prescribedTrajectoryMeasure events (initial n),
        ∀ r : ℝ, 0 ≤ r → r < R →
          TendstoUniformlyOn
            (fun m z => prescribedNormalizedProfile (Complex.exp z) events (initial n) J
              (J + 2 ^ m) (ω (J + 2 ^ m))) (L ω) atTop (closedBall z₀ r) ∧
            DifferentiableOn ℂ (L ω) (ball z₀ r) := by
  let q : ℝ := b - p * (a + 1) + 1
  let C : ℝ := (4 * (2 : ℝ) ^ p) *
    ((W / (A * c)) ^ p * (2 : ℝ) ^ p * B) / (-(b - p * (a + 1)) - 1)
  have hq : q < 0 := by dsimp [q]; linarith
  have hden : 0 < -(b - p * (a + 1)) - 1 := by linarith
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have htimes : Monotone (fun m : ℕ => J + 2 ^ m) := by
    intro i j hij
    exact Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) hij) J
  apply prescribedTrajectory_exists_analytic_sequence_limit_of_moments events (initial n) J
    z₀ hR (fun m => J + 2 ^ m) htimes (fun _ => Nat.le_add_right _ _)
    (by simpa only [infectious_initial] using hC) hp.le
    (fun m => C * ((2 : ℝ) ^ m) ^ q)
    (summable_dyadic_moment_root hC0 hq (by linarith))
  intro m z hz
  let j := J + 2 ^ m
  let N := J + 2 ^ (m + 1)
  have hJj : J ≤ j := Nat.le_add_right _ _
  have hj : 1 ≤ j := Nat.one_le_two_pow.trans (Nat.le_add_left _ _)
  have hjN : j ≤ N := htimes (Nat.le_succ m)
  have hm := prescribedPath_complex_moment_polynomial_le
    (hw z hz).1 hp hp2 hA hB hc hexp events n N J j hJj hj hjN
    (fun i _ => hpos i) (hC N (hJj.trans hjN) z (sphere_subset_closedBall hz))
    (fun k hk => hClower z hz k (hJj.trans (Finset.mem_Ico.mp hk).1))
    (fun k hk => hCupper z hz k (hJj.trans (Finset.mem_Ico.mp hk).1))
    (fun k hk => hcount k (hJj.trans (Finset.mem_Ico.mp hk).1))
  have heq := kernelTrajectory_integral_prefix (fun i => prescribedStep (events i))
    (initial n) N (fun t =>
      ‖prescribedNormalizedProfile (Complex.exp z) events (initial n) J N t.last -
        prescribedNormalizedProfile (Complex.exp z) events (initial n) J j (t.eval j)‖ ^ p)
  simp only [trajectoryPrefix_last, trajectoryPrefix_eval N _ j hjN] at heq
  change _ ≤ C * ((2 : ℝ) ^ m) ^ q
  simp only [prescribedTrajectoryMeasure]
  rw [heq]
  simp only [prescribedNormalizedProfile, infectious_initial]
  refine hm.trans ?_
  have hnorm : (‖Complex.exp z‖ / (A * c)) ^ p ≤ (W / (A * c)) ^ p :=
    Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_right (hw z hz).2 (mul_pos hA hc).le) (by linarith)
  have hjpow : (j : ℝ) ^ q ≤ ((2 : ℝ) ^ m) ^ q := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ hq.le
    exact_mod_cast Nat.le_add_left (2 ^ m) J
  calc
    _ ≤ (4 * (2 : ℝ) ^ p) * ((W / (A * c)) ^ p * (2 : ℝ) ^ p * B) *
        ((j : ℝ) ^ q / (-(b - p * (a + 1)) - 1)) := by
      gcongr
    _ = C * (j : ℝ) ^ q := by dsimp [C]; ring
    _ ≤ C * ((2 : ℝ) ^ m) ^ q := mul_le_mul_of_nonneg_left hjpow hC0

end HeightPaper.Model
