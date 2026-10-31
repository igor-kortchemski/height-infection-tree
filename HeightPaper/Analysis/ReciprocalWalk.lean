module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.PSeries

/-!
# Summable reciprocal errors for a walk with positive drift

These are the deterministic estimates in the proof of the reciprocal-walk
limit. They keep the same constants for an entire family of walks. Positive
source times `i = 1, …, n` are represented by `k + 1`, `k ∈ range n`, so no
reciprocal at time zero is added. Stochastic bounds for the envelopes `M` and
`Y` must be proved separately.
-/

@[expose] public section

open Filter
open scoped Topology BigOperators Classical

namespace HeightPaper

/-- The source's reciprocal error, indexed from the first positive time. -/
noncomputable def reciprocalWalkError (S : ℕ → ℝ) (d : ℝ) (k : ℕ) : ℝ :=
  1 / S (k + 1) - 1 / (d * (k + 1 : ℕ))

/-- Pointwise reciprocal comparison with exactly the source constant. -/
theorem abs_reciprocal_sub_linear_le {s d k M Y : ℝ}
    (hs : 0 < s) (hd : 0 < d) (hk : 0 < k) (hM : 0 ≤ M)
    (hratio : k / s ≤ M) (hdev : |s - d * k| ≤ Y * k ^ (3 / 4 : ℝ)) :
    |1 / s - 1 / (d * k)| ≤ d⁻¹ * M * Y * k ^ (-5 / 4 : ℝ) := by
  have hid : |1 / s - 1 / (d * k)| =
      d⁻¹ * (k / s) * |s - d * k| / k ^ 2 := by
    have heq : 1 / s - 1 / (d * k) = -(s - d * k) / (s * (d * k)) := by
      field_simp
      ring
    rw [heq, abs_div, abs_neg, abs_of_pos (mul_pos hs (mul_pos hd hk))]
    field_simp
  rw [hid]
  calc
    d⁻¹ * (k / s) * |s - d * k| / k ^ 2 ≤
        d⁻¹ * M * (Y * k ^ (3 / 4 : ℝ)) / k ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg k)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hratio (inv_nonneg.mpr hd.le)) hdev
        (abs_nonneg _) (mul_nonneg (inv_nonneg.mpr hd.le) hM)
    _ = d⁻¹ * M * Y * k ^ (-5 / 4 : ℝ) := by
      have hp : k ^ (-5 / 4 : ℝ) = k ^ (3 / 4 : ℝ) / k ^ 2 := by
        convert Real.rpow_sub_natCast hk.ne' (3 / 4 : ℝ) 2 using 1
        norm_num
      rw [hp]
      ring

/-- The common summable envelope, independent of the walk and its drift. -/
theorem summable_reciprocalWalk_envelope :
    Summable (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) :=
  (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num))

theorem abs_reciprocalWalkError_le (S : ℕ → ℝ) {d M Y : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M)
    (hpos : ∀ k, 0 < S (k + 1))
    (hratio : ∀ k, ((k + 1 : ℕ) : ℝ) / S (k + 1) ≤ M)
    (hdev : ∀ k, |S (k + 1) - d * (k + 1 : ℕ)| ≤
      Y * ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)) (k : ℕ) :
    |reciprocalWalkError S d k| ≤
      d⁻¹ * M * Y * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
  exact abs_reciprocal_sub_linear_le (hpos k) hd (by positivity) hM
    (hratio k) (hdev k)

/-- Multiplication by any weights of absolute value at most one preserves
both the envelope and the exact constant. Birth indicators are a special case. -/
theorem abs_weighted_reciprocalWalkError_le (S w : ℕ → ℝ) {d M Y : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M)
    (hpos : ∀ k, 0 < S (k + 1))
    (hratio : ∀ k, ((k + 1 : ℕ) : ℝ) / S (k + 1) ≤ M)
    (hdev : ∀ k, |S (k + 1) - d * (k + 1 : ℕ)| ≤
      Y * ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ))
    (hw : ∀ k, |w (k + 1)| ≤ 1) (k : ℕ) :
    |reciprocalWalkError S d k * w (k + 1)| ≤
      d⁻¹ * M * Y * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (hw k)).trans
    (abs_reciprocalWalkError_le S hd hM hpos hratio hdev k)

theorem summable_abs_weighted_reciprocalWalkError (S w : ℕ → ℝ) {d M Y : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M)
    (hpos : ∀ k, 0 < S (k + 1))
    (hratio : ∀ k, ((k + 1 : ℕ) : ℝ) / S (k + 1) ≤ M)
    (hdev : ∀ k, |S (k + 1) - d * (k + 1 : ℕ)| ≤
      Y * ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ))
    (hw : ∀ k, |w (k + 1)| ≤ 1) :
    Summable (fun k ↦ |reciprocalWalkError S d k * w (k + 1)|) := by
  apply (summable_reciprocalWalk_envelope.mul_left (d⁻¹ * M * Y)).of_norm_bounded
  intro k
  simpa only [Real.norm_eq_abs, abs_abs] using
    abs_weighted_reciprocalWalkError_le S w hd hM hpos hratio hdev hw k

theorem summable_weighted_reciprocalWalkError (S w : ℕ → ℝ) {d M Y : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M)
    (hpos : ∀ k, 0 < S (k + 1))
    (hratio : ∀ k, ((k + 1 : ℕ) : ℝ) / S (k + 1) ≤ M)
    (hdev : ∀ k, |S (k + 1) - d * (k + 1 : ℕ)| ≤
      Y * ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ))
    (hw : ∀ k, |w (k + 1)| ≤ 1) :
    Summable (fun k ↦ reciprocalWalkError S d k * w (k + 1)) := by
  exact (summable_abs_weighted_reciprocalWalkError S w hd hM hpos hratio hdev hw).of_abs

/-- Absolute bound for the limiting correction, with a common p-series for
all parameter values. The series is the positive-time version of ζ(5/4). -/
theorem abs_tsum_weighted_reciprocalWalkError_le (S w : ℕ → ℝ) {d M Y : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M)
    (hpos : ∀ k, 0 < S (k + 1))
    (hratio : ∀ k, ((k + 1 : ℕ) : ℝ) / S (k + 1) ≤ M)
    (hdev : ∀ k, |S (k + 1) - d * (k + 1 : ℕ)| ≤
      Y * ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ))
    (hw : ∀ k, |w (k + 1)| ≤ 1) :
    |∑' k, reciprocalWalkError S d k * w (k + 1)| ≤
      d⁻¹ * M * Y * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
  rw [← Real.norm_eq_abs]
  apply tsum_of_norm_bounded (summable_reciprocalWalk_envelope.hasSum.mul_left
    (d⁻¹ * M * Y))
  intro k
  simpa only [Real.norm_eq_abs] using
    abs_weighted_reciprocalWalkError_le S w hd hM hpos hratio hdev hw k

/-- The same bound for every tail. This quantitative form is what turns
uniform bounds for the random envelopes into weakly uniform convergence. -/
theorem abs_reciprocalWalkError_tail_le (S w : ℕ → ℝ) {d M Y : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M)
    (hpos : ∀ k, 0 < S (k + 1))
    (hratio : ∀ k, ((k + 1 : ℕ) : ℝ) / S (k + 1) ≤ M)
    (hdev : ∀ k, |S (k + 1) - d * (k + 1 : ℕ)| ≤
      Y * ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ))
    (hw : ∀ k, |w (k + 1)| ≤ 1) (n : ℕ) :
    |(∑' k, reciprocalWalkError S d k * w (k + 1)) -
      ∑ k ∈ Finset.range n, reciprocalWalkError S d k * w (k + 1)| ≤
      d⁻¹ * M * Y * ∑' k : ℕ, ((k + n + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
  have hs := summable_weighted_reciprocalWalkError S w hd hM hpos hratio hdev hw
  have heq : (∑' k, reciprocalWalkError S d k * w (k + 1)) -
      ∑ k ∈ Finset.range n, reciprocalWalkError S d k * w (k + 1) =
      ∑' k, reciprocalWalkError S d (k + n) * w (k + n + 1) := by
    have h := hs.sum_add_tsum_nat_add n
    linarith
  rw [heq]
  have htail : Summable (fun k : ℕ ↦ ((k + n + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) :=
    (summable_nat_add_iff n).mpr summable_reciprocalWalk_envelope
  rw [← Real.norm_eq_abs]
  apply tsum_of_norm_bounded (htail.hasSum.mul_left (d⁻¹ * M * Y))
  intro k
  simpa only [Real.norm_eq_abs] using
    abs_weighted_reciprocalWalkError_le S w hd hM hpos hratio hdev hw (k + n)

/-- The tail majorant vanishes independently of any walk or parameter. -/
theorem tendsto_reciprocalWalk_envelope_tail :
    Tendsto (fun n : ℕ ↦ ∑' k : ℕ,
      ((k + n + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) atTop (𝓝 0) :=
  tendsto_sum_nat_add (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ))

/-- Harmonic decomposition with the source's exact logarithmic centering. -/
theorem sum_weighted_reciprocal_centered_eq (S w : ℕ → ℝ) (d γ : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, w (k + 1) / S (k + 1)) - γ * Real.log n =
      (∑ k ∈ Finset.range n, reciprocalWalkError S d k * w (k + 1)) +
      (∑ k ∈ Finset.range n, (w (k + 1) / d - γ) / (k + 1 : ℕ)) +
      γ * ((harmonic n : ℝ) - Real.log n) := by
  have hh : (harmonic n : ℝ) = ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [hh, mul_sub, Finset.mul_sum, ← add_sub_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  dsimp [reciprocalWalkError]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Once the centered weighted harmonic series converges, the reciprocal
sum has its corrected limit, including γ times Euler--Mascheroni. -/
theorem tendsto_weighted_reciprocal_sub_log (S w : ℕ → ℝ) {d M Y γ Z' : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M)
    (hpos : ∀ k, 0 < S (k + 1))
    (hratio : ∀ k, ((k + 1 : ℕ) : ℝ) / S (k + 1) ≤ M)
    (hdev : ∀ k, |S (k + 1) - d * (k + 1 : ℕ)| ≤
      Y * ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ))
    (hw : ∀ k, |w (k + 1)| ≤ 1)
    (hcenter : Tendsto (fun n ↦ ∑ k ∈ Finset.range n,
      (w (k + 1) / d - γ) / (k + 1 : ℕ)) atTop (𝓝 Z')) :
    Tendsto (fun n ↦ (∑ k ∈ Finset.range n, w (k + 1) / S (k + 1)) -
      γ * Real.log n) atTop
      (𝓝 ((∑' k, reciprocalWalkError S d k * w (k + 1)) + Z' +
        γ * Real.eulerMascheroniConstant)) := by
  have hs := (summable_weighted_reciprocalWalkError S w hd hM hpos hratio hdev hw).hasSum.tendsto_sum_nat
  have ht := (hs.add hcenter).add (Real.tendsto_harmonic_sub_log.const_mul γ)
  exact ht.congr (fun n ↦ (sum_weighted_reciprocal_centered_eq S w d γ n).symm)

/-- A decreasing sequence of finite survival events stabilizes pathwise.
This statement includes the initial condition at time zero. -/
theorem eventually_finite_survival_iff (P : ℕ → Prop) :
    ∀ᶠ n : ℕ in atTop, (∀ i ≤ n, P i) ↔ ∀ i, P i := by
  classical
  by_cases h : ∀ i, P i
  · exact Eventually.of_forall (fun _ ↦ ⟨fun _ ↦ h, fun h i _ ↦ h i⟩)
  · obtain ⟨i, hi⟩ := not_forall.mp h
    filter_upwards [eventually_ge_atTop i] with n hn
    constructor
    · intro hall
      exact False.elim (hi (hall i hn))
    · intro hall j _
      exact hall j

/-- The reciprocal-series correction is zero away from infinite survival,
exactly as in the source's definition of `Z''`. -/
noncomputable def survivalReciprocalCorrection (S w : ℕ → ℝ) (d : ℝ) : ℝ :=
  if ∀ i, 0 < S i then ∑' k, reciprocalWalkError S d k * w (k + 1) else 0

/-- The source limit with its finite survival indicator and corrected
constant: `1_survival * (Z' + γ * EulerMascheroni) + Z''`. The stochastic
convergence of the centered harmonic series remains an explicit input. -/
theorem tendsto_survival_weighted_reciprocal_sub_log
    (S w : ℕ → ℝ) {d M Y γ Z' : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M)
    (hratio : (∀ i, 0 < S i) → ∀ k, ((k + 1 : ℕ) : ℝ) / S (k + 1) ≤ M)
    (hdev : (∀ i, 0 < S i) → ∀ k, |S (k + 1) - d * (k + 1 : ℕ)| ≤
      Y * ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ))
    (hw : ∀ k, |w (k + 1)| ≤ 1)
    (hcenter : Tendsto (fun n ↦ ∑ k ∈ Finset.range n,
      (w (k + 1) / d - γ) / (k + 1 : ℕ)) atTop (𝓝 Z')) :
    Tendsto (fun n ↦ (if ∀ i ≤ n, 0 < S i then (1 : ℝ) else 0) *
      ((∑ k ∈ Finset.range n, w (k + 1) / S (k + 1)) - γ * Real.log n))
      atTop (𝓝 ((if ∀ i, 0 < S i then (1 : ℝ) else 0) *
        (Z' + γ * Real.eulerMascheroniConstant) + survivalReciprocalCorrection S w d)) := by
  classical
  by_cases hsurv : ∀ i, 0 < S i
  · have ht := tendsto_weighted_reciprocal_sub_log S w hd hM
      (fun k ↦ hsurv (k + 1)) (hratio hsurv) (hdev hsurv) hw hcenter
    have hfinite (n : ℕ) : ∀ i ≤ n, 0 < S i := fun i _ ↦ hsurv i
    have heq : (fun n ↦ (if ∀ i ≤ n, 0 < S i then (1 : ℝ) else 0) *
        ((∑ k ∈ Finset.range n, w (k + 1) / S (k + 1)) - γ * Real.log n)) =
        (fun n ↦ (∑ k ∈ Finset.range n, w (k + 1) / S (k + 1)) - γ * Real.log n) := by
      funext n
      rw [ite_eq_left (hfinite n), one_mul]
    rw [heq, ite_eq_left hsurv, one_mul, survivalReciprocalCorrection, ite_eq_left hsurv]
    have hlimit : (∑' k, reciprocalWalkError S d k * w (k + 1)) + Z' +
        γ * Real.eulerMascheroniConstant = Z' + γ * Real.eulerMascheroniConstant +
          ∑' k, reciprocalWalkError S d k * w (k + 1) := by ring
    rwa [hlimit] at ht
  · have heq : (fun n ↦ (if ∀ i ≤ n, 0 < S i then (1 : ℝ) else 0) *
        ((∑ k ∈ Finset.range n, w (k + 1) / S (k + 1)) - γ * Real.log n)) =ᶠ[atTop]
        (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [eventually_finite_survival_iff (fun i ↦ 0 < S i)] with n hn
      simp only [hn, hsurv, ↓reduceIte, zero_mul]
    simpa only [hsurv, ↓reduceIte, zero_mul, survivalReciprocalCorrection, add_zero] using
      (tendsto_const_nhds.congr' heq.symm : Tendsto _ atTop (𝓝 (0 : ℝ)))

/-- Birth-event weights, with the same time index as `S`. -/
def walkBirthIndicator (births : ℕ → Bool) (i : ℕ) : ℝ :=
  if births i then 1 else 0

theorem abs_walkBirthIndicator_le_one (births : ℕ → Bool) (i : ℕ) :
    |walkBirthIndicator births i| ≤ 1 := by
  unfold walkBirthIndicator
  split <;> norm_num

/-- Birth-indicator specialization of the centered reciprocal-walk limit.
The limit keeps both the survival multiplier and the Euler--Mascheroni shift. -/
theorem tendsto_survival_birth_reciprocal_sub_log
    (S : ℕ → ℝ) (births : ℕ → Bool) {d M Y γ Z' : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M)
    (hratio : (∀ i, 0 < S i) → ∀ k, ((k + 1 : ℕ) : ℝ) / S (k + 1) ≤ M)
    (hdev : (∀ i, 0 < S i) → ∀ k, |S (k + 1) - d * (k + 1 : ℕ)| ≤
      Y * ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ))
    (hcenter : Tendsto (fun n ↦ ∑ k ∈ Finset.range n,
      (walkBirthIndicator births (k + 1) / d - γ) / (k + 1 : ℕ)) atTop (𝓝 Z')) :
    Tendsto (fun n ↦ (if ∀ i ≤ n, 0 < S i then (1 : ℝ) else 0) *
      ((∑ k ∈ Finset.range n, walkBirthIndicator births (k + 1) / S (k + 1)) -
        γ * Real.log n)) atTop
      (𝓝 ((if ∀ i, 0 < S i then (1 : ℝ) else 0) *
        (Z' + γ * Real.eulerMascheroniConstant) +
        survivalReciprocalCorrection S (walkBirthIndicator births) d)) :=
  tendsto_survival_weighted_reciprocal_sub_log S (walkBirthIndicator births)
    hd hM hratio hdev (fun k ↦ abs_walkBirthIndicator_le_one births (k + 1)) hcenter

end HeightPaper
