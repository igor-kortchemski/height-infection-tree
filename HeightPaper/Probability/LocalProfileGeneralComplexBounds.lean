module

public import HeightPaper.Probability.LocalProfileMoments
public import HeightPaper.Model.ProfileCutoffMoment

/-!
# Polynomial normalizer bounds throughout the complex source half-plane

The safe cutoff controls complex products for real weights below one as well
as above one. The common logarithmic envelope is independent of the tilt.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology NNReal BigOperators

namespace HeightPaper.CountCoupling

open Model

theorem localProfile_complex_polynomial_upper {l M B : ℝ} (hl : 1 < l)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (u : ℕ → ℝ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hcut : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B)
    (z : ℂ) (hz : z.re < 2 * profileRoot l)
    {k : ℕ} (hk : localSafeCutoff l u ≤ k) :
    ‖prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1
        (localSafeCutoff l u) (k + 1)‖ ≤
      Real.exp (localProfileLogEnvelope l u M B) *
        ((k + 1 : ℕ) : ℝ) ^ (growthFactor l * ((Complex.exp z).re - 1)) := by
  have hcenter' := Model.birthReciprocal_Ico_centered_bound (localBirth l u) 1
    (localSafeCutoff l u) (k + 1) (localSafeCutoff l u) (by omega) le_rfl
    (by
      have heq : Model.birthReciprocal (localBirth l u) 1 = localBirthCoefficient l u :=
        funext (fun i ↦ (localBirthCoefficient_eq_model l u hs i).symm)
      simpa only [heq] using hcenter (k + 1))
  have hsquare := Model.birthReciprocal_Ico_square_bound (localBirth l u) 1
    (localSafeCutoff l u) (k + 1) (M := M) (fun i _ ↦ by
      rw [← localBirthCoefficient_eq_model l u hs]
      exact localBirthCoefficient_le_linear l u hM hs hr i)
  have hsmall : ∀ i ∈ Finset.Ico (localSafeCutoff l u) (k + 1),
      localNormalizerRadius l * Model.birthReciprocal (localBirth l u) 1 i ≤ 1 / 2 := by
    intro i hi
    rw [← localBirthCoefficient_eq_model l u hs]
    simpa only [abs_of_nonneg (localBirthCoefficient_nonneg l u hs i)] using
      localBirthCoefficient_safe_after l u hs hcut (Finset.mem_Ico.mp hi).1
  have hh := (Model.normalizerFrom_polynomial_bounds (localBirth l u) 1
    (localSafeCutoff l u) (k + 1) (γ := growthFactor l) (t := (k + 1 : ℕ))
    (localNormalizerRadius_pos l).le (by positivity) hsmall hcenter' hsquare
    (Complex.exp z) (norm_exp_sub_one_lt_localNormalizerRadius z hz).le).2
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  apply Real.exp_le_exp.mpr
  unfold localProfileLogEnvelope
  have hR := localNormalizerRadius_le hl
  have hR0 := (localNormalizerRadius_pos l).le
  gcongr

theorem realNormalizerFrom_succ (v : ℝ) (events : ℕ → Bool) (i₀ : ℕ)
    {J k : ℕ} (hJk : J ≤ k) :
    realNormalizerFrom v events i₀ J (k + 1) =
      realNormalizerFrom v events i₀ J k *
        (1 + (v - 1) * birthReciprocal events i₀ k) := by
  exact Finset.prod_Ico_succ_top hJk _

theorem realNormalizerFrom_le_two_succ {v : ℝ} (hv : 0 ≤ v)
    (events : ℕ → Bool) (i₀ : ℕ) {J k : ℕ} (hJk : J ≤ k)
    (hb : birthReciprocal events i₀ k ≤ 1 / 2) :
    realNormalizerFrom v events i₀ J k ≤
      2 * realNormalizerFrom v events i₀ J (k + 1) := by
  have hnonneg := realNormalizerFrom_nonneg hv events i₀ J k
  have hb0 := birthReciprocal_nonneg events i₀ k
  have hfactor : (1 / 2 : ℝ) ≤ 1 + (v - 1) * birthReciprocal events i₀ k := by
    nlinarith [mul_nonneg hv hb0]
  rw [realNormalizerFrom_succ v events i₀ hJk]
  nlinarith

theorem realNormalizer_nonneg {v : ℝ} (hv : 0 ≤ v)
    (events : ℕ → Bool) (i₀ k : ℕ) :
    0 ≤ realNormalizer v events i₀ k := by
  simpa only [realNormalizer, realNormalizerFrom, Nat.Ico_zero_eq_range] using
    realNormalizerFrom_nonneg hv events i₀ 0 k

theorem norm_prescribedIncrementCoeff_complex_le_max (w : ℂ)
    (events : ℕ → Bool) (i₀ J k : ℕ) (hJk : J ≤ k)
    (hi : 0 < prescribedWalk events i₀ (k + 1)) :
    ‖prescribedIncrementCoeff w (prescribedNormalizerFrom w events i₀ J k)
      (events k) (prescribedWalk events i₀ k)‖ ≤
      max 1 ‖w‖ / (‖prescribedNormalizerFrom w events i₀ J (k + 1)‖ *
        (prescribedWalk events i₀ (k + 1) : ℝ)) := by
  rw [prescribedIncrementCoeff_eq_next _ _ _ _ hi,
    ← prescribedNormalizerFrom_succ w events i₀ hJk]
  rw [norm_div, norm_mul, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  cases events k <;> simp [le_max_left, le_max_right]

theorem prescribedShiftedMomentBound_complex_le_max (w : ℂ)
    {p : ℝ} (hp : 0 ≤ p) (events : ℕ → Bool) (n J k : ℕ) (hJk : J ≤ k)
    (hi : 0 < prescribedWalk events 1 (k + 1)) :
    prescribedShiftedMomentBound w events (initial n) J p k ≤
      ((max 1 ‖w‖ / (‖prescribedNormalizerFrom w events 1 J (k + 1)‖ *
        (prescribedWalk events 1 (k + 1) : ℝ))) ^ p * (2 : ℝ) ^ p) *
        realNormalizer (‖w‖ ^ p) events 1 k := by
  have hwp : 0 ≤ ‖w‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  simp only [prescribedShiftedMomentBound, infectious_initial,
    normalizedActiveWeight_initial, one_mul, prescribedNormalizer_ofReal, Complex.ofReal_re]
  apply mul_le_mul_of_nonneg_right _ (realNormalizer_nonneg hwp events 1 k)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
  exact Real.rpow_le_rpow (norm_nonneg _)
    (norm_prescribedIncrementCoeff_complex_le_max w events 1 J k hJk hi) hp

theorem localProfile_real_polynomial_upper_all {l M B : ℝ} (hl : 1 < l)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (u : ℕ → ℝ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hcut : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B)
    (z : ℂ) (hz : z.re < profileRoot l) {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (k : ℕ) (hk : localSafeCutoff l u ≤ k) :
    realNormalizer (‖Complex.exp z‖ ^ p) (localBirth l u) 1 k ≤
      2 * (max 1 (‖Complex.exp z‖ ^ p)) ^ (localSafeCutoff l u) *
        Real.exp (localProfileLogEnvelope l u M B) *
        ((k + 1 : ℕ) : ℝ) ^
          (growthFactor l * (Real.exp (p * z.re) - 1)) := by
  let J := localSafeCutoff l u
  let v := ‖Complex.exp z‖ ^ p
  have hv : 0 ≤ v := Real.rpow_nonneg (norm_nonneg _) _
  have hJ : J ≤ k := hk
  have hz' : p * z.re < 2 * profileRoot l := by
    by_cases hx : 0 ≤ z.re
    · have hmul := mul_le_mul_of_nonneg_right hp2 hx
      linarith
    · have hp0 : 0 ≤ p := zero_le_one.trans hp
      have hmul := mul_nonpos_of_nonneg_of_nonpos hp0 (le_of_lt (lt_of_not_ge hx))
      linarith [profileRoot_pos hl]
  have hw : Complex.exp ((p * z.re : ℝ) : ℂ) = (v : ℂ) := by
    dsimp [v]
    rw [← Complex.ofReal_exp, Complex.norm_exp, ← Real.exp_mul]
    congr 1
    ring
  have hreal : ‖prescribedNormalizerFrom
      (Complex.exp ((p * z.re : ℝ) : ℂ)) (localBirth l u) 1 J (k + 1)‖ =
      realNormalizerFrom v (localBirth l u) 1 J (k + 1) := by
    rw [hw, prescribedNormalizerFrom_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (realNormalizerFrom_nonneg hv _ _ _ _)]
  have hupper := localProfile_complex_polynomial_upper hl hM hB u hs hr hcut
    hcenter ((p * z.re : ℝ) : ℂ) (by simpa only [Complex.ofReal_re] using hz') hk
  rw [hreal] at hupper
  simp only [← Complex.ofReal_exp, Complex.ofReal_re] at hupper
  have hb : birthReciprocal (localBirth l u) 1 k ≤ 1 / 2 := by
    have hh := localBirthCoefficient_safe_after l u hs hcut hk
    rw [localBirthCoefficient_eq_model l u hs] at hh
    have hR : 1 ≤ localNormalizerRadius l := by
      unfold localNormalizerRadius
      have he := Real.exp_pos (2 * profileRoot l)
      linarith
    have hcoeff := birthReciprocal_nonneg (localBirth l u) 1 k
    rw [abs_of_nonneg hcoeff] at hh
    nlinarith [mul_le_mul_of_nonneg_right hR hcoeff]
  have hnext := realNormalizerFrom_le_two_succ hv (localBirth l u) 1 hJ hb
  have hpref := realNormalizer_le_max_pow hv (localBirth l u) 1 J
  have hfrom := realNormalizerFrom_nonneg hv (localBirth l u) 1 J k
  rw [realNormalizer_split v (localBirth l u) 1 hJ]
  calc
    realNormalizer v (localBirth l u) 1 J *
        realNormalizerFrom v (localBirth l u) 1 J k ≤
      (max 1 v) ^ J * realNormalizerFrom v (localBirth l u) 1 J k :=
        mul_le_mul_of_nonneg_right hpref hfrom
    _ ≤ (max 1 v) ^ J * (2 * realNormalizerFrom v (localBirth l u) 1 J (k + 1)) :=
      mul_le_mul_of_nonneg_left hnext (by positivity)
    _ ≤ (max 1 v) ^ J * (2 * (Real.exp (localProfileLogEnvelope l u M B) *
        ((k + 1 : ℕ) : ℝ) ^
          (growthFactor l * (Real.exp (p * z.re) - 1)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hupper (by norm_num)) (by positivity)
    _ = _ := by dsimp [J, v]; ring

/-- Polynomial control of the shifted increment series without a sign
restriction on the real part of the complex tilt. -/
theorem prescribedShiftedMomentBound_summable_complex_all {w : ℂ}
    {p A B c a b : ℝ} (hp : 1 < p)
    (hA : 0 < A) (hB : 0 ≤ B) (hc : 0 < c)
    (hexp : b - p * (a + 1) < -1)
    (events : ℕ → Bool) (n J : ℕ)
    (hpos : ∀ i, 0 < prescribedWalk events 1 i)
    (hC : ∀ k ≥ J, prescribedNormalizerFrom w events 1 J k ≠ 0)
    (hClower : ∀ k ≥ J,
      A * ((k + 1 : ℕ) : ℝ) ^ a ≤ ‖prescribedNormalizerFrom w events 1 J (k + 1)‖)
    (hCupper : ∀ k ≥ J,
      realNormalizer (‖w‖ ^ p) events 1 k ≤ B * ((k + 1 : ℕ) : ℝ) ^ b)
    (hcount : ∀ k ≥ J,
      c * (k + 1 : ℕ) ≤ (prescribedWalk events 1 (k + 1) : ℝ)) :
    Summable (fun i ↦ prescribedShiftedMomentBound w events (initial n) J p (J + i)) := by
  have hp0 : 0 ≤ p := by linarith
  have hwp : 0 ≤ ‖w‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  have hnonneg (i : ℕ) :
      0 ≤ prescribedShiftedMomentBound w events (initial n) J p (J + i) := by
    apply prescribedShiftedMomentBound_nonneg w events (initial n) J (J + i)
      (Nat.le_add_right J i) hp.le
    · simpa only [infectious_initial] using (fun k (_ : k ≤ J + i + 1) ↦ hpos k)
    · simpa only [infectious_initial] using hC (J + i + 1) (by omega)
  have hbound (i : ℕ) :
      prescribedShiftedMomentBound w events (initial n) J p (J + i) ≤
        ((max 1 ‖w‖ / (A * c)) ^ p * (2 : ℝ) ^ p * B) *
          ((J + i + 1 : ℕ) : ℝ) ^ (b - p * (a + 1)) := by
    apply (prescribedShiftedMomentBound_complex_le_max w hp0 events n J (J + i)
      (Nat.le_add_right J i) (hpos (J + i + 1))).trans
    exact profile_moment_ratio_le (le_max_of_le_left (by norm_num)) hp0 hA hB hc
      (by positivity) (realNormalizer_nonneg hwp events 1 (J + i))
      (hClower (J + i) (Nat.le_add_right J i))
      (hcount (J + i) (Nat.le_add_right J i))
      (hCupper (J + i) (Nat.le_add_right J i))
  have hpow := (Real.summable_nat_rpow.mpr hexp).comp_injective
    (show Function.Injective (fun i : ℕ ↦ J + i + 1) from fun i j h ↦ by dsimp at h; omega)
  exact Summable.of_nonneg_of_le hnonneg hbound
    (hpow.mul_left ((max 1 ‖w‖ / (A * c)) ^ p * (2 : ℝ) ^ p * B))

/-- Pointwise almost-sure and Lp convergence under polynomial bounds on the
entire complex source half-plane. -/
theorem prescribedTrajectory_exists_profile_lp_limit_complex_all {w : ℂ}
    {p A B c a b : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hA : 0 < A) (hB : 0 ≤ B) (hc : 0 < c)
    (hexp : b - p * (a + 1) < -1)
    (events : ℕ → Bool) (n J : ℕ)
    (hpos : ∀ i, 0 < prescribedWalk events 1 i)
    (hC : ∀ k ≥ J, prescribedNormalizerFrom w events 1 J k ≠ 0)
    (hClower : ∀ k ≥ J,
      A * ((k + 1 : ℕ) : ℝ) ^ a ≤ ‖prescribedNormalizerFrom w events 1 J (k + 1)‖)
    (hCupper : ∀ k ≥ J,
      realNormalizer (‖w‖ ^ p) events 1 k ≤ B * ((k + 1 : ℕ) : ℝ) ^ b)
    (hcount : ∀ k ≥ J,
      c * (k + 1 : ℕ) ≤ (prescribedWalk events 1 (k + 1) : ℝ)) :
    ∃ F : (ℕ → State) → ℂ, Measurable F ∧
      MemLp F (ENNReal.ofReal p) (prescribedTrajectoryMeasure events (initial n)) ∧
      (∀ᵐ ω ∂prescribedTrajectoryMeasure events (initial n),
        Tendsto (fun k ↦ prescribedNormalizedProfile w events (initial n) J
          (J + k) (ω (J + k))) atTop (𝓝 (F ω))) ∧
      Tendsto (fun k ↦ eLpNorm
        ((fun ω ↦ prescribedNormalizedProfile w events (initial n) J
          (J + k) (ω (J + k))) - F)
        (ENNReal.ofReal p) (prescribedTrajectoryMeasure events (initial n)))
        atTop (𝓝 0) := by
  apply prescribedTrajectory_exists_profile_lp_limit w events (initial n) J hp hp2
  · simpa only [infectious_initial] using hpos
  · simpa only [infectious_initial] using hC
  · exact prescribedShiftedMomentBound_summable_complex_all hp hA hB hc hexp
      events n J hpos hC hClower hCupper hcount

/-- Almost every local event word has one set of reciprocal, cutoff, and
logarithmic controls, simultaneously for all complex tilts. -/
theorem localProfile_ae_raw_controls_all {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
      ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
        (∀ k, positiveReciprocal l u k ≤ M) ∧
        BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
          1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)} ∧
        ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
          growthFactor l * Real.log k| ≤ B := by
  filter_upwards [ae_tendsto_finiteLocalCenteredReciprocal hl,
    positiveReciprocal_ae_uniform_bounded hl, localSafeCutoff_ae_bddAbove hl]
    with u hconv hratio hcut
  intro hs
  obtain ⟨M₀, hM₀⟩ := hratio
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hr : ∀ k, positiveReciprocal l u k ≤ M :=
    fun k ↦ (hM₀ l le_rfl k).trans (le_max_left _ _)
  obtain ⟨B₀, hB₀, hBbound⟩ :=
    (Metric.isBounded_range_of_tendsto _ hconv).exists_pos_norm_le
  have hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B₀ := by
    intro k
    have hh := hBbound (finiteLocalCenteredReciprocal l u k) ⟨k, rfl⟩
    simpa only [Real.norm_eq_abs, finiteLocalCenteredReciprocal, localBirthCoefficient,
      ite_eq_left (show ∀ i ≤ k, 0 < (localWalk l u i : ℝ) from fun i _ ↦ hs i),
      one_mul, growthFactor] using hh
  exact ⟨M, B₀, hM, hB₀.le, hr, hcut, hcenter⟩

/-- The actual infinite prescribed tree has a pointwise complex profile limit
throughout the source moment domain, including negative real tilts. -/
theorem localProfile_ae_exists_lp_limit_complex_all {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
      ∀ (n : ℕ) (z : ℂ) (p : ℝ), z.re < profileRoot l →
        1 < p → p ≤ 2 → complexProfileMomentExponent l z p < -1 →
        ∃ F : (ℕ → State) → ℂ, Measurable F ∧
          MemLp F (ENNReal.ofReal p)
            (prescribedTrajectoryMeasure (localBirth l u) (initial n)) ∧
          (∀ᵐ ω ∂prescribedTrajectoryMeasure (localBirth l u) (initial n),
            Tendsto (fun k ↦ prescribedNormalizedProfile (Complex.exp z)
              (localBirth l u) (initial n) (localSafeCutoff l u)
              (localSafeCutoff l u + k) (ω (localSafeCutoff l u + k)))
              atTop (𝓝 (F ω))) ∧
          Tendsto (fun k ↦ eLpNorm
            ((fun ω ↦ prescribedNormalizedProfile (Complex.exp z)
              (localBirth l u) (initial n) (localSafeCutoff l u)
              (localSafeCutoff l u + k) (ω (localSafeCutoff l u + k))) - F)
            (ENNReal.ofReal p) (prescribedTrajectoryMeasure (localBirth l u) (initial n)))
            atTop (𝓝 0) := by
  filter_upwards [localProfile_ae_raw_controls_all hl] with u hu
  intro hs n z p hz hp hp2 hexp
  obtain ⟨M, B, hM, hB, hr, hcut, hcenter⟩ := hu hs
  let J := localSafeCutoff l u
  let E := localProfileLogEnvelope l u M B
  let A := Real.exp (-E)
  let D := 2 * (max 1 (‖Complex.exp z‖ ^ p)) ^ J * Real.exp E
  let c := 1 / (M + 1)
  have hpos : ∀ i, 0 < prescribedWalk (localBirth l u) 1 i := by
    intro i
    apply prescribedWalk_local_pos (H := i) _ le_rfl
    intro j _
    exact_mod_cast hs j
  have hC : ∀ k ≥ J,
      prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1 J k ≠ 0 := by
    intro k hk
    rw [localNormalizer_eq_exp_centered l u hs hcut k z
      (by linarith [profileRoot_pos hl])]
    exact Complex.exp_ne_zero _
  have hClower : ∀ k ≥ J,
      A * ((k + 1 : ℕ) : ℝ) ^ (growthFactor l * ((Complex.exp z).re - 1)) ≤
        ‖prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1 J (k + 1)‖ := by
    intro k hk
    exact localProfile_complex_polynomial_lower hl hM hB u hs hr hcut hcenter z
      (by linarith [profileRoot_pos hl]) hk
  have hCupper : ∀ k ≥ J,
      realNormalizer (‖Complex.exp z‖ ^ p) (localBirth l u) 1 k ≤
        D * ((k + 1 : ℕ) : ℝ) ^
          (growthFactor l * (Real.exp (p * z.re) - 1)) := by
    intro k hk
    exact localProfile_real_polynomial_upper_all hl hM hB u hs hr hcut hcenter z
      hz hp.le hp2 k hk
  have hcount : ∀ k ≥ J,
      c * (k + 1 : ℕ) ≤ (prescribedWalk (localBirth l u) 1 (k + 1) : ℝ) := by
    intro k _
    exact localProfile_count_lower l u hM hs hr k
  have he : growthFactor l * (Real.exp (p * z.re) - 1) -
      p * (growthFactor l * ((Complex.exp z).re - 1) + 1) < -1 := by
    convert hexp using 1
    unfold complexProfileMomentExponent
    ring
  exact prescribedTrajectory_exists_profile_lp_limit_complex_all hp hp2
    (Real.exp_pos _) (by dsimp [D]; positivity) (by dsimp [c]; positivity)
    he (localBirth l u) n J hpos hC hClower hCupper hcount

theorem max_norm_exp_rpow_le_exp_two {l : ℝ} (hl : 1 < l)
    {z : ℂ} (hz : z.re < profileRoot l) {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    max 1 (‖Complex.exp z‖ ^ p) ≤ Real.exp 2 := by
  have hpre : p * z.re ≤ 2 := by
    by_cases hx : 0 ≤ z.re
    · have hh := mul_le_mul_of_nonneg_right hp2 hx
      nlinarith [profileRoot_lt_one hl]
    · have hp0 : 0 ≤ p := zero_le_one.trans hp
      have hh := mul_nonpos_of_nonneg_of_nonpos hp0 (le_of_lt (lt_of_not_ge hx))
      linarith
  rw [Complex.norm_exp, ← Real.exp_mul]
  apply max_le
  · exact Real.one_le_exp_iff.mpr (by norm_num)
  · exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hpre)

theorem localProfile_real_polynomial_upper_uniform {l M B : ℝ} (hl : 1 < l)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (u : ℕ → ℝ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hcut : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B)
    (z : ℂ) (hz : z.re < profileRoot l) {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (k : ℕ) (hk : localSafeCutoff l u ≤ k) :
    realNormalizer (‖Complex.exp z‖ ^ p) (localBirth l u) 1 k ≤
      (2 * (Real.exp 2) ^ (localSafeCutoff l u) *
        Real.exp (localProfileLogEnvelope l u M B)) *
        ((k + 1 : ℕ) : ℝ) ^
          (growthFactor l * (Real.exp (p * z.re) - 1)) := by
  have hh := localProfile_real_polynomial_upper_all hl hM hB u hs hr hcut
    hcenter z hz hp hp2 k hk
  apply hh.trans
  gcongr
  exact max_norm_exp_rpow_le_exp_two hl hz hp hp2

/-- One conditional moment tail works throughout any fixed complex window
inside the strict source moment domain. -/
theorem localProfile_ae_complex_window_moment_decay {l p η r : ℝ} {z₀ : ℂ}
    (hl : 1 < l) (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hwindow : ∀ z : ℂ, dist z z₀ < r →
      z.re < profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
      ∃ D : ℝ, 0 ≤ D ∧
        (∀ z : ℂ, dist z z₀ < r → ∀ k ≥ localSafeCutoff l u,
          prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1
            (localSafeCutoff l u) k ≠ 0) ∧
        ∀ (n : ℕ) (z : ℂ), dist z z₀ < r → ∀ (j N : ℕ),
          localSafeCutoff l u ≤ j → 1 ≤ j → j ≤ N →
          (∫ ω, ‖prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
              (initial n) (localSafeCutoff l u) N (ω N) -
            prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
              (initial n) (localSafeCutoff l u) j (ω j)‖ ^ p
            ∂prescribedTrajectoryMeasure (localBirth l u) (initial n)) ≤
              D * (j : ℝ) ^ (-η) := by
  filter_upwards [localProfile_ae_raw_controls_all hl] with u hu
  intro hs
  obtain ⟨M, B, hM, hB, hr, hcut, hcenter⟩ := hu hs
  let J := localSafeCutoff l u
  let E := localProfileLogEnvelope l u M B
  let A := Real.exp (-E)
  let U := 2 * (Real.exp 2) ^ J * Real.exp E
  let c := 1 / (M + 1)
  let Q : ℝ := (Real.exp 2 / (A * c)) ^ p * (2 : ℝ) ^ p * U
  let D : ℝ := (4 * (2 : ℝ) ^ p) * Q / η
  have hA : 0 < A := Real.exp_pos _
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hp0 : 0 ≤ p := by linarith
  have hpos : ∀ i, 0 < prescribedWalk (localBirth l u) 1 i := by
    intro i
    apply prescribedWalk_local_pos (H := i) _ le_rfl
    intro j _
    exact_mod_cast hs j
  refine ⟨D, hD, ?_, ?_⟩
  · intro z hz k hk
    obtain ⟨hzr, _⟩ := hwindow z hz
    rw [localNormalizer_eq_exp_centered l u hs hcut k z
      (by linarith [profileRoot_pos hl])]
    exact Complex.exp_ne_zero _
  · intro n z hz j N hJj hj hjN
    obtain ⟨hzr, he⟩ := hwindow z hz
    have hClower : A * ((N + 1 : ℕ) : ℝ) ^
        (growthFactor l * ((Complex.exp z).re - 1)) ≤
        ‖prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1 J (N + 1)‖ :=
      localProfile_complex_polynomial_lower hl hM hB u hs hr hcut hcenter z
        (by linarith [profileRoot_pos hl]) (hJj.trans hjN)
    have hC : prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1 J N ≠ 0 := by
      rw [localNormalizer_eq_exp_centered l u hs hcut N z
        (by linarith [profileRoot_pos hl])]
      exact Complex.exp_ne_zero _
    have hmax : max 1 ‖Complex.exp z‖ ≤ Real.exp 2 := by
      have hh := max_norm_exp_rpow_le_exp_two hl hzr (show (1 : ℝ) ≤ 1 by norm_num)
        (show (1 : ℝ) ≤ 2 by norm_num)
      simpa only [Real.rpow_one] using hh
    have hconstant :
        (max 1 ‖Complex.exp z‖ / (A * c)) ^ p * (2 : ℝ) ^ p * U ≤ Q := by
      apply mul_le_mul_of_nonneg_right _ hU
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
      exact Real.rpow_le_rpow (div_nonneg (le_max_of_le_left (by norm_num))
        (mul_pos hA hc).le)
        (div_le_div_of_nonneg_right hmax (mul_pos hA hc).le) hp0
    have hm := prescribedTrajectory_profile_moment_sub_le (Complex.exp z)
      (localBirth l u) (initial n) N J j hJj hjN hp hp2
      (by simpa only [infectious_initial] using fun i (_ : i ≤ N) ↦ hpos i) hC
    have hexp : growthFactor l * (Real.exp (p * z.re) - 1) -
        p * (growthFactor l * ((Complex.exp z).re - 1) + 1) =
          complexProfileMomentExponent l z p := by
      unfold complexProfileMomentExponent
      ring
    calc
      _ ≤ (4 * (2 : ℝ) ^ p) *
          ∑ k ∈ Finset.Ico j N,
            prescribedShiftedMomentBound (Complex.exp z) (localBirth l u)
              (initial n) J p k := hm
      _ ≤ (4 * (2 : ℝ) ^ p) *
          ∑ k ∈ Finset.Ico j N,
            Q * ((k + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro k hk
        have hJk := hJj.trans (Finset.mem_Ico.mp hk).1
        have hb := (prescribedShiftedMomentBound_complex_le_max (Complex.exp z)
          hp0 (localBirth l u) n J k hJk (hpos (k + 1))).trans
          (profile_moment_ratio_le (le_max_of_le_left (by norm_num)) hp0 hA hU hc
            (by positivity)
            (realNormalizer_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
              (localBirth l u) 1 k)
            (localProfile_complex_polynomial_lower hl hM hB u hs hr hcut hcenter z
              (by linarith [profileRoot_pos hl]) hJk)
            (localProfile_count_lower l u hM hs hr k)
            (localProfile_real_polynomial_upper_uniform hl hM hB u hs hr hcut
              hcenter z hzr hp.le hp2 k hJk))
        rw [hexp] at hb
        exact hb.trans (mul_le_mul_of_nonneg_right hconstant
          (Real.rpow_nonneg (by positivity) _))
      _ = (4 * (2 : ℝ) ^ p) * Q *
          ∑ k ∈ Finset.Ico j N,
            ((k + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ (4 * (2 : ℝ) ^ p) * Q * ((j : ℝ) ^ (-η) / η) :=
        mul_le_mul_of_nonneg_left (sum_complex_profile_moment_le hη he hj hjN)
          (by positivity)
      _ = D * (j : ℝ) ^ (-η) := by dsimp only [D]; ring

/-- Every point of the complex moment domain has a strict moment window;
the same window works as the epidemic parameter increases. -/
theorem exists_localProfile_complex_moment_disk {l p : ℝ} {z₀ : ℂ}
    (hl : 1 < l) (hp : 1 < p) (hp2 : p ≤ 2)
    (hz : z₀.re < profileRoot l)
    (he : complexProfileMomentExponent l z₀ p < -1) :
    ∃ η > 0, ∃ r > 0, ∀ L ≥ l, ∀ z : ℂ, dist z z₀ < r →
      z.re < profileRoot L ∧
        complexProfileMomentExponent L z p ≤ -1 - η := by
  let η := (-1 - complexProfileMomentExponent l z₀ p) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have he' : complexProfileMomentExponent l z₀ p < -1 - η := by
    dsimp [η]
    linarith
  have hreal : ∀ᶠ z in 𝓝 z₀, z.re < profileRoot l :=
    Complex.continuous_re.continuousAt.eventually (gt_mem_nhds hz)
  have hexp : ∀ᶠ z in 𝓝 z₀,
      complexProfileMomentExponent l z p < -1 - η :=
    (continuous_complexProfileMomentExponent l p).continuousAt.eventually
      (gt_mem_nhds he')
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hreal.and hexp)
  refine ⟨η, hη, r, hr, ?_⟩
  intro L hL z hzr
  obtain ⟨hzr', hez⟩ := hball hzr
  exact ⟨hzr'.trans_le (profileRoot_mono_supercritical hl hL),
    (complexProfileMomentExponent_antitone_parameter hl hL hp.le z).trans hez.le⟩

end HeightPaper.CountCoupling
