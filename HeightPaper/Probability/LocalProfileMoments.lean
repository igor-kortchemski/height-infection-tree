module

public import HeightPaper.Probability.LocalComplexNormalizer
public import HeightPaper.Model.FiniteNormalizerBounds
public import HeightPaper.Model.PolynomialNormalizer
public import HeightPaper.Model.InfiniteProfileLp
public import HeightPaper.Analysis.ComplexMomentExponent

/-!
# Actual local event-word profile moments

The reciprocal and count controls are supplied by the iid local walk. They
provide common polynomial product bounds before the complex tilt and moment
order are chosen, and hence discharge the hypotheses of the infinite
prescribed-tree profile convergence theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical

namespace HeightPaper.CountCoupling

/-- One pathwise logarithmic error for every safe complex tilt. -/
noncomputable def localProfileLogEnvelope (l : ℝ) (u : ℕ → ℝ) (M B : ℝ) : ℝ :=
  (Real.exp 2 + 1) * (B + localSafeCutoff l u) + (Real.exp 2 + 1) ^ 2 * (2 * M ^ 2)

theorem localProfileLogEnvelope_nonneg (l : ℝ) (u : ℕ → ℝ) (M : ℝ) {B : ℝ}
    (hB : 0 ≤ B) : 0 ≤ localProfileLogEnvelope l u M B := by
  unfold localProfileLogEnvelope
  positivity

private theorem local_model_centered_bound (l : ℝ) (u : ℕ → ℝ) {B : ℝ}
    (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B) (k : ℕ) :
    |(∑ i ∈ Finset.range k, Model.birthReciprocal (localBirth l u) 1 i) -
      growthFactor l * Real.log k| ≤ B := by
  have heq : Model.birthReciprocal (localBirth l u) 1 = localBirthCoefficient l u :=
    funext (fun i ↦ (localBirthCoefficient_eq_model l u hs i).symm)
  simpa only [heq] using hcenter k

/-- The actual complex product has a common polynomial lower bound. -/
theorem localProfile_complex_polynomial_lower {l M B : ℝ} (hl : 1 < l)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (u : ℕ → ℝ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hcut : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B)
    (z : ℂ) (hz : z.re < 2 * profileRoot l) {k : ℕ} (hk : localSafeCutoff l u ≤ k) :
    Real.exp (-localProfileLogEnvelope l u M B) *
        ((k + 1 : ℕ) : ℝ) ^ (growthFactor l * ((Complex.exp z).re - 1)) ≤
      ‖Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1
        (localSafeCutoff l u) (k + 1)‖ := by
  have hcenter' := Model.birthReciprocal_Ico_centered_bound (localBirth l u) 1
    (localSafeCutoff l u) (k + 1) (localSafeCutoff l u) (by omega) le_rfl
    (local_model_centered_bound l u hs hcenter (k + 1))
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
    (Complex.exp z) (norm_exp_sub_one_lt_localNormalizerRadius z hz).le).1
  apply le_trans _ hh
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  unfold localProfileLogEnvelope
  have hR := localNormalizerRadius_le hl
  have hR0 := (localNormalizerRadius_pos l).le
  gcongr

/-- The unshifted real product is bounded directly, so no random prefix
factor is needed in the upper bound. -/
theorem localProfile_real_polynomial_upper {l M B : ℝ} (hl : 1 < l)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (u : ℕ → ℝ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B)
    (z : ℂ) (hz : 0 ≤ z.re) {p : ℝ} (hp : 1 ≤ p)
    (hpz : p * z.re < 2 * profileRoot l) (k : ℕ) :
    Model.realNormalizer (‖Complex.exp z‖ ^ p) (localBirth l u) 1 k ≤
      Real.exp (localProfileLogEnvelope l u M B) *
        ((k + 1 : ℕ) : ℝ) ^ (growthFactor l * (Real.exp (p * z.re) - 1)) := by
  have hv : 1 ≤ Real.exp (p * z.re) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (zero_le_one.trans hp) hz)
  have hlog : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) := by
    by_cases hk : k = 0
    · simp [hk]
    · apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk)
      exact_mod_cast (show k ≤ k + 1 by omega)
  have hc := local_model_centered_bound l u hs hcenter k
  have hupper : (∑ i ∈ Finset.range k, Model.birthReciprocal (localBirth l u) 1 i) ≤
      growthFactor l * Real.log ((k + 1 : ℕ) : ℝ) + B := by
    have hmul := mul_le_mul_of_nonneg_left hlog (growthFactor_pos hl).le
    linarith [(abs_le.mp hc).2]
  have hlower : (0 : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) - B ≤
      ∑ i ∈ Finset.range k, Model.birthReciprocal (localBirth l u) 1 i := by
    have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range k) ↦
      Model.birthReciprocal_nonneg (localBirth l u) 1 i)
    linarith
  have hsquare : (∑ i ∈ Finset.range k, (Model.birthReciprocal (localBirth l u) 1 i) ^ 2) ≤
      2 * M ^ 2 := by
    simpa only [Nat.Ico_zero_eq_range] using
      Model.birthReciprocal_Ico_square_bound (localBirth l u) 1 0 k (M := M) (fun i _ ↦ by
        rw [← localBirthCoefficient_eq_model l u hs]
        exact localBirthCoefficient_le_linear l u hM hs hr i)
  have hh := (Model.realNormalizer_polynomial_bounds hv
    (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ)) (localBirth l u) 1 k
    hlower hupper hsquare).2
  have hvR : Real.exp (p * z.re) - 1 ≤ Real.exp 2 + 1 := by
    have hpre : p * z.re ≤ 2 := by linarith [profileRoot_lt_one hl]
    linarith [Real.exp_le_exp.mpr hpre]
  have hD : (Real.exp (p * z.re) - 1) * B + (Real.exp (p * z.re) - 1) ^ 2 * (2 * M ^ 2) ≤
      localProfileLogEnvelope l u M B := by
    unfold localProfileLogEnvelope
    have hv0 := sub_nonneg.mpr hv
    have hj : B ≤ B + (localSafeCutoff l u : ℝ) := by
      linarith [Nat.cast_nonneg (localSafeCutoff l u) (α := ℝ)]
    gcongr
  have hw : ‖Complex.exp z‖ ^ p = Real.exp (p * z.re) := by
    rw [Complex.norm_exp, ← Real.exp_mul, mul_comm]
  rw [hw]
  apply hh.trans
  rw [mul_comm (Real.exp (p * z.re) - 1) (growthFactor l)]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hD) (Real.rpow_nonneg (by positivity) _)

theorem localProfile_count_lower (l : ℝ) (u : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M) (k : ℕ) :
    (1 / (M + 1)) * (k + 1 : ℕ) ≤ (Model.prescribedWalk (localBirth l u) 1 (k + 1) : ℝ) := by
  have hsint : ∀ i, 0 < localWalk l u i := fun i ↦ by exact_mod_cast hs i
  rw [prescribedWalk_local_real (H := k + 1) (fun i _ ↦ hsint i) le_rfl]
  have hh := hr (k + 1)
  simp only [positiveReciprocal, ite_eq_left (hsint (k + 1))] at hh
  have hmul := (div_le_iff₀ (hs (k + 1))).mp hh
  calc
    (1 / (M + 1)) * (k + 1 : ℕ) = ((k + 1 : ℕ) : ℝ) / (M + 1) := by ring
    _ ≤ (localWalk l u (k + 1) : ℝ) := by
      apply (div_le_iff₀ (by linarith : 0 < M + 1)).mpr
      nlinarith [hs (k + 1)]


/-- The iid local event word almost surely supplies all count and normalizer
estimates with common constants chosen before the complex tilt and moment order. -/
theorem localProfile_ae_polynomial_controls {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
      ∃ A B c : ℝ, 0 < A ∧ 0 ≤ B ∧ 0 < c ∧
        (∀ i, 0 < Model.prescribedWalk (localBirth l u) 1 i) ∧
        (∀ k, c * (k + 1 : ℕ) ≤ (Model.prescribedWalk (localBirth l u) 1 (k + 1) : ℝ)) ∧
        ∀ z : ℂ, 0 ≤ z.re → z.re < 2 * profileRoot l →
          (∀ k ≥ localSafeCutoff l u,
            Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1
              (localSafeCutoff l u) k ≠ 0) ∧
          (∀ k ≥ localSafeCutoff l u,
            A * ((k + 1 : ℕ) : ℝ) ^ (growthFactor l * ((Complex.exp z).re - 1)) ≤
              ‖Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1
                (localSafeCutoff l u) (k + 1)‖) ∧
          (∀ p : ℝ, 1 ≤ p → p * z.re < 2 * profileRoot l → ∀ k ≥ localSafeCutoff l u,
            Model.realNormalizer (‖Complex.exp z‖ ^ p) (localBirth l u) 1 k ≤
              B * ((k + 1 : ℕ) : ℝ) ^ (growthFactor l * (Real.exp (p * z.re) - 1))) := by
  filter_upwards [ae_tendsto_finiteLocalCenteredReciprocal hl,
    positiveReciprocal_ae_uniform_bounded hl, localSafeCutoff_ae_bddAbove hl]
    with u hconv hratio hcut
  intro hs
  obtain ⟨M₀, hM₀⟩ := hratio
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hr : ∀ k, positiveReciprocal l u k ≤ M :=
    fun k ↦ (hM₀ l le_rfl k).trans (le_max_left _ _)
  obtain ⟨B₀, hB₀, hBbound⟩ := (Metric.isBounded_range_of_tendsto _ hconv).exists_pos_norm_le
  have hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B₀ := by
    intro k
    have hh := hBbound (finiteLocalCenteredReciprocal l u k) ⟨k, rfl⟩
    simpa only [Real.norm_eq_abs, finiteLocalCenteredReciprocal, localBirthCoefficient,
      ite_eq_left (show ∀ i ≤ k, 0 < (localWalk l u i : ℝ) from fun i _ ↦ hs i),
      one_mul, growthFactor] using hh
  refine ⟨Real.exp (-localProfileLogEnvelope l u M B₀),
    Real.exp (localProfileLogEnvelope l u M B₀), 1 / (M + 1),
    Real.exp_pos _, (Real.exp_pos _).le, by positivity, ?_, ?_, ?_⟩
  · intro i
    apply prescribedWalk_local_pos (H := i) _ le_rfl
    intro j _
    exact_mod_cast hs j
  · exact localProfile_count_lower l u hM hs hr
  · intro z hz0 hz
    refine ⟨?_, ?_, ?_⟩
    · intro k _
      rw [localNormalizer_eq_exp_centered l u hs hcut k z hz]
      exact Complex.exp_ne_zero _
    · intro k hk
      exact localProfile_complex_polynomial_lower hl hM hB₀.le u hs hr hcut hcenter z hz hk
    · intro p hp hpz k _
      exact localProfile_real_polynomial_upper hl hM hB₀.le u hs hr hcenter z hz0 hp hpz k

/-- The actual local random event word supplies the hypotheses of the
prescribed-history almost-sure and Lp convergence theorem. -/
theorem localProfile_ae_exists_lp_limit {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
      ∀ (n : ℕ) (z : ℂ) (p : ℝ), 0 ≤ z.re → z.re < 2 * profileRoot l →
        1 < p → p ≤ 2 → p * z.re < 2 * profileRoot l →
        complexProfileMomentExponent l z p < -1 →
        ∃ F : (ℕ → Model.State) → ℂ, Measurable F ∧
          MemLp F (ENNReal.ofReal p) (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
          (∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
            Tendsto (fun k ↦ Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
              (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
              (ω (localSafeCutoff l u + k))) atTop (𝓝 (F ω))) ∧
          Tendsto (fun k ↦ eLpNorm
            ((fun ω ↦ Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
              (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
              (ω (localSafeCutoff l u + k))) - F)
            (ENNReal.ofReal p) (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)))
            atTop (𝓝 0) := by
  filter_upwards [localProfile_ae_polynomial_controls hl] with u hu
  intro hs n z p hz0 hz hp hp2 hpz hexp
  obtain ⟨A, B, c, hA, hB, hc, hpos, hcount, hnormal⟩ := hu hs
  obtain ⟨hC, hClower, hCupper⟩ := hnormal z hz0 hz
  have hw : 1 ≤ ‖Complex.exp z‖ := by
    rw [Complex.norm_exp]
    exact Real.one_le_exp_iff.mpr hz0
  have he : growthFactor l * (Real.exp (p * z.re) - 1) -
      p * (growthFactor l * ((Complex.exp z).re - 1) + 1) < -1 := by
    convert hexp using 1
    unfold complexProfileMomentExponent
    ring
  exact Model.prescribedTrajectory_exists_profile_lp_limit_of_polynomial hw hp hp2 hA hB hc he
    (localBirth l u) n (localSafeCutoff l u) hpos hC hClower (hCupper p hp.le hpz)
    (fun k _ ↦ hcount k)


/-- The profile edge increases with the supercritical epidemic parameter. -/
theorem profileRoot_mono_supercritical {l L : ℝ} (hl : 1 < l) (hL : l ≤ L) :
    profileRoot l ≤ profileRoot L := by
  have hL1 := hl.trans_le hL
  let a := Real.exp (profileRoot l) - 1 - profileRoot l * Real.exp (profileRoot l)
  have heq : 1 + growthFactor l * a = 0 := profileExponent_profileRoot hl
  have ha : a ≤ 0 := by
    by_contra h
    have hpos := mul_pos (growthFactor_pos hl) (lt_of_not_ge h)
    linarith
  have hm := mul_le_mul_of_nonpos_right (growthFactor_antitone hl hL) ha
  have hnonneg : 0 ≤ profileExponent L (profileRoot l) := by
    change 0 ≤ 1 + growthFactor L * a
    linarith
  by_contra h
  have hstrict := profileExponent_strictAntiOn hL1 (profileRoot_pos hL1).le
    (profileRoot_pos hl).le (lt_of_not_ge h)
  rw [profileExponent_profileRoot hL1] at hstrict
  exact not_lt_of_ge hnonneg hstrict

/-- A common disk around a positive real tilt lies within the safe moment
domain and has a fixed strictly summable moment exponent. -/
theorem exists_localProfile_moment_disk {l x : ℝ} (hl : 1 < l)
    (hx : 0 < x) (hxr : x < profileRoot l) :
    ∃ p ∈ Set.Ioo (1 : ℝ) 2, ∃ η : ℝ, 0 < η ∧ ∃ r > 0,
      ∀ L ≥ l, ∀ z : ℂ, dist z (x : ℂ) < r →
        0 ≤ z.re ∧ z.re < profileRoot L ∧ p * z.re < 2 * profileRoot L ∧
          complexProfileMomentExponent L z p ≤ -1 - η := by
  obtain ⟨p, hp, η, hη, r₀, hr₀, hdecay⟩ :=
    exists_uniform_complex_profile_moment_decay hl hx.le hxr
  let r := min r₀ (min (x / 2) ((profileRoot l - x) / 2))
  have hr : 0 < r := lt_min hr₀ (lt_min (by positivity) (by linarith))
  refine ⟨p, hp, η, hη, r, hr, ?_⟩
  intro L hL z hz
  have hr₁ : r ≤ r₀ := min_le_left _ _
  have hr₂ : r ≤ x / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr₃ : r ≤ (profileRoot l - x) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have habs : |z.re - x| < r := by
    have hh : |z.re - x| ≤ dist z (x : ℂ) := by
      simpa only [Complex.sub_re, Complex.ofReal_re, dist_eq_norm] using
        Complex.abs_re_le_norm (z - (x : ℂ))
    exact hh.trans_lt hz
  have hz0 : 0 ≤ z.re := by have hh := (abs_lt.mp habs).1; linarith
  have hzroot : z.re < profileRoot L := by
    have hh := (abs_lt.mp habs).2
    have hm := profileRoot_mono_supercritical hl hL
    linarith
  have hpz : p * z.re < 2 * profileRoot L := by
    have hh := mul_le_mul_of_nonneg_right hp.2.le hz0
    linarith
  exact ⟨hz0, hzroot, hpz, hdecay L hL z (hz.trans_le hr₁)⟩

/-- Uniform conditional moment tails on one deterministic complex neighborhood
of a positive real tilt. All count-word hypotheses are discharged under the
actual iid law. The random multiplier is shared by every tilt and both times. -/
theorem localProfile_uniform_near_real_moment_decay {l₀ x : ℝ} (hl₀ : 1 < l₀)
    (hx : 0 < x) (hxr : x < profileRoot l₀) :
    ∃ p ∈ Set.Ioo (1 : ℝ) 2, ∃ η : ℝ, 0 < η ∧ ∃ r > 0,
      ∀ l ≥ l₀, ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
        ∃ D : ℝ, 0 ≤ D ∧
          (∀ z : ℂ, dist z (x : ℂ) < r → ∀ k ≥ localSafeCutoff l u,
            Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1
              (localSafeCutoff l u) k ≠ 0) ∧
          ∀ (n : ℕ) (z : ℂ), dist z (x : ℂ) < r → ∀ (j N : ℕ),
            localSafeCutoff l u ≤ j → 1 ≤ j → j ≤ N →
            (∫ ω, ‖Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                (Model.initial n) (localSafeCutoff l u) N (ω N) -
              Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p
              ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤
                D * (j : ℝ) ^ (-η) := by
  obtain ⟨p, hp, η, hη, r, hr, hwindow⟩ := exists_localProfile_moment_disk hl₀ hx hxr
  refine ⟨p, hp, η, hη, r, hr, ?_⟩
  intro l hl
  have hl1 := hl₀.trans_le hl
  filter_upwards [localProfile_ae_polynomial_controls hl1] with u hu
  intro hs
  obtain ⟨A, B, c, hA, hB, hc, hpos, hcount, hnormal⟩ := hu hs
  let Q : ℝ := (Real.exp 2 / (A * c)) ^ p * (2 : ℝ) ^ p * B
  let D : ℝ := (4 * (2 : ℝ) ^ p) * Q / η
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hp0 : 0 ≤ p := zero_le_one.trans hp.1.le
  refine ⟨D, hD, ?_, ?_⟩
  · intro z hz
    obtain ⟨hz0, hzr, _, _⟩ := hwindow l hl z hz
    exact (hnormal z hz0 (by linarith [profileRoot_pos hl1])).1
  · intro n z hz j N hJj hj hjN
    obtain ⟨hz0, hzr, hpz, he⟩ := hwindow l hl z hz
    obtain ⟨hC, hClower, hCupper⟩ := hnormal z hz0 (by linarith [profileRoot_pos hl1])
    have hw : 1 ≤ ‖Complex.exp z‖ := by
      rw [Complex.norm_exp]
      exact Real.one_le_exp_iff.mpr hz0
    have hwupper : ‖Complex.exp z‖ ≤ Real.exp 2 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      linarith [profileRoot_lt_one hl1]
    have hwp : 1 ≤ ‖Complex.exp z‖ ^ p := Real.one_le_rpow hw hp0
    have hconstant : (‖Complex.exp z‖ / (A * c)) ^ p * (2 : ℝ) ^ p * B ≤ Q := by
      apply mul_le_mul_of_nonneg_right _ hB
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
      exact Real.rpow_le_rpow (div_nonneg (norm_nonneg _) (mul_pos hA hc).le)
        (div_le_div_of_nonneg_right hwupper (mul_pos hA hc).le) hp0
    have hm := Model.prescribedTrajectory_profile_moment_sub_le (Complex.exp z)
      (localBirth l u) (Model.initial n) N (localSafeCutoff l u) j hJj hjN hp.1 hp.2.le
      (by simpa only [Model.infectious_initial] using fun i (_ : i ≤ N) ↦ hpos i)
      (by simpa only [Model.infectious_initial] using hC N (hJj.trans hjN))
    have hexp : growthFactor l * (Real.exp (p * z.re) - 1) -
        p * (growthFactor l * ((Complex.exp z).re - 1) + 1) =
          complexProfileMomentExponent l z p := by
      unfold complexProfileMomentExponent
      ring
    calc
      _ ≤ (4 * (2 : ℝ) ^ p) *
          ∑ k ∈ Finset.Ico j N,
            Model.prescribedShiftedMomentBound (Complex.exp z) (localBirth l u)
              (Model.initial n) (localSafeCutoff l u) p k := hm
      _ ≤ (4 * (2 : ℝ) ^ p) *
          ∑ k ∈ Finset.Ico j N, Q * ((k + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro k hk
        have hJk := hJj.trans (Finset.mem_Ico.mp hk).1
        have hb := (Model.prescribedShiftedMomentBound_complex_le (Complex.exp z) hw hp0
          (localBirth l u) n (localSafeCutoff l u) k hJk (hpos (k + 1))).trans
          (Model.profile_moment_ratio_le (norm_nonneg _) hp0 hA hB hc
            (by positivity) (zero_le_one.trans (Model.one_le_realNormalizer hwp (localBirth l u) 1 k))
            (hClower k hJk) (hcount k) (hCupper p hp.1.le hpz k hJk))
        rw [hexp] at hb
        exact hb.trans (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg (by positivity) _))
      _ = (4 * (2 : ℝ) ^ p) * Q *
          ∑ k ∈ Finset.Ico j N, ((k + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ (4 * (2 : ℝ) ^ p) * Q * ((j : ℝ) ^ (-η) / η) :=
        mul_le_mul_of_nonneg_left (sum_complex_profile_moment_le hη he hj hjN) (by positivity)
      _ = D * (j : ℝ) ^ (-η) := by dsimp only [D]; ring

end HeightPaper.CountCoupling
