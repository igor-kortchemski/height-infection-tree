module

public import HeightPaper.Probability.LocalProfileGeneralComplexTightness
public import HeightPaper.Probability.FiniteProfileGrowth

/-! # Complex local profile moments at every power exponent -/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace HeightPaper.CountCoupling

open Model

noncomputable def localComplexGrowthEnvelope (M B : ℝ) (K : ℕ) (p : ℝ) : ℝ :=
  let E := localProfileUniformLogEnvelope M B K
  let A := Real.exp (-E)
  let U := 2 * (Real.exp 2) ^ K * Real.exp E
  let c := 1 / (M + 1)
  (4 * (2 : ℝ) ^ p) *
    ((Real.exp 2 / (A * c)) ^ p * (2 : ℝ) ^ p * U)

theorem localComplexGrowthEnvelope_nonneg {M B p : ℝ} (hM : 0 ≤ M)
    (K : ℕ) : 0 ≤ localComplexGrowthEnvelope M B K p := by
  unfold localComplexGrowthEnvelope
  positivity

noncomputable def localComplexGrowthUniformEnvelope (M B : ℝ) (K : ℕ) : ℝ :=
  let E := localProfileUniformLogEnvelope M B K
  let A := Real.exp (-E)
  let U := 2 * (Real.exp 2) ^ K * Real.exp E
  let c := 1 / (M + 1)
  16 * (max 1 (Real.exp 2 / (A * c))) ^ (2 : ℝ) * 4 * U

theorem localComplexGrowthEnvelope_le_uniform {M B p : ℝ}
    (hM : 0 ≤ M) (hp : 1 ≤ p) (hp2 : p ≤ 2) (K : ℕ) :
    localComplexGrowthEnvelope M B K p ≤
      localComplexGrowthUniformEnvelope M B K := by
  let E := localProfileUniformLogEnvelope M B K
  let A := Real.exp (-E)
  let U := 2 * (Real.exp 2) ^ K * Real.exp E
  let c := 1 / (M + 1)
  let b := Real.exp 2 / (A * c)
  have hA : 0 < A := Real.exp_pos _
  have hc : 0 < c := by dsimp [c]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have htwo : (2 : ℝ) ^ p ≤ 4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ 2 by norm_num) hp2
    rw [Real.rpow_two] at hh
    norm_num at hh ⊢
    exact hh
  have hbase : b ^ p ≤ (max 1 b) ^ (2 : ℝ) :=
    (Real.rpow_le_rpow hb (le_max_right _ _) hp0).trans
      (Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) hp2)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hbig : 4 * (2 : ℝ) ^ p ≤ 16 := by nlinarith
  calc
    localComplexGrowthEnvelope M B K p =
        (4 * (2 : ℝ) ^ p) * (b ^ p * (2 : ℝ) ^ p * U) := rfl
    _ ≤ 16 * (b ^ p * (2 : ℝ) ^ p * U) :=
      mul_le_mul_of_nonneg_right hbig (by positivity)
    _ ≤ 16 * ((max 1 b) ^ (2 : ℝ) * (2 : ℝ) ^ p * U) := by
      gcongr
    _ ≤ 16 * ((max 1 b) ^ (2 : ℝ) * 4 * U) := by
      gcongr
    _ = localComplexGrowthUniformEnvelope M B K := by
      dsimp only [localComplexGrowthUniformEnvelope, E, A, U, c, b]
      ring

theorem localComplexGrowthUniformEnvelope_nonneg {M B : ℝ} (hM : 0 ≤ M)
    (K : ℕ) : 0 ≤ localComplexGrowthUniformEnvelope M B K := by
  unfold localComplexGrowthUniformEnvelope
  positivity

/-- The exponent in the source half-plane has a common upper bound for all
parameters above a fixed supercritical lower endpoint. -/
theorem complexProfileMomentExponent_le_global
    {l₀ l p : ℝ} (hl₀ : 1 < l₀) (hll : l₀ ≤ l)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) {z : ℂ}
    (hz : z.re < profileRoot l) :
    complexProfileMomentExponent l z p ≤
      growthFactor l₀ * (Real.exp 2 + 2 * Real.exp 1 + 1) := by
  have hl : 1 < l := hl₀.trans_le hll
  have hz1 : z.re < 1 := hz.trans (profileRoot_lt_one hl)
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hpre : p * z.re ≤ 2 := by
    by_cases hx : 0 ≤ z.re
    · have hh := mul_le_mul_of_nonneg_right hp2 hx
      nlinarith
    · have hh := mul_nonpos_of_nonneg_of_nonpos hp0 (le_of_lt (lt_of_not_ge hx))
      linarith
  have hexp : Real.exp (p * z.re) ≤ Real.exp 2 := Real.exp_le_exp.mpr hpre
  have hnorm : ‖Complex.exp z‖ ≤ Real.exp 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr hz1.le
  have hneg : -(Complex.exp z).re ≤ Real.exp 1 := by
    have hh := Complex.re_le_norm (-Complex.exp z)
    simpa only [Complex.neg_re] using
      hh.trans (by simpa only [norm_neg] using hnorm)
  have hterm : p * (1 - (Complex.exp z).re) ≤ 2 * (Real.exp 1 + 1) := by
    have hh := mul_le_mul_of_nonneg_left
      (show 1 - (Complex.exp z).re ≤ Real.exp 1 + 1 by linarith) hp0
    have hh' := mul_le_mul_of_nonneg_right hp2
      (show 0 ≤ Real.exp 1 + 1 by positivity)
    linarith
  have hbracket :
      Real.exp (p * z.re) - 1 - p * ((Complex.exp z).re - 1) ≤
        Real.exp 2 + 2 * Real.exp 1 + 1 := by
    linarith
  have hbracket0 := complex_profile_ratio_exponent_nonneg z hp
  have hγ := growthFactor_antitone hl₀ hll
  have hγpos := growthFactor_pos hl₀
  have hmul := mul_le_mul_of_nonneg_right hγ hbracket0
  have hmul' := mul_le_mul_of_nonneg_left hbracket hγpos.le
  unfold complexProfileMomentExponent
  linarith

theorem max_two_rpow_complexProfileMomentExponent_le_global
    {l₀ l p : ℝ} (hl₀ : 1 < l₀) (hll : l₀ ≤ l)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) {z : ℂ}
    (hz : z.re < profileRoot l) :
    max 1 ((2 : ℝ) ^ complexProfileMomentExponent l z p) ≤
      (2 : ℝ) ^ (growthFactor l₀ * (Real.exp 2 + 2 * Real.exp 1 + 1)) := by
  have hR : 0 ≤ growthFactor l₀ * (Real.exp 2 + 2 * Real.exp 1 + 1) := by
    exact mul_nonneg (growthFactor_pos hl₀).le (by positivity)
  apply max_le
  · exact Real.one_le_rpow (by norm_num) hR
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (complexProfileMomentExponent_le_global hl₀ hll hp hp2 hz)

/-- The all-exponent increment bound retains the logarithm at the critical
power `-1`. The envelope depends on the count word only through three controls. -/
theorem localProfile_complexMomentDifference_le_power_sum
    {l M B p : ℝ} (hl : 1 < l)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (u : ℕ → ℝ) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hcut : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B)
    (K : ℕ) (hK : localSafeCutoff l u ≤ K)
    (n : ℕ) (z : ℂ) (hzr : z.re < profileRoot l)
    (j N : ℕ) (hJj : localSafeCutoff l u ≤ j) (hjN : j ≤ N) :
    localProfileMomentDifference l u n z p j N ≤
      localComplexGrowthEnvelope M B K p *
        (∑ k ∈ Finset.Ico j N,
          ((k + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p) := by
  let E := localProfileUniformLogEnvelope M B K
  let A := Real.exp (-E)
  let U := 2 * (Real.exp 2) ^ K * Real.exp E
  let c := 1 / (M + 1)
  let Q : ℝ := (Real.exp 2 / (A * c)) ^ p * (2 : ℝ) ^ p * U
  have hA : 0 < A := Real.exp_pos _
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hz : z.re < 2 * profileRoot l := by linarith [profileRoot_pos hl]
  have hE : localProfileLogEnvelope l u M B ≤ E := by
    have hKr : (localSafeCutoff l u : ℝ) ≤ K := by exact_mod_cast hK
    dsimp only [E, localProfileUniformLogEnvelope, localProfileLogEnvelope]
    gcongr
  have hpos : ∀ i, 0 < Model.prescribedWalk (localBirth l u) 1 i := by
    intro i
    apply prescribedWalk_local_pos (H := i) _ le_rfl
    intro k _
    exact_mod_cast hs k
  have hClower : ∀ k ≥ localSafeCutoff l u,
      A * ((k + 1 : ℕ) : ℝ) ^ (growthFactor l * ((Complex.exp z).re - 1)) ≤
        ‖Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1
          (localSafeCutoff l u) (k + 1)‖ := by
    intro k hk
    apply le_trans _ (localProfile_complex_polynomial_lower hl hM hB u hs hr hcut hcenter z hz hk)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hE))
      (Real.rpow_nonneg (by positivity) _)
  have hCupper : ∀ k ≥ localSafeCutoff l u,
      Model.realNormalizer (‖Complex.exp z‖ ^ p) (localBirth l u) 1 k ≤
        U * ((k + 1 : ℕ) : ℝ) ^ (growthFactor l * (Real.exp (p * z.re) - 1)) := by
    intro k hk
    apply (localProfile_real_polynomial_upper_uniform hl hM hB u hs hr hcut
      hcenter z hzr hp hp2 k hk).trans
    have hpow : (Real.exp 2) ^ (localSafeCutoff l u) ≤ (Real.exp 2) ^ K :=
      pow_le_pow_right₀ (Real.one_le_exp_iff.mpr (by norm_num)) hK
    dsimp only [U]
    gcongr
  have hC : Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1
      (localSafeCutoff l u) N ≠ 0 := by
    rw [localNormalizer_eq_exp_centered l u hs hcut N z hz]
    exact Complex.exp_ne_zero _
  have hmax : max 1 ‖Complex.exp z‖ ≤ Real.exp 2 := by
    have hh := max_norm_exp_rpow_le_exp_two hl hzr
      (show (1 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 2 by norm_num)
    simpa only [Real.rpow_one] using hh
  have hconstant :
      (max 1 ‖Complex.exp z‖ / (A * c)) ^ p * (2 : ℝ) ^ p * U ≤ Q := by
    apply mul_le_mul_of_nonneg_right _ hU
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
    exact Real.rpow_le_rpow (div_nonneg (le_max_of_le_left (by norm_num))
      (mul_pos hA hc).le)
      (div_le_div_of_nonneg_right hmax (mul_pos hA hc).le) hp0
  have hm := Model.prescribedTrajectory_profile_moment_sub_le_all (Complex.exp z)
    (localBirth l u) (Model.initial n) N (localSafeCutoff l u) j hJj hjN hp hp2
    (by simpa only [Model.infectious_initial] using fun i (_ : i ≤ N) ↦ hpos i)
    (by simpa only [Model.infectious_initial] using hC)
  have hexp : growthFactor l * (Real.exp (p * z.re) - 1) -
      p * (growthFactor l * ((Complex.exp z).re - 1) + 1) =
        complexProfileMomentExponent l z p := by
    unfold complexProfileMomentExponent
    ring
  have hterm (k : ℕ) (hk : k ∈ Finset.Ico j N) :
      Model.prescribedShiftedMomentBound (Complex.exp z) (localBirth l u)
          (Model.initial n) (localSafeCutoff l u) p k ≤
        Q * Real.exp (complexProfileMomentExponent l z p * Real.log (k + 1 : ℕ)) := by
    have hJk := hJj.trans (Finset.mem_Ico.mp hk).1
    have hb := (prescribedShiftedMomentBound_complex_le_max (Complex.exp z)
      hp0 (localBirth l u) n (localSafeCutoff l u) k hJk (hpos (k + 1))).trans
      (Model.profile_moment_ratio_le (le_max_of_le_left (by norm_num)) hp0 hA hU hc
        (by positivity)
        (realNormalizer_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
          (localBirth l u) 1 k)
        (hClower k hJk) (localProfile_count_lower l u hM hs hr k)
        (hCupper k hJk))
    rw [hexp] at hb
    calc
      _ ≤ (max 1 ‖Complex.exp z‖ / (A * c)) ^ p * (2 : ℝ) ^ p * U *
          ((k + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p := hb
      _ ≤ Q * ((k + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p :=
        mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg (by positivity) _)
      _ = _ := by rw [Real.rpow_def_of_pos (by positivity)]; ring
  have hsum :
      (∑ k ∈ Finset.Ico j N,
        Model.prescribedShiftedMomentBound (Complex.exp z) (localBirth l u)
          (Model.initial n) (localSafeCutoff l u) p k) ≤
        Q * (∑ k ∈ Finset.Ico j N,
          ((k + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p) := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico j N,
          Q * Real.exp (complexProfileMomentExponent l z p * Real.log (k + 1 : ℕ)) :=
        Finset.sum_le_sum hterm
      _ = Q * ∑ k ∈ Finset.Ico j N,
          Real.exp (complexProfileMomentExponent l z p * Real.log (k + 1 : ℕ)) := by
        rw [Finset.mul_sum]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [Real.rpow_def_of_pos (by positivity)]
        congr 1
        ring
  calc
    _ ≤ (4 * (2 : ℝ) ^ p) *
        ∑ k ∈ Finset.Ico j N,
          Model.prescribedShiftedMomentBound (Complex.exp z) (localBirth l u)
            (Model.initial n) (localSafeCutoff l u) p k := hm
    _ ≤ (4 * (2 : ℝ) ^ p) *
        (Q * ∑ k ∈ Finset.Ico j N,
          ((k + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp only [localComplexGrowthEnvelope, Q, A, U, c, E]; ring

/-- The global all-exponent envelope, with the critical logarithm retained. -/
theorem localProfile_complexMomentDifference_le_growth
    {l M B p : ℝ} (hl : 1 < l)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (u : ℕ → ℝ) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hcut : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B)
    (K : ℕ) (hK : localSafeCutoff l u ≤ K)
    (n : ℕ) (z : ℂ) (hzr : z.re < profileRoot l)
    (j N : ℕ) (hJj : localSafeCutoff l u ≤ j) (hjN : j ≤ N) :
    localProfileMomentDifference l u n z p j N ≤
      localComplexGrowthEnvelope M B K p *
        profileGrowthScale (complexProfileMomentExponent l z p) N := by
  have hsum := sum_exp_log_Ico_le (complexProfileMomentExponent l z p) 0 j N
  have hsumpow :
      (∑ k ∈ Finset.Ico j N,
        ((k + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p) ≤
          profileGrowthScale (complexProfileMomentExponent l z p) N := by
    convert hsum using 1
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Real.rpow_def_of_pos (by positivity)]
      congr 1
      ring
    · simp [profileGrowthScale]
  exact (localProfile_complexMomentDifference_le_power_sum hl hM hB hp hp2 u hs hr hcut
    hcenter K hK n z hzr j N hJj hjN).trans
    (mul_le_mul_of_nonneg_left hsumpow (localComplexGrowthEnvelope_nonneg hM K))

/-- The first estimate in the paper's complex moment lemma, with the exact
dyadic power and an explicit constant for each exponent. -/
theorem localProfile_complexMomentDifference_le_dyadic
    {l M B p : ℝ} (hl : 1 < l)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (u : ℕ → ℝ) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hcut : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B)
    (K : ℕ) (hK : localSafeCutoff l u ≤ K)
    (n : ℕ) (z : ℂ) (hzr : z.re < profileRoot l)
    (k : ℕ) (hJk : localSafeCutoff l u ≤ k) (hk : 1 ≤ k) :
    localProfileMomentDifference l u n z p k (2 * k) ≤
      localComplexGrowthEnvelope M B K p *
        max 1 ((2 : ℝ) ^ complexProfileMomentExponent l z p) *
          (k : ℝ) ^ (complexProfileMomentExponent l z p + 1) := by
  let a := complexProfileMomentExponent l z p
  have hsum := sum_rpow_Ico_double_le a hk
  have hpow : (k : ℝ) * max 1 ((2 : ℝ) ^ a) * (k : ℝ) ^ a =
      max 1 ((2 : ℝ) ^ a) * (k : ℝ) ^ (a + 1) := by
    rw [Real.rpow_add (by positivity), Real.rpow_one]
    ring
  have hbound := localProfile_complexMomentDifference_le_power_sum hl hM hB hp hp2
    u hs hr hcut hcenter K hK n z hzr k (2 * k) hJk (by omega)
  apply hbound.trans
  calc
    localComplexGrowthEnvelope M B K p *
        (∑ i ∈ Finset.Ico k (2 * k), ((i + 1 : ℕ) : ℝ) ^ a) ≤
      localComplexGrowthEnvelope M B K p *
        ((k : ℝ) * max 1 ((2 : ℝ) ^ a) * (k : ℝ) ^ a) :=
      mul_le_mul_of_nonneg_left hsum (localComplexGrowthEnvelope_nonneg hM K)
    _ = _ := by rw [hpow]; ring

noncomputable def localProfileMomentAtTime (l : ℝ) (u : ℕ → ℝ)
    (n : ℕ) (z : ℂ) (p : ℝ) (k : ℕ) : ℝ :=
  ∫ ω, ‖Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
      (Model.initial n) (localSafeCutoff l u) k (ω k)‖ ^ p
    ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)

theorem localProfileMomentAtTime_eq_finite (l : ℝ) (u : ℕ → ℝ)
    (n : ℕ) (z : ℂ) (p : ℝ) (k : ℕ) :
    localProfileMomentAtTime l u n z p k =
      ∫ q, ‖Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
        (Model.initial n) (localSafeCutoff l u) k q.last‖ ^ p
        ∂Model.kernelPathMeasure (fun i ↦ Model.prescribedStep (localBirth l u i))
          (Model.initial n) k := by
  have heq := Model.kernelTrajectory_integral_prefix
    (fun i ↦ Model.prescribedStep (localBirth l u i)) (Model.initial n) k
    (fun q ↦ ‖Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
      (Model.initial n) (localSafeCutoff l u) k q.last‖ ^ p)
  simpa only [Model.trajectoryPrefix_last, Model.prescribedTrajectoryMeasure,
    localProfileMomentAtTime] using heq

theorem localProfileMomentAtTime_congr_prefix {l : ℝ} {u v : ℕ → ℝ}
    (hJ : localSafeCutoff l u = localSafeCutoff l v) {k : ℕ}
    (he : ∀ i < k, localBirth l u i = localBirth l v i)
    (n : ℕ) (z : ℂ) (p : ℝ) (hJk : localSafeCutoff l u ≤ k) :
    localProfileMomentAtTime l u n z p k = localProfileMomentAtTime l v n z p k := by
  rw [localProfileMomentAtTime_eq_finite l u n z p k,
    localProfileMomentAtTime_eq_finite l v n z p k]
  simp only [Model.prescribedNormalizedProfile, Model.infectious_initial]
  rw [← hJ, Model.prescribedNormalizerFrom_congr_prefix (Complex.exp z) 1 _ he le_rfl]
  unfold Model.kernelPathMeasure
  rw [Model.kernelPathLaw_prescribed_congr_prefix (Model.initial n) he]

/-- The profile at the safe cutoff has a deterministic bound once the cutoff
itself is bounded; this includes negative real tilts. -/
theorem localProfileMomentAtTime_cutoff_le
    {l : ℝ} (hl : 1 < l) (u : ℕ → ℝ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (K : ℕ) (hK : localSafeCutoff l u ≤ K)
    (n : ℕ) (z : ℂ) (hz : z.re < profileRoot l)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    localProfileMomentAtTime l u n z p (localSafeCutoff l u) ≤
      (Real.exp 2) ^ K := by
  let J := localSafeCutoff l u
  let w := Complex.exp z
  have hpos : ∀ i ≤ J, 0 < prescribedWalk (localBirth l u) 1 i := by
    intro i hi
    apply prescribedWalk_local_pos (H := i) _ le_rfl
    intro k _
    exact_mod_cast hs k
  have hpath := prescribedPath_shifted_moment_le_max_prefix w (localBirth l u)
    n J J le_rfl hp hpos
  have hpath' :
      (∫ q, ‖prescribedNormalizedProfile w (localBirth l u) (initial n) J J q.last‖ ^ p
        ∂kernelPathMeasure (fun i ↦ prescribedStep (localBirth l u i)) (initial n) J) ≤
      (max 1 (‖w‖ ^ p)) ^ J := by
    simpa only [prescribedNormalizedProfile, infectious_initial, realNormalizerFrom,
      prescribedNormalizerFrom, Finset.Ico_self, Finset.prod_empty, norm_one,
      one_pow, Real.one_rpow, div_one, inv_one, one_mul] using hpath
  have htraj := kernelTrajectory_integral_prefix
    (fun i ↦ prescribedStep (localBirth l u i)) (initial n) J
    (fun q ↦ ‖prescribedNormalizedProfile w (localBirth l u) (initial n) J J q.last‖ ^ p)
  have hbase : localProfileMomentAtTime l u n z p J ≤
      (max 1 (‖w‖ ^ p)) ^ J := by
    simpa only [localProfileMomentAtTime, prescribedTrajectoryMeasure,
      trajectoryPrefix_last, w, J] using htraj.trans_le hpath'
  have hmax : max 1 (‖w‖ ^ p) ≤ Real.exp 2 :=
    max_norm_exp_rpow_le_exp_two hl hz hp hp2
  exact hbase.trans ((pow_le_pow_left₀ (by positivity) hmax J).trans
    (pow_le_pow_right₀ (Real.one_le_exp_iff.mpr (by norm_num)) hK))

/-- The second growth estimate before taking the common stochastic envelope. -/
theorem localProfileMomentAtTime_le_growth
    {l M B p : ℝ} (hl : 1 < l)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (u : ℕ → ℝ) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hcut : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B)
    (K : ℕ) (hK : localSafeCutoff l u ≤ K)
    (n : ℕ) (z : ℂ) (hzr : z.re < profileRoot l)
    (k : ℕ) (hJk : localSafeCutoff l u ≤ k) (hk : 1 ≤ k) :
    localProfileMomentAtTime l u n z p k ≤
      (2 * localComplexGrowthEnvelope M B K p + 2 * (Real.exp 2) ^ K) *
        profileGrowthScale (complexProfileMomentExponent l z p) k := by
  let J := localSafeCutoff l u
  let μ := prescribedTrajectoryMeasure (localBirth l u) (initial n)
  let f : (ℕ → State) → ℂ := fun ω ↦
    prescribedNormalizedProfile (Complex.exp z) (localBirth l u) (initial n) J k (ω k)
  let g : (ℕ → State) → ℂ := fun ω ↦
    prescribedNormalizedProfile (Complex.exp z) (localBirth l u) (initial n) J J (ω J)
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpne : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hf : MemLp f (ENNReal.ofReal p) μ := by
    have hsum : J + (k - J) = k := Nat.add_sub_of_le hJk
    simpa only [f, μ, hsum] using
      prescribedTrajectory_profile_memLp (Complex.exp z) (localBirth l u)
        (initial n) J (k - J) hp0
  have hg : MemLp g (ENNReal.ofReal p) μ := by
    simpa only [g, μ, Nat.add_zero] using
      prescribedTrajectory_profile_memLp (Complex.exp z) (localBirth l u)
        (initial n) J 0 hp0
  have hfi : Integrable (fun ω ↦ ‖f ω‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hf.integrable_norm_rpow hpne hptop
  have hgi : Integrable (fun ω ↦ ‖g ω‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hg.integrable_norm_rpow hpne hptop
  have hdi : Integrable (fun ω ↦ ‖f ω - g ω‖ ^ p) μ := by
    simpa only [Pi.sub_apply, ENNReal.toReal_ofReal hp0.le] using
      (hf.sub hg).integrable_norm_rpow hpne hptop
  have hbound : (∫ ω, ‖f ω‖ ^ p ∂μ) ≤
      2 * ((∫ ω, ‖f ω - g ω‖ ^ p ∂μ) + (∫ ω, ‖g ω‖ ^ p ∂μ)) := by
    calc
      _ ≤ ∫ ω, 2 * (‖f ω - g ω‖ ^ p + ‖g ω‖ ^ p) ∂μ :=
        integral_mono_ae hfi ((hdi.add hgi).const_mul 2)
          (ae_of_all _ (fun ω ↦ norm_rpow_le_sub_add (f ω) (g ω) hp hp2))
      _ = _ := by rw [integral_const_mul, integral_add hdi hgi]
  have hdiff := localProfile_complexMomentDifference_le_growth hl hM hB hp hp2
    u hs hr hcut hcenter K hK n z hzr J k le_rfl hJk
  have hbase := localProfileMomentAtTime_cutoff_le hl u hs K hK n z hzr hp hp2
  have hscale : 1 ≤ profileGrowthScale (complexProfileMomentExponent l z p) k :=
    one_le_profileGrowthScale _ hk
  have hnonneg : 0 ≤ localComplexGrowthEnvelope M B K p :=
    localComplexGrowthEnvelope_nonneg hM K
  have hexp : 0 ≤ (Real.exp 2) ^ K := by positivity
  change (∫ ω, ‖f ω‖ ^ p ∂μ) ≤ _
  calc
    _ ≤ 2 * ((∫ ω, ‖f ω - g ω‖ ^ p ∂μ) + (∫ ω, ‖g ω‖ ^ p ∂μ)) := hbound
    _ ≤ 2 * (localComplexGrowthEnvelope M B K p *
        profileGrowthScale (complexProfileMomentExponent l z p) k + (Real.exp 2) ^ K) := by
      have hd : (∫ ω, ‖f ω - g ω‖ ^ p ∂μ) ≤
          localComplexGrowthEnvelope M B K p *
            profileGrowthScale (complexProfileMomentExponent l z p) k := hdiff
      have hb : (∫ ω, ‖g ω‖ ^ p ∂μ) ≤ (Real.exp 2) ^ K := hbase
      linarith
    _ ≤ _ := by nlinarith

/-- Failure of either source moment-growth estimate, with a single multiplier
before the time, initial size, complex tilt, and order in `[1,2]` are chosen. -/
def localComplexGrowthBad (D l : ℝ) : Set (ℕ → ℝ) :=
  {u | (∀ i, 0 < (localWalk l u i : ℝ)) ∧
    ∃ n : ℕ, ∃ z : ℂ, z.re < profileRoot l ∧
      ∃ p ∈ Icc (1 : ℝ) 2, ∃ k : ℕ,
        localSafeCutoff l u ≤ k ∧ 1 ≤ k ∧
        (D * (k : ℝ) ^ (complexProfileMomentExponent l z p + 1) <
            localProfileMomentDifference l u n z p k (2 * k) ∨
          D * profileGrowthScale (complexProfileMomentExponent l z p) k <
            localProfileMomentAtTime l u n z p k)}

/-- Both source bounds admit one stochastic multiplier, weakly uniformly over
all supercritical parameters above the lower endpoint. The global growth
scale retains `1 + log k` exactly at the critical exponent. -/
theorem localComplexGrowthBad_uniform_tight
    {l₀ : ℝ} (hl₀ : 1 < l₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ l ≥ l₀,
      uniformLaw.real (localComplexGrowthBad D l) ≤ ε := by
  have heps : 0 < ε / 3 := by positivity
  obtain ⟨M, hM, hMtight⟩ := positiveReciprocal_uniform_tight hl₀ heps
  obtain ⟨K, hKtight⟩ := localSafeCutoff_uniform_tight hl₀ heps
  obtain ⟨B, hB, hBtight⟩ := localCenteredReciprocal_uniform_tight hl₀ heps
  let U := localComplexGrowthUniformEnvelope M B K
  let R := (2 : ℝ) ^ (growthFactor l₀ * (Real.exp 2 + 2 * Real.exp 1 + 1))
  let D := (2 * U + 2 * (Real.exp 2) ^ K) * R
  have hU : 0 ≤ U := localComplexGrowthUniformEnvelope_nonneg hM K
  have hR : 1 ≤ R := Real.one_le_rpow (by norm_num)
    (mul_nonneg (growthFactor_pos hl₀).le (by positivity))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro l hl
  have hl1 := hl₀.trans_le hl
  let F₁ : Set (ℕ → ℝ) := {u | ∃ k, M < positiveReciprocal l u k}
  let F₂ : Set (ℕ → ℝ) := {u | K < localSafeCutoff l u}
  let F₃ : Set (ℕ → ℝ) := {u | ∃ k : ℕ, (∀ i ≤ k, 0 < (localWalk l u i : ℝ)) ∧
    B < |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) - growthFactor l * Real.log k|}
  have hsub : ∀ᵐ u ∂uniformLaw,
      u ∈ localComplexGrowthBad D l → u ∈ F₁ ∪ F₂ ∪ F₃ := by
    filter_upwards [localSafeCutoff_ae_bddAbove hl1] with u hu
    rintro ⟨hs, n, z, hz, p, ⟨hp, hp2⟩, k, hJk, hk, hbad⟩
    by_cases h₁ : u ∈ F₁
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : u ∈ F₂
    · exact Or.inl (Or.inr h₂)
    by_cases h₃ : u ∈ F₃
    · exact Or.inr h₃
    have hr : ∀ j, positiveReciprocal l u j ≤ M :=
      fun j ↦ le_of_not_gt (fun hh ↦ h₁ ⟨j, hh⟩)
    have hK : localSafeCutoff l u ≤ K := le_of_not_gt h₂
    have hcenter : ∀ j, |(∑ i ∈ Finset.range j, localBirthCoefficient l u i) -
        growthFactor l * Real.log j| ≤ B := by
      intro j
      exact le_of_not_gt (fun hh ↦ h₃ ⟨j, fun i _ ↦ hs i, hh⟩)
    have hEnv := localComplexGrowthEnvelope_le_uniform (B := B) hM hp hp2 K
    have hFactor := max_two_rpow_complexProfileMomentExponent_le_global hl₀ hl hp hp2 hz
    have hScale : 0 ≤ (k : ℝ) ^ (complexProfileMomentExponent l z p + 1) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hGrowth : 0 ≤ profileGrowthScale (complexProfileMomentExponent l z p) k :=
      (show (0 : ℝ) ≤ 1 by norm_num).trans (one_le_profileGrowthScale _ hk)
    have hDyadic := localProfile_complexMomentDifference_le_dyadic hl1 hM hB hp hp2
      u hs hr hu hcenter K hK n z hz k hJk hk
    have hWhole := localProfileMomentAtTime_le_growth hl1 hM hB hp hp2
      u hs hr hu hcenter K hK n z hz k hJk hk
    have hDyadicCoeff :
        localComplexGrowthEnvelope M B K p *
          max 1 ((2 : ℝ) ^ complexProfileMomentExponent l z p) ≤ D := by
      have hE0 := localComplexGrowthEnvelope_nonneg (B := B) (p := p) hM K
      have hm := mul_le_mul hEnv hFactor (by positivity) hU
      have hD' : U * R ≤ D := by
        dsimp [D]
        nlinarith [mul_nonneg hU (zero_le_one.trans hR),
          mul_nonneg (by positivity : 0 ≤ (Real.exp 2) ^ K) (zero_le_one.trans hR)]
      exact hm.trans hD'
    have hWholeCoeff : 2 * localComplexGrowthEnvelope M B K p +
        2 * (Real.exp 2) ^ K ≤ D := by
      have hh : 2 * localComplexGrowthEnvelope M B K p + 2 * (Real.exp 2) ^ K ≤
          2 * U + 2 * (Real.exp 2) ^ K := by linarith
      exact hh.trans (by
        dsimp [D]
        exact le_mul_of_one_le_right (by positivity) hR)
    rcases hbad with hbad | hbad
    · have hh := hDyadic.trans
        (mul_le_mul_of_nonneg_right hDyadicCoeff hScale)
      exact False.elim (not_lt_of_ge hh hbad)
    · have hh := hWhole.trans
        (mul_le_mul_of_nonneg_right hWholeCoeff hGrowth)
      exact False.elim (not_lt_of_ge hh hbad)
  have hmeasure := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hunion : uniformLaw.real (F₁ ∪ F₂ ∪ F₃) ≤
      uniformLaw.real F₁ + uniformLaw.real F₂ + uniformLaw.real F₃ :=
    (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
  apply hmeasure.trans (hunion.trans _)
  have h₁ := hMtight l hl
  have h₂ := hKtight l hl
  have h₃ : uniformLaw.real F₃ ≤ ε / 3 := by
    simpa only [F₃, localBirthCoefficient, growthFactor] using hBtight l hl
  linarith

/-- A deterministic power slack absorbs the critical logarithm. -/
theorem profileGrowthScale_le_rpow_slack (a η : ℝ) (hη : 0 < η)
    {k : ℕ} (hk : 1 ≤ k) :
    profileGrowthScale a k ≤
      (1 + 1 / η) * (k : ℝ) ^ (max (a + 1) 0 + η) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hpow : 1 ≤ (k : ℝ) ^ η :=
    Real.one_le_rpow (by exact_mod_cast hk) hη.le
  have hlog := Real.log_natCast_le_rpow_div k hη
  have hfactor : 1 + Real.log k ≤ (1 + 1 / η) * (k : ℝ) ^ η := by
    calc
      _ ≤ 1 + (k : ℝ) ^ η / η := by linarith
      _ ≤ (k : ℝ) ^ η + (k : ℝ) ^ η / η := by linarith
      _ = _ := by ring
  unfold profileGrowthScale
  have hexp : Real.exp (max (a + 1) 0 * Real.log k) =
      (k : ℝ) ^ max (a + 1) 0 := by
    rw [Real.rpow_def_of_pos hkpos]
    congr 1
    ring
  rw [hexp, Real.rpow_add hkpos]
  have hnonneg := Real.rpow_nonneg hkpos.le (max (a + 1) 0)
  nlinarith [mul_le_mul_of_nonneg_right hfactor hnonneg]

/-- The paper's two power estimates with an arbitrary positive exponent slack.
This is a precise version of its `O_P(k^(exponent + o_P(1)))` notation. -/
def localComplexGrowthPowerBad (D η l : ℝ) : Set (ℕ → ℝ) :=
  {u | (∀ i, 0 < (localWalk l u i : ℝ)) ∧
    ∃ n : ℕ, ∃ z : ℂ, z.re < profileRoot l ∧
      ∃ p ∈ Icc (1 : ℝ) 2, ∃ k : ℕ,
        localSafeCutoff l u ≤ k ∧ 1 ≤ k ∧
        (D * (k : ℝ) ^ (complexProfileMomentExponent l z p + 1) <
            localProfileMomentDifference l u n z p k (2 * k) ∨
          D * (k : ℝ) ^ (max (complexProfileMomentExponent l z p + 1) 0 + η) <
            localProfileMomentAtTime l u n z p k)}

theorem measurableSet_localComplexGrowthPowerBad (D η l : ℝ) :
    MeasurableSet (localComplexGrowthPowerBad D η l) := by
  have hsurv : MeasurableSet {u : ℕ → ℝ | ∀ i, 0 < (localWalk l u i : ℝ)} := by
    have hh := MeasurableSet.iInter (fun i ↦
      measurableSet_lt (measurable_const : Measurable (fun _ : ℕ → ℝ ↦ (0 : ℝ)))
        (measurable_localWalk_real l i))
    convert hh using 1
    ext u
    simp
  have hslice (k : ℕ) : MeasurableSet {u : ℕ → ℝ |
      localSafeCutoff l u ≤ k ∧ 1 ≤ k ∧
      ∃ n : ℕ, ∃ z : ℂ, z.re < profileRoot l ∧
        ∃ p ∈ Icc (1 : ℝ) 2,
          D * (k : ℝ) ^ (complexProfileMomentExponent l z p + 1) <
              localProfileMomentDifference l u n z p k (2 * k) ∨
            D * (k : ℝ) ^ (max (complexProfileMomentExponent l z p + 1) 0 + η) <
              localProfileMomentAtTime l u n z p k} := by
    apply measurableSet_of_localBirth_cutoff_prefix l (2 * k)
    intro u v hJ he
    have he' : ∀ i < k, localBirth l u i = localBirth l v i :=
      fun i hi ↦ he i (by omega)
    constructor
    · rintro ⟨hJk, hk, n, z, hz, p, hp, hbad⟩
      refine ⟨hJ ▸ hJk, hk, n, z, hz, p, hp, ?_⟩
      rcases hbad with hbad | hbad
      · left
        rwa [← localProfileMomentDifference_congr_prefix hJ he n z p (by omega)]
      · right
        rwa [← localProfileMomentAtTime_congr_prefix hJ he' n z p hJk]
    · rintro ⟨hJk, hk, n, z, hz, p, hp, hbad⟩
      refine ⟨hJ.symm ▸ hJk, hk, n, z, hz, p, hp, ?_⟩
      rcases hbad with hbad | hbad
      · left
        rwa [localProfileMomentDifference_congr_prefix hJ he n z p (by omega)]
      · right
        rwa [localProfileMomentAtTime_congr_prefix hJ he' n z p (hJ.symm ▸ hJk)]
  convert hsurv.inter (MeasurableSet.iUnion hslice) using 1
  ext u
  simp only [localComplexGrowthPowerBad, mem_ofPred_eq, mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨hs, n, z, hz, p, hp, k, hJk, hk, hbad⟩
    exact ⟨hs, k, hJk, hk, n, z, hz, p, hp, hbad⟩
  · rintro ⟨hs, k, hJk, hk, n, z, hz, p, hp, hbad⟩
    exact ⟨hs, n, z, hz, p, hp, k, hJk, hk, hbad⟩

theorem localComplexGrowthPowerBad_uniform_tight
    {l₀ η : ℝ} (hl₀ : 1 < l₀) (hη : 0 < η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ l ≥ l₀,
      uniformLaw.real (localComplexGrowthPowerBad D η l) ≤ ε := by
  obtain ⟨D₀, hD₀, hbound⟩ := localComplexGrowthBad_uniform_tight hl₀ hε
  let D := D₀ * (1 + 1 / η)
  have hfactor : 1 ≤ 1 + 1 / η := by linarith [one_div_pos.mpr hη]
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro l hl
  have hsub : localComplexGrowthPowerBad D η l ⊆ localComplexGrowthBad D₀ l := by
    rintro u ⟨hs, n, z, hz, p, hp, k, hJk, hk, hbad⟩
    refine ⟨hs, n, z, hz, p, hp, k, hJk, hk, ?_⟩
    have hscale : 0 ≤ (k : ℝ) ^ (complexProfileMomentExponent l z p + 1) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hDle : D₀ ≤ D := by
      dsimp [D]
      exact le_mul_of_one_le_right hD₀ hfactor
    rcases hbad with hbad | hbad
    · left
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hDle hscale) hbad
    · right
      have hgrowth := profileGrowthScale_le_rpow_slack
        (complexProfileMomentExponent l z p) η hη hk
      have hh : D₀ * profileGrowthScale (complexProfileMomentExponent l z p) k ≤
          D * (k : ℝ) ^
            (max (complexProfileMomentExponent l z p + 1) 0 + η) := by
        dsimp [D]
        convert mul_le_mul_of_nonneg_left hgrowth hD₀ using 1 <;> ring
      exact lt_of_le_of_lt hh hbad
  exact (measureReal_mono hsub).trans (hbound l hl)

end HeightPaper.CountCoupling
