module

public import HeightPaper.Probability.LocalProfileGeneralComplexBounds
public import HeightPaper.Probability.LocalProfileMomentTightness

/-!
# Parameter-uniform complex moment multipliers
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical

namespace HeightPaper.CountCoupling

noncomputable def localComplexMomentEnvelope (M B : ℝ) (K : ℕ) (p η : ℝ) : ℝ :=
  let E := localProfileUniformLogEnvelope M B K
  let A := Real.exp (-E)
  let U := 2 * (Real.exp 2) ^ K * Real.exp E
  let c := 1 / (M + 1)
  (4 * (2 : ℝ) ^ p) *
    ((Real.exp 2 / (A * c)) ^ p * (2 : ℝ) ^ p * U) / η

theorem localComplexMomentEnvelope_nonneg {M B p η : ℝ}
    (hM : 0 ≤ M) (hη : 0 < η) (K : ℕ) :
    0 ≤ localComplexMomentEnvelope M B K p η := by
  unfold localComplexMomentEnvelope
  positivity

/-- A deterministic multiplier from common count-word controls works for
all tilts in the negative as well as positive half-plane. -/
theorem localProfile_complexMomentDifference_le_envelope
    {l M B p η : ℝ} (hl : 1 < l)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (u : ℕ → ℝ) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hcut : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B)
    (K : ℕ) (hK : localSafeCutoff l u ≤ K)
    (n : ℕ) (z : ℂ) (hzr : z.re < profileRoot l)
    (he : complexProfileMomentExponent l z p ≤ -1 - η)
    (j N : ℕ) (hJj : localSafeCutoff l u ≤ j) (hj : 1 ≤ j) (hjN : j ≤ N) :
    localProfileMomentDifference l u n z p j N ≤
      localComplexMomentEnvelope M B K p η * (j : ℝ) ^ (-η) := by
  let E := localProfileUniformLogEnvelope M B K
  let A := Real.exp (-E)
  let U := 2 * (Real.exp 2) ^ K * Real.exp E
  let c := 1 / (M + 1)
  let Q : ℝ := (Real.exp 2 / (A * c)) ^ p * (2 : ℝ) ^ p * U
  have hA : 0 < A := Real.exp_pos _
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
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
      hcenter z hzr hp.le hp2 k hk).trans
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
  have hm := Model.prescribedTrajectory_profile_moment_sub_le (Complex.exp z)
    (localBirth l u) (Model.initial n) N (localSafeCutoff l u) j hJj hjN hp hp2
    (by simpa only [Model.infectious_initial] using fun i (_ : i ≤ N) ↦ hpos i)
    (by simpa only [Model.infectious_initial] using hC)
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
        ∑ k ∈ Finset.Ico j N,
          Q * ((k + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k hk
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
    _ = _ := by dsimp only [Q, A, U, c, E, localComplexMomentEnvelope]; ring

/-- Failure of a complex-window conditional moment multiplier on a surviving
local word. -/
def localComplexMomentBad (p η r : ℝ) (z₀ : ℂ) (D l : ℝ) : Set (ℕ → ℝ) :=
  {u | (∀ i, 0 < (localWalk l u i : ℝ)) ∧ ∃ n j N : ℕ,
    localSafeCutoff l u ≤ j ∧ 1 ≤ j ∧ j ≤ N ∧ ∃ z : ℂ,
      dist z z₀ < r ∧
        D * (j : ℝ) ^ (-η) < localProfileMomentDifference l u n z p j N}

theorem measurableSet_localComplexMomentBad (p η r : ℝ) (z₀ : ℂ) (D l : ℝ) :
    MeasurableSet (localComplexMomentBad p η r z₀ D l) := by
  have hsurv : MeasurableSet {u : ℕ → ℝ | ∀ i, 0 < (localWalk l u i : ℝ)} := by
    have hh := MeasurableSet.iInter (fun i ↦
      measurableSet_lt (measurable_const : Measurable (fun _ : ℕ → ℝ ↦ (0 : ℝ)))
        (measurable_localWalk_real l i))
    convert hh using 1
    ext u
    simp
  have hslice (n j N : ℕ) : MeasurableSet {u : ℕ → ℝ |
      localSafeCutoff l u ≤ j ∧ 1 ≤ j ∧ j ≤ N ∧ ∃ z : ℂ,
        dist z z₀ < r ∧ D * (j : ℝ) ^ (-η) < localProfileMomentDifference l u n z p j N} := by
    apply measurableSet_of_localBirth_cutoff_prefix l N
    intro u v hJ he
    constructor
    · rintro ⟨hJj, hj, hjN, z, hz, hbad⟩
      refine ⟨hJ ▸ hJj, hj, hjN, z, hz, ?_⟩
      rwa [← localProfileMomentDifference_congr_prefix hJ he n z p hjN]
    · rintro ⟨hJj, hj, hjN, z, hz, hbad⟩
      refine ⟨hJ.symm ▸ hJj, hj, hjN, z, hz, ?_⟩
      rwa [localProfileMomentDifference_congr_prefix hJ he n z p hjN]
  convert hsurv.inter (MeasurableSet.iUnion (fun n ↦ MeasurableSet.iUnion (fun j ↦
    MeasurableSet.iUnion (fun N ↦ hslice n j N)))) using 1
  ext u
  simp only [localComplexMomentBad, mem_ofPred_eq, mem_inter_iff, mem_iUnion]

/-- A single multiplier is tight uniformly in all epidemic parameters above
the supercritical lower endpoint, on a fixed complex moment window. -/
theorem localComplexMomentBad_uniform_tight
    {l₀ p η r : ℝ} {z₀ : ℂ} (hl₀ : 1 < l₀)
    (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z z₀ < r →
      z.re < profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ l ≥ l₀,
      uniformLaw.real (localComplexMomentBad p η r z₀ D l) ≤ ε := by
  have heps : 0 < ε / 3 := by positivity
  obtain ⟨M, hM, hMtight⟩ := positiveReciprocal_uniform_tight hl₀ heps
  obtain ⟨K, hKtight⟩ := localSafeCutoff_uniform_tight hl₀ heps
  obtain ⟨B, hB, hBtight⟩ := localCenteredReciprocal_uniform_tight hl₀ heps
  let D := localComplexMomentEnvelope M B K p η
  refine ⟨D, localComplexMomentEnvelope_nonneg hM hη K, ?_⟩
  intro l hl
  have hl1 := hl₀.trans_le hl
  let F₁ : Set (ℕ → ℝ) := {u | ∃ k, M < positiveReciprocal l u k}
  let F₂ : Set (ℕ → ℝ) := {u | K < localSafeCutoff l u}
  let F₃ : Set (ℕ → ℝ) := {u | ∃ k : ℕ, (∀ i ≤ k, 0 < (localWalk l u i : ℝ)) ∧
    B < |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) - growthFactor l * Real.log k|}
  have hsub : ∀ᵐ u ∂uniformLaw,
      u ∈ localComplexMomentBad p η r z₀ D l → u ∈ F₁ ∪ F₂ ∪ F₃ := by
    filter_upwards [localSafeCutoff_ae_bddAbove hl1] with u hu
    rintro ⟨hs, n, j, N, hJj, hj, hjN, z, hz, hbad⟩
    by_cases h₁ : u ∈ F₁
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : u ∈ F₂
    · exact Or.inl (Or.inr h₂)
    by_cases h₃ : u ∈ F₃
    · exact Or.inr h₃
    have hr : ∀ k, positiveReciprocal l u k ≤ M :=
      fun k ↦ le_of_not_gt (fun hh ↦ h₁ ⟨k, hh⟩)
    have hK : localSafeCutoff l u ≤ K := le_of_not_gt h₂
    have hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
        growthFactor l * Real.log k| ≤ B := by
      intro k
      exact le_of_not_gt (fun hh ↦ h₃ ⟨k, fun i _ ↦ hs i, hh⟩)
    obtain ⟨hzr, he⟩ := hwindow l hl z hz
    have hh := localProfile_complexMomentDifference_le_envelope hl1 hM hB hp hp2 hη
      u hs hr hu hcenter K hK n z hzr he j N hJj hj hjN
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

end HeightPaper.CountCoupling
