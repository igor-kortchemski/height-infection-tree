module

public import HeightPaper.Probability.LocalProfileMoments
public import HeightPaper.Model.PrescribedPrefix

/-!
# Uniform stochastic multipliers for local profile moment tails

Finite word observables retain the exact infinite-trajectory moments. Their
common multiplier is bounded on events controlled by the already proved
uniform count, centered reciprocal sum, and cutoff tail estimates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical

namespace HeightPaper.CountCoupling

noncomputable def localProfileMomentDifference (l : ℝ) (u : ℕ → ℝ)
    (n : ℕ) (z : ℂ) (p : ℝ) (j N : ℕ) : ℝ :=
  ∫ ω, ‖Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
      (Model.initial n) (localSafeCutoff l u) N (ω N) -
    Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
      (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p
    ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)

/-- The moment is computed on the actual finite prefix of the same infinite
history, so its dependence on the event word is finite once the cutoff is fixed. -/
theorem localProfileMomentDifference_eq_finite (l : ℝ) (u : ℕ → ℝ)
    (n : ℕ) (z : ℂ) (p : ℝ) {j N : ℕ} (hjN : j ≤ N) :
    localProfileMomentDifference l u n z p j N =
      ∫ q, ‖Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
          (Model.initial n) (localSafeCutoff l u) N q.last -
        Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
          (Model.initial n) (localSafeCutoff l u) j (q.eval j)‖ ^ p
        ∂Model.kernelPathMeasure (fun i ↦ Model.prescribedStep (localBirth l u i)) (Model.initial n) N := by
  have heq := Model.kernelTrajectory_integral_prefix
    (fun i ↦ Model.prescribedStep (localBirth l u i)) (Model.initial n) N
    (fun q ↦ ‖Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
        (Model.initial n) (localSafeCutoff l u) N q.last -
      Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
        (Model.initial n) (localSafeCutoff l u) j (q.eval j)‖ ^ p)
  simpa only [Model.trajectoryPrefix_last, Model.trajectoryPrefix_eval N _ j hjN,
    Model.prescribedTrajectoryMeasure, localProfileMomentDifference] using heq

theorem localProfileMomentDifference_congr_prefix {l : ℝ} {u v : ℕ → ℝ}
    (hJ : localSafeCutoff l u = localSafeCutoff l v) {N : ℕ}
    (he : ∀ i < N, localBirth l u i = localBirth l v i)
    (n : ℕ) (z : ℂ) (p : ℝ) {j : ℕ} (hjN : j ≤ N) :
    localProfileMomentDifference l u n z p j N = localProfileMomentDifference l v n z p j N := by
  rw [localProfileMomentDifference_eq_finite l u n z p hjN,
    localProfileMomentDifference_eq_finite l v n z p hjN]
  simp only [Model.prescribedNormalizedProfile, Model.infectious_initial]
  rw [hJ, Model.prescribedNormalizerFrom_congr_prefix (Complex.exp z) 1 _ he le_rfl,
    Model.prescribedNormalizerFrom_congr_prefix (Complex.exp z) 1 _ he hjN]
  unfold Model.kernelPathMeasure
  rw [Model.kernelPathLaw_prescribed_congr_prefix (Model.initial n) he]

/-- Arbitrary auxiliary suprema remain measurable when only a finite birth
word and the natural-valued cutoff are observed. -/
theorem measurableSet_of_localBirth_cutoff_prefix (l : ℝ) (N : ℕ) {E : Set (ℕ → ℝ)}
    (hE : ∀ u v, localSafeCutoff l u = localSafeCutoff l v →
      (∀ i < N, localBirth l u i = localBirth l v i) → (u ∈ E ↔ v ∈ E)) : MeasurableSet E := by
  let f : (ℕ → ℝ) → ℕ × (Fin N → Bool) :=
    fun u ↦ (localSafeCutoff l u, fun i ↦ localBirth l u i)
  have hf : Measurable f := (measurable_localSafeCutoff l).prodMk
    (Measurable.of_eval (fun i ↦ measurable_localBirth l i))
  have himage : MeasurableSet (f '' E) := (Set.to_countable _).measurableSet
  have heq : f ⁻¹' (f '' E) = E := by
    ext u
    constructor
    · rintro ⟨v, hv, hvu⟩
      exact (hE v u (congrArg Prod.fst hvu)
        (fun i hi ↦ congrFun (congrArg Prod.snd hvu) ⟨i, hi⟩)).mp hv
    · intro hu
      exact ⟨u, hu, rfl⟩
  rw [← heq]
  exact hf himage

/-- Failure of a single multiplier for every initial state, complex tilt and
pair of times after the source cutoff. -/
def localProfileMomentBad (p η r x D l : ℝ) : Set (ℕ → ℝ) :=
  {u | (∀ i, 0 < (localWalk l u i : ℝ)) ∧ ∃ n j N : ℕ,
    localSafeCutoff l u ≤ j ∧ 1 ≤ j ∧ j ≤ N ∧ ∃ z : ℂ,
      dist z (x : ℂ) < r ∧
        D * (j : ℝ) ^ (-η) < localProfileMomentDifference l u n z p j N}

theorem measurableSet_localProfileMomentBad (p η r x D l : ℝ) :
    MeasurableSet (localProfileMomentBad p η r x D l) := by
  have hsurv : MeasurableSet {u : ℕ → ℝ | ∀ i, 0 < (localWalk l u i : ℝ)} := by
    have hh := MeasurableSet.iInter (fun i ↦
      measurableSet_lt (measurable_const : Measurable (fun _ : ℕ → ℝ ↦ (0 : ℝ)))
        (measurable_localWalk_real l i))
    convert hh using 1
    ext u
    simp
  have hslice (n j N : ℕ) : MeasurableSet {u : ℕ → ℝ |
      localSafeCutoff l u ≤ j ∧ 1 ≤ j ∧ j ≤ N ∧ ∃ z : ℂ,
        dist z (x : ℂ) < r ∧ D * (j : ℝ) ^ (-η) < localProfileMomentDifference l u n z p j N} := by
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
  simp only [localProfileMomentBad, mem_ofPred_eq, mem_inter_iff, mem_iUnion]

noncomputable def localProfileUniformLogEnvelope (M B : ℝ) (J : ℕ) : ℝ :=
  (Real.exp 2 + 1) * (B + J) + (Real.exp 2 + 1) ^ 2 * (2 * M ^ 2)

/-- An explicit multiplier determined by three deterministic envelope levels. -/
noncomputable def localProfileMomentEnvelope (M B : ℝ) (J : ℕ) (p η : ℝ) : ℝ :=
  (4 * (2 : ℝ) ^ p) *
    ((Real.exp 2 / (Real.exp (-localProfileUniformLogEnvelope M B J) * (1 / (M + 1)))) ^ p *
      (2 : ℝ) ^ p * Real.exp (localProfileUniformLogEnvelope M B J)) / η

theorem localProfileMomentEnvelope_nonneg {M B p η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) (J : ℕ) :
    0 ≤ localProfileMomentEnvelope M B J p η := by
  unfold localProfileMomentEnvelope
  positivity


/-- Explicit good-event control of every conditional profile moment tail. -/
theorem localProfileMomentDifference_le_envelope {l M B p η : ℝ} (hl : 1 < l)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (u : ℕ → ℝ) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hcut : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B)
    (K : ℕ) (hK : localSafeCutoff l u ≤ K)
    (n : ℕ) (z : ℂ) (hz0 : 0 ≤ z.re) (hzr : z.re < profileRoot l)
    (hpz : p * z.re < 2 * profileRoot l)
    (he : complexProfileMomentExponent l z p ≤ -1 - η)
    (j N : ℕ) (hJj : localSafeCutoff l u ≤ j) (hj : 1 ≤ j) (hjN : j ≤ N) :
    localProfileMomentDifference l u n z p j N ≤
      localProfileMomentEnvelope M B K p η * (j : ℝ) ^ (-η) := by
  let E := localProfileUniformLogEnvelope M B K
  let A := Real.exp (-E)
  let B₁ := Real.exp E
  let c : ℝ := 1 / (M + 1)
  let Q : ℝ := (Real.exp 2 / (A * c)) ^ p * (2 : ℝ) ^ p * B₁
  have hA : 0 < A := Real.exp_pos _
  have hB₁ : 0 ≤ B₁ := (Real.exp_pos _).le
  have hc : 0 < c := by dsimp only [c]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
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
  have hcount := localProfile_count_lower l u hM hs hr
  have hClower : ∀ k ≥ localSafeCutoff l u,
      A * ((k + 1 : ℕ) : ℝ) ^ (growthFactor l * ((Complex.exp z).re - 1)) ≤
        ‖Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1
          (localSafeCutoff l u) (k + 1)‖ := by
    intro k hk
    apply le_trans _ (localProfile_complex_polynomial_lower hl hM hB u hs hr hcut hcenter z hz hk)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hE))
      (Real.rpow_nonneg (by positivity) _)
  have hCupper : ∀ k,
      Model.realNormalizer (‖Complex.exp z‖ ^ p) (localBirth l u) 1 k ≤
        B₁ * ((k + 1 : ℕ) : ℝ) ^ (growthFactor l * (Real.exp (p * z.re) - 1)) := by
    intro k
    apply (localProfile_real_polynomial_upper hl hM hB u hs hr hcenter z hz0 hp.le hpz k).trans
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hE) (Real.rpow_nonneg (by positivity) _)
  have hC : Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1
      (localSafeCutoff l u) N ≠ 0 := by
    rw [localNormalizer_eq_exp_centered l u hs hcut N z hz]
    exact Complex.exp_ne_zero _
  have hw : 1 ≤ ‖Complex.exp z‖ := by
    rw [Complex.norm_exp]
    exact Real.one_le_exp_iff.mpr hz0
  have hwupper : ‖Complex.exp z‖ ≤ Real.exp 2 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    linarith [profileRoot_lt_one hl]
  have hwp : 1 ≤ ‖Complex.exp z‖ ^ p := Real.one_le_rpow hw hp0
  have hconstant : (‖Complex.exp z‖ / (A * c)) ^ p * (2 : ℝ) ^ p * B₁ ≤ Q := by
    apply mul_le_mul_of_nonneg_right _ hB₁
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
    exact Real.rpow_le_rpow (div_nonneg (norm_nonneg _) (mul_pos hA hc).le)
      (div_le_div_of_nonneg_right hwupper (mul_pos hA hc).le) hp0
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
        ∑ k ∈ Finset.Ico j N, Model.prescribedShiftedMomentBound (Complex.exp z) (localBirth l u)
          (Model.initial n) (localSafeCutoff l u) p k := hm
    _ ≤ (4 * (2 : ℝ) ^ p) *
        ∑ k ∈ Finset.Ico j N, Q * ((k + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k hk
      have hJk := hJj.trans (Finset.mem_Ico.mp hk).1
      have hb := (Model.prescribedShiftedMomentBound_complex_le (Complex.exp z) hw hp0
        (localBirth l u) n (localSafeCutoff l u) k hJk (hpos (k + 1))).trans
        (Model.profile_moment_ratio_le (norm_nonneg _) hp0 hA hB₁ hc
          (by positivity) (zero_le_one.trans (Model.one_le_realNormalizer hwp (localBirth l u) 1 k))
          (hClower k hJk) (hcount k) (hCupper k))
      rw [hexp] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg (by positivity) _))
    _ = (4 * (2 : ℝ) ^ p) * Q *
        ∑ k ∈ Finset.Ico j N, ((k + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (4 * (2 : ℝ) ^ p) * Q * ((j : ℝ) ^ (-η) / η) :=
      mul_le_mul_of_nonneg_left (sum_complex_profile_moment_le hη he hj hjN) (by positivity)
    _ = _ := by dsimp only [Q, A, B₁, c, E, localProfileMomentEnvelope]; ring


/-- The shared moment-tail multiplier is tight under the actual uniform law,
using the count, cutoff and centered reciprocal-sum tightness theorems. -/
theorem localProfileMomentBad_uniform_tight {l₀ p η r x : ℝ} (hl₀ : 1 < l₀)
    (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < r →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ l ≥ l₀,
      uniformLaw.real (localProfileMomentBad p η r x D l) ≤ ε := by
  have heps : 0 < ε / 3 := by positivity
  obtain ⟨M, hM, hMtight⟩ := positiveReciprocal_uniform_tight hl₀ heps
  obtain ⟨K, hKtight⟩ := localSafeCutoff_uniform_tight hl₀ heps
  obtain ⟨B, hB, hBtight⟩ := localCenteredReciprocal_uniform_tight hl₀ heps
  let D := localProfileMomentEnvelope M B K p η
  refine ⟨D, localProfileMomentEnvelope_nonneg hM hη K, ?_⟩
  intro l hl
  have hl1 := hl₀.trans_le hl
  let F₁ : Set (ℕ → ℝ) := {u | ∃ k, M < positiveReciprocal l u k}
  let F₂ : Set (ℕ → ℝ) := {u | K < localSafeCutoff l u}
  let F₃ : Set (ℕ → ℝ) := {u | ∃ k : ℕ, (∀ i ≤ k, 0 < (localWalk l u i : ℝ)) ∧
    B < |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) - growthFactor l * Real.log k|}
  have hsub : ∀ᵐ u ∂uniformLaw, u ∈ localProfileMomentBad p η r x D l → u ∈ F₁ ∪ F₂ ∪ F₃ := by
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
    obtain ⟨hz0, hzr, hpz, he⟩ := hwindow l hl z hz
    have hh := localProfileMomentDifference_le_envelope hl1 hM hB hp hp2 hη u hs hr hu
      hcenter K hK n z hz0 hzr hpz he j N hJj hj hjN
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

/-- The same fixed disk and moment order give an almost-sure finite multiplier,
with nonvanishing of all normalizers on that disk. -/
theorem localProfile_ae_moment_decay_on_window {l p η r x : ℝ} (hl : 1 < l)
    (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hwindow : ∀ z : ℂ, dist z (x : ℂ) < r →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
      ∃ D : ℝ, 0 ≤ D ∧
        (∀ z : ℂ, dist z (x : ℂ) < r → ∀ k ≥ localSafeCutoff l u,
          Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1 (localSafeCutoff l u) k ≠ 0) ∧
        ∀ (n : ℕ) (z : ℂ), dist z (x : ℂ) < r → ∀ j N : ℕ,
          localSafeCutoff l u ≤ j → 1 ≤ j → j ≤ N →
          localProfileMomentDifference l u n z p j N ≤ D * (j : ℝ) ^ (-η) := by
  filter_upwards [ae_tendsto_finiteLocalCenteredReciprocal hl,
    positiveReciprocal_ae_uniform_bounded hl, localSafeCutoff_ae_bddAbove hl]
    with u hconv hratio hcut
  intro hs
  obtain ⟨M₀, hM₀⟩ := hratio
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hr : ∀ k, positiveReciprocal l u k ≤ M :=
    fun k ↦ (hM₀ l le_rfl k).trans (le_max_left _ _)
  obtain ⟨B, hB, hBbound⟩ := (Metric.isBounded_range_of_tendsto _ hconv).exists_pos_norm_le
  have hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B := by
    intro k
    have hh := hBbound (finiteLocalCenteredReciprocal l u k) ⟨k, rfl⟩
    simpa only [Real.norm_eq_abs, finiteLocalCenteredReciprocal, localBirthCoefficient,
      ite_eq_left (show ∀ i ≤ k, 0 < (localWalk l u i : ℝ) from fun i _ ↦ hs i),
      one_mul, growthFactor] using hh
  refine ⟨localProfileMomentEnvelope M B (localSafeCutoff l u) p η,
    localProfileMomentEnvelope_nonneg hM hη _, ?_, ?_⟩
  · intro z hz k _
    have hzr := (hwindow z hz).2.1
    rw [localNormalizer_eq_exp_centered l u hs hcut k z (by linarith [profileRoot_pos hl])]
    exact Complex.exp_ne_zero _
  · intro n z hz j N hJj hj hjN
    obtain ⟨hz0, hzr, hpz, he⟩ := hwindow z hz
    exact localProfileMomentDifference_le_envelope hl hM hB.le hp hp2 hη u hs hr hcut
      hcenter (localSafeCutoff l u) le_rfl n z hz0 hzr hpz he j N hJj hj hjN

/-- One common choice of disk, moment order and decay exponent supports both
the almost-sure conditional estimates and a multiplier tight uniformly in λ. -/
theorem exists_localProfile_uniform_tight_moment_decay {l₀ x : ℝ} (hl₀ : 1 < l₀)
    (hx : 0 < x) (hxr : x < profileRoot l₀) :
    ∃ p ∈ Set.Ioo (1 : ℝ) 2, ∃ η : ℝ, 0 < η ∧ ∃ r > 0,
      (∀ l ≥ l₀, ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
        ∃ D : ℝ, 0 ≤ D ∧
          (∀ z : ℂ, dist z (x : ℂ) < r → ∀ k ≥ localSafeCutoff l u,
            Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1 (localSafeCutoff l u) k ≠ 0) ∧
          ∀ (n : ℕ) (z : ℂ), dist z (x : ℂ) < r → ∀ j N : ℕ,
            localSafeCutoff l u ≤ j → 1 ≤ j → j ≤ N →
            localProfileMomentDifference l u n z p j N ≤ D * (j : ℝ) ^ (-η)) ∧
      ∀ ε > (0 : ℝ), ∃ D : ℝ, 0 ≤ D ∧ ∀ l ≥ l₀,
        uniformLaw.real (localProfileMomentBad p η r x D l) ≤ ε := by
  obtain ⟨p, hp, η, hη, r, hr, hwindow⟩ := exists_localProfile_moment_disk hl₀ hx hxr
  refine ⟨p, hp, η, hη, r, hr, ?_, ?_⟩
  · intro l hl
    exact localProfile_ae_moment_decay_on_window (hl₀.trans_le hl) hp.1 hp.2.le hη (hwindow l hl)
  · intro ε hε
    exact localProfileMomentBad_uniform_tight hl₀ hp.1 hp.2.le hη hwindow hε

end HeightPaper.CountCoupling
