module

public import HeightPaper.Probability.ReciprocalWalkLimit

/-!
# The uniform reciprocal limit for the actual local walk

This module chooses the centered harmonic limit from the constructed
martingale and combines its quantitative tails with the uniform walk controls.
The source limit retains both survival and the Euler--Mascheroni correction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical

namespace HeightPaper.CountCoupling

noncomputable def centeredBirthFiltration (l : ℝ) : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  independentPastFiltration (centeredLocalBirth l)
    (fun k ↦ (measurable_centeredLocalBirth l k).stronglyMeasurable)

private theorem centeredBirth_adapted (l : ℝ) (k : ℕ) :
    StronglyMeasurable[centeredBirthFiltration l (k + 1)] (centeredLocalBirth l k) :=
  stronglyMeasurable_independentPastFiltration _ _ k

private theorem centeredBirth_zero {l : ℝ} (hl : 0 ≤ l) (k : ℕ) :
    uniformLaw[centeredLocalBirth l k | centeredBirthFiltration l k] =ᵐ[uniformLaw] 0 :=
  condExp_independentPastFiltration_eq_zero uniformLaw (centeredLocalBirth l)
    (fun j ↦ (measurable_centeredLocalBirth l j).stronglyMeasurable)
    (centeredLocalBirth_independent l) (integral_centeredLocalBirth hl) k

private theorem centeredBirth_bound {l : ℝ} (hl : 0 ≤ l) (k : ℕ) :
    ∀ᵐ u ∂uniformLaw, ‖centeredLocalBirth l k u‖ ≤ 1 :=
  Eventually.of_forall (norm_centeredLocalBirth_le_one hl k)

/-- The source's centered harmonic limit `Z'`, from the actual birth martingale. -/
noncomputable def sourceBirthHarmonicLimit (l : ℝ) (u : ℕ → ℝ) : ℝ :=
  weightedDifferenceLimit uniformLaw (centeredBirthFiltration l) (centeredLocalBirth l) u /
    localDrift l

theorem measurable_sourceBirthHarmonicLimit (l : ℝ) : Measurable (sourceBirthHarmonicLimit l) := by
  have hm : StronglyMeasurable
      (weightedDifferenceLimit uniformLaw (centeredBirthFiltration l) (centeredLocalBirth l)) :=
    Filtration.stronglyMeasurable_limit_process'
  exact hm.measurable.div_const _

theorem sourceBirthHarmonicLimit_ae_tendsto {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, Tendsto (sourceBirthCenteredSum l u) atTop
      (𝓝 (sourceBirthHarmonicLimit l u)) := by
  have hl0 := zero_le_one.trans hl.le
  filter_upwards [ae_tendsto_weightedDifferenceSum uniformLaw (centeredBirthFiltration l)
    (centeredLocalBirth l) (centeredBirth_adapted l) (centeredBirth_bound hl0)
    (centeredBirth_zero hl0)] with u hu
  apply (hu.div_const (localDrift l)).congr
  intro n
  exact (sourceBirthCenteredSum_eq hl u n).symm

/-- Exact uniform numerical bound for every centered harmonic tail. -/
theorem sourceBirthHarmonicLimit_tail_l2 {l : ℝ} (hl : 1 < l) (N : ℕ) :
    eLpNorm (fun u ↦ sourceBirthHarmonicLimit l u - sourceBirthCenteredSum l u N) 2 uniformLaw ≤
      ‖(localDrift l)⁻¹‖ₑ * ENNReal.ofReal
        ((∑' k : ℕ, 1 / ((k + N + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ)⁻¹) := by
  have hl0 := zero_le_one.trans hl.le
  have hbase := eLpNorm_weightedDifference_tail_two_le uniformLaw (centeredBirthFiltration l)
    (centeredLocalBirth l) (centeredBirth_adapted l) (centeredBirth_bound hl0)
    (centeredBirth_zero hl0) N
  have heq : (fun u ↦ sourceBirthHarmonicLimit l u - sourceBirthCenteredSum l u N) =
      (localDrift l)⁻¹ • (fun u ↦
        weightedDifferenceLimit uniformLaw (centeredBirthFiltration l) (centeredLocalBirth l) u -
          weightedDifferenceSum (centeredLocalBirth l) N u) := by
    funext u
    rw [sourceBirthCenteredSum_eq hl]
    dsimp only [sourceBirthHarmonicLimit, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact eLpNorm_const_smul_le.trans (mul_le_mul le_rfl hbase zero_le zero_le)

/-- The centered harmonic series converges in probability uniformly over
all parameters above a fixed supercritical lower endpoint. -/
theorem sourceBirthCenteredSum_uniform_convergence {l₀ : ℝ} (hl₀ : 1 < l₀)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ≥ l₀,
      uniformLaw.real {u | ε ≤ |sourceBirthHarmonicLimit l u - sourceBirthCenteredSum l u n|} < η := by
  let b : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal ((localDrift l₀)⁻¹) * ENNReal.ofReal
    ((∑' k : ℕ, 1 / ((k + n + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ)⁻¹)
  have ht : Tendsto (fun n : ℕ ↦ ∑' k : ℕ, 1 / ((k + n + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_sum_nat_add (fun k : ℕ ↦ 1 / ((k + 1 : ℕ) : ℝ) ^ 2)
  have hr : Tendsto (fun n : ℕ ↦
      (∑' k : ℕ, 1 / ((k + n + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ)⁻¹) atTop (𝓝 0) := by
    have hh := ht.sqrt
    rw [Real.sqrt_zero] at hh
    simpa only [Real.sqrt_eq_rpow, one_div] using hh
  have he : Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      ((∑' k : ℕ, 1 / ((k + n + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hr
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa only [b, mul_zero] using ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal ((localDrift l₀)⁻¹)) he (Or.inr ENNReal.ofReal_ne_top)
  let F : ℕ → {l : ℝ // l₀ ≤ l} → (ℕ → ℝ) → ℝ :=
    fun n l u ↦ sourceBirthHarmonicLimit l u - sourceBirthCenteredSum l u n
  have hF : ∀ n l, eLpNorm (F n l) 2 uniformLaw ≤ b n := by
    intro n l
    exact (sourceBirthHarmonicLimit_tail_l2 (hl₀.trans_le l.property) n).trans
      (mul_le_mul (localDrift_inv_uniform_le hl₀ l.property) le_rfl zero_le zero_le)
  obtain ⟨N, hN⟩ := uniform_measureReal_abs_lt_of_eLpNorm_bound uniformLaw F b hb hF hε hη
  exact ⟨N, fun n hn l hl ↦ hN n hn ⟨l, hl⟩⟩

/-- The finite survival-gated reciprocal sum, with the source's centering. -/
noncomputable def finiteLocalCenteredReciprocal (l : ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  (if ∀ i ≤ n, 0 < (localWalk l u i : ℝ) then (1 : ℝ) else 0) *
    ((∑ k ∈ Finset.range n,
      (if localBirth l u k then (1 : ℝ) else 0) / (localWalk l u (k + 1) : ℝ)) -
      l / (l - 1) * Real.log n)

/-- Corrected source limit: `1_survival * (Z' + γ * EM) + Z''`. -/
noncomputable def localBirthReciprocalLimit (l : ℝ) (u : ℕ → ℝ) : ℝ :=
  (if ∀ i, 0 < (localWalk l u i : ℝ) then (1 : ℝ) else 0) *
    (sourceBirthHarmonicLimit l u + l / (l - 1) * Real.eulerMascheroniConstant) +
    localBirthReciprocalCorrection l u

theorem measurable_localBirthReciprocalLimit (l : ℝ) : Measurable (localBirthReciprocalLimit l) := by
  have hsurv : MeasurableSet {u : ℕ → ℝ | ∀ i, 0 < (localWalk l u i : ℝ)} := by
    have hh := MeasurableSet.iInter (fun i ↦
      measurableSet_lt (measurable_const : Measurable (fun _ : ℕ → ℝ ↦ (0 : ℝ)))
        (measurable_localWalk_real l i))
    convert hh using 1
    ext u
    simp
  exact ((measurable_const.ite hsurv measurable_const).mul
    ((measurable_sourceBirthHarmonicLimit l).add_const _)).add
      (measurable_localBirthReciprocalCorrection l)

/-- Almost-sure convergence to the explicitly chosen corrected limit. -/
theorem ae_tendsto_finiteLocalCenteredReciprocal {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, Tendsto (finiteLocalCenteredReciprocal l u) atTop
      (𝓝 (localBirthReciprocalLimit l u)) := by
  filter_upwards [sourceBirthHarmonicLimit_ae_tendsto hl,
    positiveReciprocal_ae_uniform_bounded hl,
    localWalk_ae_power_deviation (zero_le_one.trans hl.le)] with u hcenter hratio hdev
  obtain ⟨M, hM⟩ := hratio
  obtain ⟨Y, _, hY⟩ := hdev
  let S : ℕ → ℝ := fun k ↦ (localWalk l u k : ℝ)
  let w : ℕ → ℝ := fun i ↦ if localBirth l u (i - 1) then 1 else 0
  have hr : (∀ i, 0 < S i) → ∀ k, ((k + 1 : ℕ) : ℝ) / S (k + 1) ≤ max M 0 := by
    intro hs k
    have hk : 0 < localWalk l u (k + 1) := by
      have hs' : (0 : ℝ) < (localWalk l u (k + 1) : ℝ) := hs (k + 1)
      exact_mod_cast hs'
    have hh := (hM l le_rfl (k + 1)).trans (le_max_left M 0)
    simpa only [positiveReciprocal, ite_eq_left hk] using hh
  have hd : (∀ i, 0 < S i) → ∀ k,
      |S (k + 1) - localDrift l * (k + 1 : ℕ)| ≤
        Y * ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
    intro _ k
    simpa only [S, mul_comm] using hY (k + 1) (by omega)
  have hw : ∀ k, |w (k + 1)| ≤ 1 := by
    intro k
    dsimp only [w]
    split <;> norm_num
  have hc : Tendsto (fun n ↦ ∑ k ∈ Finset.range n,
      (w (k + 1) / localDrift l - l / (l - 1)) / (k + 1 : ℕ)) atTop
      (𝓝 (sourceBirthHarmonicLimit l u)) := by
    change Tendsto (fun n ↦ sourceBirthCenteredSum l u n) atTop
      (𝓝 (sourceBirthHarmonicLimit l u)) at hcenter
    simpa only [sourceBirthCenteredSum, w, Nat.add_sub_cancel] using hcenter
  have ht := tendsto_survival_weighted_reciprocal_sub_log S w (localDrift_pos hl)
    (le_max_right M 0) hr hd hw hc
  change Tendsto (fun n ↦ finiteLocalCenteredReciprocal l u n) atTop
    (𝓝 (localBirthReciprocalLimit l u))
  simpa only [S, w, Nat.add_sub_cancel, localBirthReciprocalCorrection,
    finiteLocalCenteredReciprocal, localBirthReciprocalLimit] using ht

/-- A common late lower barrier makes finite and infinite survival identical,
pathwise for every parameter above the lower endpoint. -/
theorem finite_survival_iff_of_not_lateLowerFailure {l₀ l : ℝ} (hl₀ : 1 < l₀)
    (hl : l₀ ≤ l) (u : ℕ → ℝ) (n : ℕ) (hu : u ∉ lateLowerFailure l₀ n) :
    (∀ i ≤ n, 0 < (localWalk l u i : ℝ)) ↔ ∀ i, 0 < (localWalk l u i : ℝ) := by
  refine ⟨?_, fun hs i _ ↦ hs i⟩
  intro hs i
  by_cases hi : i ≤ n
  · exact hs i hi
  have hn : n ≤ i := by omega
  have hlo : localDrift l₀ / 2 * i ≤ (localWalk l₀ u i : ℝ) :=
    le_of_not_gt (fun hbad ↦ hu ⟨i, hn, hbad⟩)
  have hmono : (localWalk l₀ u i : ℝ) ≤ (localWalk l u i : ℝ) := by
    exact_mod_cast localWalk_mono (zero_le_one.trans hl₀.le) hl u i
  have hpos : 0 < localDrift l₀ / 2 * i :=
    mul_pos (half_pos (localDrift_pos hl₀)) (by exact_mod_cast (show 0 < i by omega))
  exact hpos.trans_le (hlo.trans hmono)

private theorem localDrift_inv_real_le {l₀ l : ℝ} (hl₀ : 1 < l₀) (hl : l₀ ≤ l) :
    (localDrift l)⁻¹ ≤ (localDrift l₀)⁻¹ := by
  have hh := localDrift_inv_uniform_le hl₀ hl
  rw [Real.enorm_eq_ofReal (inv_nonneg.mpr (localDrift_pos (hl₀.trans_le hl)).le)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (inv_nonneg.mpr (localDrift_pos hl₀).le)).mp hh

private theorem sourceGamma_nonneg {l : ℝ} (hl : 1 < l) : 0 ≤ l / (l - 1) :=
  div_nonneg (zero_le_one.trans hl.le) (sub_nonneg.mpr hl.le)

private theorem sourceGamma_le {l₀ l : ℝ} (hl₀ : 1 < l₀) (hl : l₀ ≤ l) :
    l / (l - 1) ≤ (localDrift l₀)⁻¹ := by
  have hl1 := hl₀.trans_le hl
  have hd := localDrift_pos hl1
  have hγeq : birthThreshold l / localDrift l = l / (l - 1) := by
    unfold birthThreshold localDrift
    have hplus : 1 + l ≠ 0 := by linarith
    have hminus : l - 1 ≠ 0 := by linarith
    field_simp
  rw [← hγeq]
  exact (div_le_div_of_nonneg_right (birthThreshold_le_one (zero_le_one.trans hl1.le)) hd.le).trans
    (by simpa only [one_div] using localDrift_inv_real_le hl₀ hl)

/-- The three remainders on infinite survival: the centered harmonic tail,
the deterministic Euler--Mascheroni error, and the summable reciprocal tail. -/
theorem localBirthReciprocal_error_bound {l M Y : ℝ} (hl : 1 < l)
    (hM : 0 ≤ M) (u : ℕ → ℝ) (n : ℕ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hratio : ∀ k, positiveReciprocal l u k ≤ M)
    (hdev : ∀ k ≥ 1, |(localWalk l u k : ℝ) - k * localDrift l| ≤
      Y * (k : ℝ) ^ (3 / 4 : ℝ)) :
    |finiteLocalCenteredReciprocal l u n - localBirthReciprocalLimit l u| ≤
      |sourceBirthHarmonicLimit l u - sourceBirthCenteredSum l u n| +
        l / (l - 1) * |(harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant| +
        (localDrift l)⁻¹ * M * Y *
          ∑' k : ℕ, ((k + n + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
  let S : ℕ → ℝ := fun k ↦ (localWalk l u k : ℝ)
  let w : ℕ → ℝ := fun i ↦ if localBirth l u (i - 1) then 1 else 0
  have hpos : ∀ k, 0 < S (k + 1) := fun k ↦ hs (k + 1)
  have hr : ∀ k, ((k + 1 : ℕ) : ℝ) / S (k + 1) ≤ M := by
    intro k
    have hk : 0 < localWalk l u (k + 1) := by exact_mod_cast hs (k + 1)
    simpa only [positiveReciprocal, ite_eq_left hk] using hratio (k + 1)
  have hy : ∀ k, |S (k + 1) - localDrift l * (k + 1 : ℕ)| ≤
      Y * ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
    intro k
    simpa only [S, mul_comm] using hdev (k + 1) (by omega)
  have hw : ∀ k, |w (k + 1)| ≤ 1 := by
    intro k
    dsimp only [w]
    split <;> norm_num
  have htail := abs_reciprocalWalkError_tail_le S w (localDrift_pos hl) hM hpos hr hy hw n
  have htail' : |(∑ k ∈ Finset.range n, reciprocalWalkError S (localDrift l) k * w (k + 1)) -
      ∑' k, reciprocalWalkError S (localDrift l) k * w (k + 1)| ≤
      (localDrift l)⁻¹ * M * Y * ∑' k : ℕ, ((k + n + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
    rw [abs_sub_comm]
    exact htail
  have hsplit : (∑ k ∈ Finset.range n,
      (if localBirth l u k then (1 : ℝ) else 0) / (localWalk l u (k + 1) : ℝ)) -
      l / (l - 1) * Real.log n =
      (∑ k ∈ Finset.range n, reciprocalWalkError S (localDrift l) k * w (k + 1)) +
        sourceBirthCenteredSum l u n + l / (l - 1) * ((harmonic n : ℝ) - Real.log n) := by
    simpa only [S, w, Nat.add_sub_cancel, sourceBirthCenteredSum] using
      sum_weighted_reciprocal_centered_eq S w (localDrift l) (l / (l - 1)) n
  have hcorr : localBirthReciprocalCorrection l u =
      ∑' k, reciprocalWalkError S (localDrift l) k * w (k + 1) := by
    change survivalReciprocalCorrection S w (localDrift l) = _
    rw [survivalReciprocalCorrection, ite_eq_left (show ∀ i, 0 < S i from hs)]
  have hfinite : ∀ i ≤ n, 0 < (localWalk l u i : ℝ) := fun i _ ↦ hs i
  have heq : finiteLocalCenteredReciprocal l u n - localBirthReciprocalLimit l u =
      ((∑ k ∈ Finset.range n, reciprocalWalkError S (localDrift l) k * w (k + 1)) -
        ∑' k, reciprocalWalkError S (localDrift l) k * w (k + 1)) +
      (sourceBirthCenteredSum l u n - sourceBirthHarmonicLimit l u) +
      l / (l - 1) * ((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) := by
    dsimp only [finiteLocalCenteredReciprocal, localBirthReciprocalLimit]
    rw [ite_eq_left hfinite, ite_eq_left hs, one_mul, hcorr, hsplit]
    ring
  rw [heq]
  calc
    _ ≤ |(∑ k ∈ Finset.range n, reciprocalWalkError S (localDrift l) k * w (k + 1)) -
          ∑' k, reciprocalWalkError S (localDrift l) k * w (k + 1)| +
        |sourceBirthCenteredSum l u n - sourceBirthHarmonicLimit l u| +
        |l / (l - 1) * ((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (localDrift l)⁻¹ * M * Y *
          (∑' k : ℕ, ((k + n + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) +
        |sourceBirthCenteredSum l u n - sourceBirthHarmonicLimit l u| +
        l / (l - 1) * |(harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant| := by
      rw [abs_mul, abs_of_nonneg (sourceGamma_nonneg hl)]
      exact add_le_add (add_le_add htail' le_rfl) le_rfl
    _ = _ := by rw [abs_sub_comm (sourceBirthCenteredSum l u n)]; ring

/-- Weakly uniform convergence of the source reciprocal sums, including
finite survival indicators, over the entire supercritical half-line. -/
theorem finiteLocalCenteredReciprocal_uniform_convergence {l₀ : ℝ} (hl₀ : 1 < l₀)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ≥ l₀,
      uniformLaw.real {u | ε ≤ |finiteLocalCenteredReciprocal l u n - localBirthReciprocalLimit l u|} < η := by
  have heps : 0 < ε / 3 := by positivity
  have heta : 0 < η / 4 := by positivity
  obtain ⟨M, hM, hMtight⟩ := positiveReciprocal_uniform_tight hl₀ heta
  obtain ⟨Y, hY, hYtight⟩ := localWalk_power_deviation_uniform_tight heta
  have hH : Tendsto (fun n : ℕ ↦ (localDrift l₀)⁻¹ *
      |(harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, mul_zero] using
      ((Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant).abs).const_mul
        (localDrift l₀)⁻¹
  have hT : Tendsto (fun n : ℕ ↦ (localDrift l₀)⁻¹ * M * Y *
      ∑' k : ℕ, ((k + n + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_reciprocalWalk_envelope_tail.const_mul
      ((localDrift l₀)⁻¹ * M * Y)
  obtain ⟨NH, hNH⟩ := eventually_atTop.mp (hH.eventually (Iio_mem_nhds heps))
  obtain ⟨NT, hNT⟩ := eventually_atTop.mp (hT.eventually (Iio_mem_nhds heps))
  obtain ⟨NC, hNC⟩ := sourceBirthCenteredSum_uniform_convergence hl₀ heps heta
  obtain ⟨NS, hNS⟩ := eventually_atTop.mp
    ((lateLowerFailure_tendsto hl₀).eventually (Iio_mem_nhds heta))
  refine ⟨max (max NH NT) (max NC NS), ?_⟩
  intro n hn l hl
  have hnH : NH ≤ n := by omega
  have hnT : NT ≤ n := by omega
  have hnC : NC ≤ n := by omega
  have hnS : NS ≤ n := by omega
  have hl1 := hl₀.trans_le hl
  let F₁ : Set (ℕ → ℝ) := {u | ∃ k, M < positiveReciprocal l u k}
  let F₂ : Set (ℕ → ℝ) := {u | ∃ (k : ℕ), 1 ≤ k ∧
    Y * (k : ℝ) ^ (3 / 4 : ℝ) < |(localWalk l u k : ℝ) - k * localDrift l|}
  let F₃ : Set (ℕ → ℝ) := {u | ε / 3 ≤ |sourceBirthHarmonicLimit l u - sourceBirthCenteredSum l u n|}
  let F₄ : Set (ℕ → ℝ) := lateLowerFailure l₀ n
  have hsub : {u | ε ≤ |finiteLocalCenteredReciprocal l u n - localBirthReciprocalLimit l u|} ⊆
      F₁ ∪ F₂ ∪ F₃ ∪ F₄ := by
    intro u hu
    change ε ≤ |finiteLocalCenteredReciprocal l u n - localBirthReciprocalLimit l u| at hu
    by_cases h₁ : u ∈ F₁
    · exact Or.inl (Or.inl (Or.inl h₁))
    by_cases h₂ : u ∈ F₂
    · exact Or.inl (Or.inl (Or.inr h₂))
    by_cases h₃ : u ∈ F₃
    · exact Or.inl (Or.inr h₃)
    by_cases h₄ : u ∈ F₄
    · exact Or.inr h₄
    by_cases hs : ∀ i, 0 < (localWalk l u i : ℝ)
    · have hr : ∀ k, positiveReciprocal l u k ≤ M := by
        intro k
        exact le_of_not_gt (fun hh ↦ h₁ ⟨k, hh⟩)
      have hy : ∀ k ≥ 1, |(localWalk l u k : ℝ) - k * localDrift l| ≤
          Y * (k : ℝ) ^ (3 / 4 : ℝ) := by
        intro k hk
        exact le_of_not_gt (fun hh ↦ h₂ ⟨k, hk, hh⟩)
      have hc : |sourceBirthHarmonicLimit l u - sourceBirthCenteredSum l u n| < ε / 3 :=
        lt_of_not_ge h₃
      have hh : l / (l - 1) * |(harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant| < ε / 3 :=
        (mul_le_mul_of_nonneg_right (sourceGamma_le hl₀ hl) (abs_nonneg _)).trans_lt (hNH n hnH)
      have ht : (localDrift l)⁻¹ * M * Y *
          (∑' k : ℕ, ((k + n + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) < ε / 3 := by
        apply lt_of_le_of_lt _ (hNT n hnT)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (localDrift_inv_real_le hl₀ hl) hM) hY.le)
            (tsum_nonneg (fun k ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _))
      have hb := localBirthReciprocal_error_bound hl1 hM u n hs hr hy
      exact False.elim (by linarith)
    · have hfinite : ¬∀ i ≤ n, 0 < (localWalk l u i : ℝ) :=
        fun hh ↦ hs ((finite_survival_iff_of_not_lateLowerFailure hl₀ hl u n h₄).mp hh)
      have hz : finiteLocalCenteredReciprocal l u n - localBirthReciprocalLimit l u = 0 := by
        simp only [finiteLocalCenteredReciprocal, localBirthReciprocalLimit, ite_eq_right hs,
          ite_eq_right hfinite, zero_mul, localBirthReciprocalCorrection,
          survivalReciprocalCorrection, add_zero, sub_zero]
      rw [hz, abs_zero] at hu
      exact False.elim (not_le_of_gt hε hu)
  have hbound : uniformLaw.real (F₁ ∪ F₂ ∪ F₃ ∪ F₄) ≤
      uniformLaw.real F₁ + uniformLaw.real F₂ + uniformLaw.real F₃ + uniformLaw.real F₄ :=
    (measureReal_union_le _ _).trans (add_le_add
      ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)) le_rfl)
  apply (measureReal_mono (h₂ := measure_ne_top _ _) hsub).trans_lt
  apply hbound.trans_lt
  have h₁ := hMtight l hl
  have h₂ := hYtight l (zero_le_one.trans hl1.le)
  have h₃ := hNC n hnC l hl
  have h₄ := hNS n hnS
  linarith

/-- Tightness of the corrected limiting random variables, uniformly over
all supercritical parameters bounded away from one. -/
theorem localBirthReciprocalLimit_uniform_tight {l₀ : ℝ} (hl₀ : 1 < l₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ l ≥ l₀,
      uniformLaw.real {u | A < |localBirthReciprocalLimit l u|} ≤ ε := by
  obtain ⟨A, hA, hbound⟩ := localCenteredReciprocal_uniform_tight hl₀ hε
  refine ⟨A, hA, ?_⟩
  intro l hl
  have hsub : ∀ᵐ u ∂uniformLaw, A < |localBirthReciprocalLimit l u| →
      ∃ n : ℕ, (∀ i ≤ n, 0 < (localWalk l u i : ℝ)) ∧
        A < |(∑ k ∈ Finset.range n,
          (if localBirth l u k then (1 : ℝ) else 0) / (localWalk l u (k + 1) : ℝ)) -
          l / (l - 1) * Real.log n| := by
    filter_upwards [ae_tendsto_finiteLocalCenteredReciprocal (hl₀.trans_le hl)] with u hu
    intro hb
    obtain ⟨n, hn⟩ := (hu.abs.eventually (Ioi_mem_nhds hb)).exists
    by_cases hs : ∀ i ≤ n, 0 < (localWalk l u i : ℝ)
    · exact ⟨n, hs, by simpa only [finiteLocalCenteredReciprocal, ite_eq_left hs, one_mul] using hn⟩
    · have hz : A < 0 := by
        simpa only [finiteLocalCenteredReciprocal, ite_eq_right hs, zero_mul, abs_zero] using hn
      exact False.elim (not_lt_of_ge hA hz)
  have hm := measure_mono_ae hsub
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hm).trans (hbound l hl)

end HeightPaper.CountCoupling
