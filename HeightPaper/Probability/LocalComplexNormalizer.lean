module

public import HeightPaper.Probability.LocalReciprocalLimit
public import HeightPaper.Probability.SafeCutoff
public import HeightPaper.Model.ComplexNormalizer
public import HeightPaper.Model.CoupledPrescribedWalk

/-!
# The analytic normalizer for the actual local birth walk

The cutoff is the paper's last unsafe index. The analytic correction retains
`(exp z - 1) * (Z - prefix_J)`, including the multiplier omitted from the
manuscript's displayed formula for the limiting correction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical

namespace HeightPaper.CountCoupling

/-- The common safe radius in the complex weight, before exponential tilting. -/
noncomputable def localNormalizerRadius (l : ℝ) : ℝ :=
  Real.exp (2 * profileRoot l) + 1

theorem localNormalizerRadius_pos (l : ℝ) : 0 < localNormalizerRadius l := by
  unfold localNormalizerRadius
  positivity

theorem localNormalizerRadius_le {l : ℝ} (hl : 1 < l) :
    localNormalizerRadius l ≤ Real.exp 2 + 1 := by
  unfold localNormalizerRadius
  gcongr
  linarith [profileRoot_lt_one hl]

theorem norm_exp_sub_one_lt_localNormalizerRadius {l : ℝ} (z : ℂ)
    (hz : z.re < 2 * profileRoot l) : ‖Complex.exp z - 1‖ < localNormalizerRadius l := by
  calc
    ‖Complex.exp z - 1‖ ≤ ‖Complex.exp z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = Real.exp z.re + 1 := by rw [Complex.norm_exp, norm_one]
    _ < localNormalizerRadius l := by
      simpa only [localNormalizerRadius, add_comm] using
        add_lt_add_right (Real.exp_lt_exp.mpr hz) 1

/-- The reciprocal coefficient at draw `k`, whose denominator is the count
immediately after the corresponding birth. -/
noncomputable def localBirthCoefficient (l : ℝ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  (if localBirth l u k then (1 : ℝ) else 0) / (localWalk l u (k + 1) : ℝ)

theorem measurable_localBirthCoefficient (l : ℝ) (k : ℕ) :
    Measurable (fun u ↦ localBirthCoefficient l u k) := by
  unfold localBirthCoefficient
  exact ((measurable_of_countable (fun b : Bool ↦ if b then (1 : ℝ) else 0)).comp
    (measurable_localBirth l k)).div (measurable_localWalk_real l (k + 1))

theorem localBirthCoefficient_nonneg (l : ℝ) (u : ℕ → ℝ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ)) (k : ℕ) :
    0 ≤ localBirthCoefficient l u k := by
  unfold localBirthCoefficient
  split
  · exact div_nonneg zero_le_one (hs (k + 1)).le
  · simp

theorem localBirthCoefficient_le_one (l : ℝ) (u : ℕ → ℝ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ)) (k : ℕ) :
    localBirthCoefficient l u k ≤ 1 := by
  have hpos : 0 < localWalk l u (k + 1) := by exact_mod_cast hs (k + 1)
  have hone : (1 : ℝ) ≤ (localWalk l u (k + 1) : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ localWalk l u (k + 1) by omega)
  unfold localBirthCoefficient
  split
  · exact (div_le_one (hs (k + 1))).mpr hone
  · simp

theorem localBirthCoefficient_le_linear (l : ℝ) (u : ℕ → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M) (k : ℕ) :
    localBirthCoefficient l u k ≤ M / (k + 1 : ℕ) := by
  have hpos : 0 < localWalk l u (k + 1) := by exact_mod_cast hs (k + 1)
  have hh := hr (k + 1)
  simp only [positiveReciprocal, ite_eq_left hpos] at hh
  unfold localBirthCoefficient
  split
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < (k + 1 : ℕ))).mpr
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hh
  · simp only [zero_div]
    positivity

private theorem summable_reciprocal_square :
    Summable (fun k : ℕ ↦ 1 / ((k + 1 : ℕ) : ℝ) ^ 2) :=
  (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))

theorem localBirthCoefficient_square_summable (l : ℝ) (u : ℕ → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M) :
    Summable (fun k ↦ (localBirthCoefficient l u k) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k ↦ sq_nonneg _) _
    (summable_reciprocal_square.mul_left (M ^ 2))
  intro k
  have hb := pow_le_pow_left₀ (localBirthCoefficient_nonneg l u hs k)
    (localBirthCoefficient_le_linear l u hM hs hr k) 2
  simpa only [div_pow, mul_one_div] using hb

/-- The exact source cutoff makes every subsequent logarithmic factor safe. -/
theorem localBirthCoefficient_safe_after (l : ℝ) (u : ℕ → ℝ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hb : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    {k : ℕ} (hk : localSafeCutoff l u ≤ k) :
    localNormalizerRadius l * |localBirthCoefficient l u k| ≤ 1 / 2 := by
  rw [abs_of_nonneg (localBirthCoefficient_nonneg l u hs k)]
  have hh := localSafeCutoff_safe_after l u hb (show localSafeCutoff l u < k + 1 by omega)
  unfold localBirthCoefficient
  split
  · simpa only [localNormalizerRadius, mul_comm] using hh.le
  · simp


/-- Coefficients before the exact source cutoff are suppressed. This permits
one series on natural indices while retaining the physical time `n`. -/
noncomputable def localSafeBirthCoefficient (l : ℝ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  if localSafeCutoff l u ≤ k then localBirthCoefficient l u k else 0

noncomputable def localBirthPrefixAtCutoff (l : ℝ) (u : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (localSafeCutoff l u), localBirthCoefficient l u k

/-- The source's centered log product, using the sum of factor logarithms. -/
noncomputable def localCenteredNormalizerLog (l : ℝ) (u : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (Complex.exp z - 1) *
    (((∑ k ∈ Finset.range n, localSafeBirthCoefficient l u k) -
      l / (l - 1) * Real.log n : ℝ) : ℂ) +
    complexProductRemainder (Finset.range n) (localSafeBirthCoefficient l u) (Complex.exp z - 1)

/-- The named analytic correction. It is zero off infinite survival. -/
noncomputable def localNormalizerCorrection (l : ℝ) (u : ℕ → ℝ) (z : ℂ) : ℂ :=
  if ∀ i, 0 < (localWalk l u i : ℝ) then
    (Complex.exp z - 1) * ((localBirthReciprocalLimit l u - localBirthPrefixAtCutoff l u : ℝ) : ℂ) +
      ∑' k, complexLogRemainder ((Complex.exp z - 1) * (localSafeBirthCoefficient l u k : ℂ))
  else 0

theorem measurable_localSafeBirthCoefficient (l : ℝ) (k : ℕ) :
    Measurable (fun u ↦ localSafeBirthCoefficient l u k) :=
  (measurable_localBirthCoefficient l k).ite
    (measurableSet_le (measurable_localSafeCutoff l) measurable_const) measurable_const

theorem measurable_localBirthPrefixAtCutoff (l : ℝ) : Measurable (localBirthPrefixAtCutoff l) := by
  have hm : Measurable (fun p : (ℕ → ℝ) × ℕ ↦
      ∑ k ∈ Finset.range p.2, localBirthCoefficient l p.1 k) :=
    measurable_from_prod_countable_left (fun n ↦
      Finset.measurable_sum (Finset.range n) (fun k _ ↦ measurable_localBirthCoefficient l k))
  exact hm.comp (measurable_id.prodMk (measurable_localSafeCutoff l))

theorem measurable_localNormalizerCorrection (l : ℝ) (z : ℂ) :
    Measurable (fun u ↦ localNormalizerCorrection l u z) := by
  have hsurv : MeasurableSet {u : ℕ → ℝ | ∀ i, 0 < (localWalk l u i : ℝ)} := by
    have hh := MeasurableSet.iInter (fun i ↦
      measurableSet_lt (measurable_const : Measurable (fun _ : ℕ → ℝ ↦ (0 : ℝ)))
        (measurable_localWalk_real l i))
    convert hh using 1
    ext u
    simp
  apply Measurable.ite hsurv _ measurable_const
  apply Measurable.add
  · exact measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_localBirthReciprocalLimit l).sub (measurable_localBirthPrefixAtCutoff l)))
  · apply Measurable.tsum
    intro k
    have hm : Measurable (fun u : ℕ → ℝ ↦
        (Complex.exp z - 1) * (localSafeBirthCoefficient l u k : ℂ)) :=
      measurable_const.mul (Complex.measurable_ofReal.comp
        (measurable_localSafeBirthCoefficient l k))
    exact (measurable_const.add hm).clog.sub hm

private theorem sum_range_cut_eq_Ico {α : Type*} [AddCommMonoid α] (a : ℕ → α) (j n : ℕ) :
    (∑ k ∈ Finset.range n, if j ≤ k then a k else 0) = ∑ k ∈ Finset.Ico j n, a k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

theorem sum_localSafeBirthCoefficient (l : ℝ) (u : ℕ → ℝ) {n : ℕ}
    (hn : localSafeCutoff l u ≤ n) :
    (∑ k ∈ Finset.range n, localSafeBirthCoefficient l u k) =
      (∑ k ∈ Finset.range n, localBirthCoefficient l u k) - localBirthPrefixAtCutoff l u := by
  rw [show (∑ k ∈ Finset.range n, localSafeBirthCoefficient l u k) =
    ∑ k ∈ Finset.Ico (localSafeCutoff l u) n, localBirthCoefficient l u k from
      sum_range_cut_eq_Ico _ _ _]
  have hh := Finset.sum_range_add_sum_Ico (localBirthCoefficient l u) hn
  unfold localBirthPrefixAtCutoff
  linarith

theorem localSafeBirthCoefficient_square_summable (l : ℝ) (u : ℕ → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M) :
    Summable (fun k ↦ (localSafeBirthCoefficient l u k) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k ↦ sq_nonneg _) _
    (localBirthCoefficient_square_summable l u hM hs hr)
  intro k
  unfold localSafeBirthCoefficient
  split <;> simp [sq_nonneg]

theorem localSafeBirthCoefficient_safe (l : ℝ) (u : ℕ → ℝ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hb : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)}) (k : ℕ) :
    localNormalizerRadius l * |localSafeBirthCoefficient l u k| ≤ 1 / 2 := by
  unfold localSafeBirthCoefficient
  split
  · exact localBirthCoefficient_safe_after l u hs hb ‹_›
  · norm_num

/-- Actual almost-sure centered reciprocal convergence after the source cutoff. -/
theorem localSafeBirthCoefficient_ae_centered_limit {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
      Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.range n, localSafeBirthCoefficient l u k) -
        l / (l - 1) * Real.log n) atTop
        (𝓝 (localBirthReciprocalLimit l u - localBirthPrefixAtCutoff l u)) := by
  filter_upwards [ae_tendsto_finiteLocalCenteredReciprocal hl] with u hu
  intro hs
  have hraw : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.range n, localBirthCoefficient l u k) -
      l / (l - 1) * Real.log n) atTop (𝓝 (localBirthReciprocalLimit l u)) := by
    apply hu.congr
    intro n
    simp only [finiteLocalCenteredReciprocal, localBirthCoefficient,
      ite_eq_left (show ∀ i ≤ n, 0 < (localWalk l u i : ℝ) from fun i _ ↦ hs i), one_mul]
  apply (hraw.sub_const (localBirthPrefixAtCutoff l u)).congr'
  filter_upwards [eventually_ge_atTop (localSafeCutoff l u)] with n hn
  rw [sum_localSafeBirthCoefficient l u hn]
  ring

/-- Almost surely on survival the actual centered logarithmic product has
one analytic limit, uniformly on the entire safe exponential domain. -/
theorem localNormalizer_ae_analytic_limit {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw,
      AnalyticOnNhd ℂ (localNormalizerCorrection l u) {z : ℂ | z.re < 2 * profileRoot l} ∧
      ((∀ i, 0 < (localWalk l u i : ℝ)) →
        TendstoUniformlyOn (localCenteredNormalizerLog l u) (localNormalizerCorrection l u)
          atTop {z : ℂ | z.re < 2 * profileRoot l}) := by
  filter_upwards [localSafeBirthCoefficient_ae_centered_limit hl,
    positiveReciprocal_ae_uniform_bounded hl, localSafeCutoff_ae_bddAbove hl]
    with u hcenter hratio hcut
  by_cases hs : ∀ i, 0 < (localWalk l u i : ℝ)
  · obtain ⟨M, hM⟩ := hratio
    have hr : ∀ k, positiveReciprocal l u k ≤ max M 0 :=
      fun k ↦ (hM l le_rfl k).trans (le_max_left _ _)
    have hsquare := localSafeBirthCoefficient_square_summable l u (le_max_right M 0) hs hr
    have hsmall := localSafeBirthCoefficient_safe l u hs hcut
    have ha := complexNormalizerLimit_analyticOnNhd (localSafeBirthCoefficient l u)
      (localNormalizerRadius_pos l).le hsquare hsmall
      (localBirthReciprocalLimit l u - localBirthPrefixAtCutoff l u)
    have hc := complexNormalizerCentered_tendstoUniformlyOn (localSafeBirthCoefficient l u)
      (localNormalizerRadius_pos l).le hsquare hsmall (hcenter hs)
    constructor
    · change AnalyticOnNhd ℂ (fun z ↦ localNormalizerCorrection l u z) _
      have hg : AnalyticOnNhd ℂ (fun z : ℂ ↦ Complex.exp z - 1)
          {z : ℂ | z.re < 2 * profileRoot l} :=
        analyticOnNhd_cexp.sub analyticOnNhd_const
      have hh := ha.comp hg (fun z hz ↦ by
          simpa only [Metric.mem_ball, dist_zero_right] using
            norm_exp_sub_one_lt_localNormalizerRadius z hz)
      simpa only [localNormalizerCorrection, ite_eq_left hs, Function.comp_def] using hh
    · intro _
      change TendstoUniformlyOn (fun n z ↦ localCenteredNormalizerLog l u n z)
        (fun z ↦ localNormalizerCorrection l u z) atTop _
      have hh := (hc.comp (fun z : ℂ ↦ Complex.exp z - 1)).mono
        (show {z : ℂ | z.re < 2 * profileRoot l} ⊆
          (fun z : ℂ ↦ Complex.exp z - 1) ⁻¹' Metric.closedBall 0 (localNormalizerRadius l) from
          fun z hz ↦ by
            simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using
              (norm_exp_sub_one_lt_localNormalizerRadius z hz).le)
      simpa only [localCenteredNormalizerLog, localNormalizerCorrection, ite_eq_left hs,
        Function.comp_def] using hh
  · constructor
    · change AnalyticOnNhd ℂ (fun z ↦ localNormalizerCorrection l u z) _
      simpa only [localNormalizerCorrection, ite_eq_right hs] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ (0 : ℂ)) _)
    · exact fun h ↦ False.elim (hs h)


/-- Agreement with the event-word coefficient used by the tree normalizer. -/
theorem localBirthCoefficient_eq_model (l : ℝ) (u : ℕ → ℝ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ)) (k : ℕ) :
    localBirthCoefficient l u k = Model.birthReciprocal (localBirth l u) 1 k := by
  symm
  apply birthReciprocal_local_eq (H := k + 1) _ (by omega)
  intro i _
  exact_mod_cast hs i

private theorem complexProductRemainder_cut (a : ℕ → ℝ) (j n : ℕ) (w : ℂ) :
    complexProductRemainder (Finset.range n) (fun k ↦ if j ≤ k then a k else 0) w =
      complexProductRemainder (Finset.Ico j n) a w := by
  unfold complexProductRemainder
  calc
    _ = ∑ k ∈ Finset.range n, if j ≤ k then complexLogRemainder (w * (a k : ℂ)) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : j ≤ k <;> simp [hk, complexLogRemainder]
    _ = _ := sum_range_cut_eq_Ico _ _ _

/-- The analytic series is the centered logarithm of the actual prescribed
normalizer, with the source's physical index and exact cutoff. -/
theorem localCenteredNormalizerLog_eq_model (l : ℝ) (u : ℕ → ℝ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ)) (n : ℕ) (z : ℂ) :
    localCenteredNormalizerLog l u n z =
      Model.normalizerCenteredLogFrom (localBirth l u) 1 (localSafeCutoff l u) n
        (l / (l - 1)) (Complex.exp z) := by
  have heq : Model.birthReciprocal (localBirth l u) 1 = localBirthCoefficient l u :=
    funext (fun k ↦ (localBirthCoefficient_eq_model l u hs k).symm)
  unfold localCenteredNormalizerLog Model.normalizerCenteredLogFrom Model.normalizerRemainderFrom
  rw [heq]
  have hsum : (∑ k ∈ Finset.range n, localSafeBirthCoefficient l u k) =
      ∑ k ∈ Finset.Ico (localSafeCutoff l u) n, localBirthCoefficient l u k :=
    sum_range_cut_eq_Ico (localBirthCoefficient l u) (localSafeCutoff l u) n
  rw [hsum]
  congr 1
  exact complexProductRemainder_cut _ _ _ _

/-- Exact exponential representation of the actual tree normalizer. -/
theorem localNormalizer_eq_exp_centered (l : ℝ) (u : ℕ → ℝ)
    (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hb : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (n : ℕ) (z : ℂ) (hz : z.re < 2 * profileRoot l) :
    Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1 (localSafeCutoff l u) n =
      Complex.exp (((l / (l - 1) : ℝ) : ℂ) * (Complex.exp z - 1) * (Real.log n : ℂ) +
        localCenteredNormalizerLog l u n z) := by
  rw [localCenteredNormalizerLog_eq_model l u hs]
  apply Model.prescribedNormalizerFrom_eq_exp_centered
  intro i hi
  rw [← localBirthCoefficient_eq_model l u hs]
  have hsmall := localBirthCoefficient_safe_after l u hs hb (Finset.mem_Ico.mp hi).1
  rw [abs_of_nonneg (localBirthCoefficient_nonneg l u hs i)] at hsmall
  exact ((mul_le_mul_of_nonneg_right (norm_exp_sub_one_lt_localNormalizerRadius z hz).le
    (localBirthCoefficient_nonneg l u hs i)).trans hsmall).trans_lt (by norm_num)


/-- A common deterministic majorant for every logarithmic remainder, uniformly
on the whole source domain. The inverse-count envelope is squared. -/
theorem norm_localNormalizerRemainderTerm_le {l M : ℝ} (hl : 1 < l) (hM : 0 ≤ M)
    (u : ℕ → ℝ) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hb : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (z : ℂ) (hz : z.re < 2 * profileRoot l) (k : ℕ) :
    ‖complexLogRemainder ((Complex.exp z - 1) * (localSafeBirthCoefficient l u k : ℂ))‖ ≤
      (Real.exp 2 + 1) ^ 2 * M ^ 2 * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
  have hc : |localSafeBirthCoefficient l u k| ≤ M / (k + 1 : ℕ) := by
    unfold localSafeBirthCoefficient
    split
    · simpa only [abs_of_nonneg (localBirthCoefficient_nonneg l u hs k)] using
        localBirthCoefficient_le_linear l u hM hs hr k
    · simp only [abs_zero]
      positivity
  have hzR := (norm_exp_sub_one_lt_localNormalizerRadius z hz).le
  have hzG := hzR.trans (localNormalizerRadius_le hl)
  have hsmall : ‖(Complex.exp z - 1) * (localSafeBirthCoefficient l u k : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hzR (abs_nonneg _)).trans
      (localSafeBirthCoefficient_safe l u hs hb k)
  calc
    _ ≤ ‖(Complex.exp z - 1) * (localSafeBirthCoefficient l u k : ℂ)‖ ^ 2 :=
      norm_complexLogRemainder_le hsmall
    _ = ‖Complex.exp z - 1‖ ^ 2 * |localSafeBirthCoefficient l u k| ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    _ ≤ (Real.exp 2 + 1) ^ 2 * (M / (k + 1 : ℕ)) ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzG 2)
        (pow_le_pow_left₀ (abs_nonneg _) hc 2) (sq_nonneg _) (sq_nonneg _)
    _ = _ := by rw [div_pow]; ring

theorem localNormalizerRemainder_summable {l M : ℝ} (hl : 1 < l) (hM : 0 ≤ M)
    (u : ℕ → ℝ) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hb : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (z : ℂ) (hz : z.re < 2 * profileRoot l) :
    Summable (fun k ↦ complexLogRemainder
      ((Complex.exp z - 1) * (localSafeBirthCoefficient l u k : ℂ))) :=
  Summable.of_norm_bounded (summable_reciprocal_square.mul_left ((Real.exp 2 + 1) ^ 2 * M ^ 2))
    (norm_localNormalizerRemainderTerm_le hl hM u hs hr hb z hz)

theorem norm_localNormalizerRemainder_tsum_le {l M : ℝ} (hl : 1 < l) (hM : 0 ≤ M)
    (u : ℕ → ℝ) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hb : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (z : ℂ) (hz : z.re < 2 * profileRoot l) :
    ‖∑' k, complexLogRemainder ((Complex.exp z - 1) * (localSafeBirthCoefficient l u k : ℂ))‖ ≤
      (Real.exp 2 + 1) ^ 2 * M ^ 2 * ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2 :=
  tsum_of_norm_bounded (summable_reciprocal_square.hasSum.mul_left ((Real.exp 2 + 1) ^ 2 * M ^ 2))
    (norm_localNormalizerRemainderTerm_le hl hM u hs hr hb z hz)

/-- The entire logarithmic remainder tail is controlled by a deterministic
square-series tail, with a parameter-uniform random envelope. -/
theorem norm_localNormalizerRemainder_tail_le {l M : ℝ} (hl : 1 < l) (hM : 0 ≤ M)
    (u : ℕ → ℝ) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hb : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (n : ℕ) (z : ℂ) (hz : z.re < 2 * profileRoot l) :
    ‖complexProductRemainder (Finset.range n) (localSafeBirthCoefficient l u) (Complex.exp z - 1) -
      ∑' k, complexLogRemainder ((Complex.exp z - 1) * (localSafeBirthCoefficient l u k : ℂ))‖ ≤
      (Real.exp 2 + 1) ^ 2 * M ^ 2 * ∑' k : ℕ, 1 / ((k + n + 1 : ℕ) : ℝ) ^ 2 := by
  have hsum := (localNormalizerRemainder_summable hl hM u hs hr hb z hz).sum_add_tsum_nat_add n
  have heq : (∑' k, complexLogRemainder
      ((Complex.exp z - 1) * (localSafeBirthCoefficient l u k : ℂ))) -
      complexProductRemainder (Finset.range n) (localSafeBirthCoefficient l u) (Complex.exp z - 1) =
      ∑' k, complexLogRemainder
        ((Complex.exp z - 1) * (localSafeBirthCoefficient l u (k + n) : ℂ)) := by
    unfold complexProductRemainder
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hsum.symm)
  rw [norm_sub_rev, heq]
  have ht : Summable (fun k : ℕ ↦ 1 / ((k + n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff n).mpr summable_reciprocal_square
  exact tsum_of_norm_bounded (ht.hasSum.mul_left ((Real.exp 2 + 1) ^ 2 * M ^ 2))
    (fun k ↦ norm_localNormalizerRemainderTerm_le hl hM u hs hr hb z hz (k + n))


/-- The error separates into the actual centered reciprocal error and a
square-summable complex logarithmic tail. -/
theorem localNormalizer_error_bound {l M : ℝ} (hl : 1 < l) (hM : 0 ≤ M)
    (u : ℕ → ℝ) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hb : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    {n : ℕ} (hn : localSafeCutoff l u ≤ n) (z : ℂ) (hz : z.re < 2 * profileRoot l) :
    ‖localCenteredNormalizerLog l u n z - localNormalizerCorrection l u z‖ ≤
      (Real.exp 2 + 1) * |finiteLocalCenteredReciprocal l u n - localBirthReciprocalLimit l u| +
        (Real.exp 2 + 1) ^ 2 * M ^ 2 * ∑' k : ℕ, 1 / ((k + n + 1 : ℕ) : ℝ) ^ 2 := by
  have hc : finiteLocalCenteredReciprocal l u n =
      (∑ k ∈ Finset.range n, localBirthCoefficient l u k) - l / (l - 1) * Real.log n := by
    simp only [finiteLocalCenteredReciprocal, localBirthCoefficient,
      ite_eq_left (show ∀ i ≤ n, 0 < (localWalk l u i : ℝ) from fun i _ ↦ hs i), one_mul]
  have heq : localCenteredNormalizerLog l u n z - localNormalizerCorrection l u z =
      (Complex.exp z - 1) * ((finiteLocalCenteredReciprocal l u n - localBirthReciprocalLimit l u : ℝ) : ℂ) +
        (complexProductRemainder (Finset.range n) (localSafeBirthCoefficient l u) (Complex.exp z - 1) -
          ∑' k, complexLogRemainder ((Complex.exp z - 1) * (localSafeBirthCoefficient l u k : ℂ))) := by
    rw [hc]
    simp only [localCenteredNormalizerLog, localNormalizerCorrection, ite_eq_left hs]
    rw [sum_localSafeBirthCoefficient l u hn]
    push_cast
    ring
  rw [heq]
  apply (norm_add_le _ _).trans
  apply add_le_add _ (norm_localNormalizerRemainder_tail_le hl hM u hs hr hb n z hz)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    ((norm_exp_sub_one_lt_localNormalizerRadius z hz).le.trans (localNormalizerRadius_le hl))
    (abs_nonneg _)

/-- A common bound for the entire analytic correction. The finite prefix costs
at most the exact source cutoff, whose tightness is already proved. -/
theorem localNormalizerCorrection_bound {l M : ℝ} (hl : 1 < l) (hM : 0 ≤ M)
    (u : ℕ → ℝ) (hs : ∀ i, 0 < (localWalk l u i : ℝ))
    (hr : ∀ k, positiveReciprocal l u k ≤ M)
    (hb : BddAbove {k : ℕ | (1 / 2 : ℝ) ≤
      1 / (localWalk l u k : ℝ) * (Real.exp (2 * profileRoot l) + 1)})
    (z : ℂ) (hz : z.re < 2 * profileRoot l) :
    ‖localNormalizerCorrection l u z‖ ≤
      (Real.exp 2 + 1) * (|localBirthReciprocalLimit l u| + localSafeCutoff l u) +
        (Real.exp 2 + 1) ^ 2 * M ^ 2 * ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
  have hp0 : 0 ≤ localBirthPrefixAtCutoff l u :=
    Finset.sum_nonneg (fun k _ ↦ localBirthCoefficient_nonneg l u hs k)
  have hp : localBirthPrefixAtCutoff l u ≤ localSafeCutoff l u := by
    calc
      _ ≤ ∑ _k ∈ Finset.range (localSafeCutoff l u), (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ ↦ localBirthCoefficient_le_one l u hs k)
      _ = _ := by simp
  have hlin : |localBirthReciprocalLimit l u - localBirthPrefixAtCutoff l u| ≤
      |localBirthReciprocalLimit l u| + localSafeCutoff l u := by
    exact (abs_sub _ _).trans (add_le_add le_rfl (by simpa only [abs_of_nonneg hp0] using hp))
  rw [localNormalizerCorrection, ite_eq_left hs]
  apply (norm_add_le _ _).trans
  apply add_le_add _ (norm_localNormalizerRemainder_tsum_le hl hM u hs hr hb z hz)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul
    ((norm_exp_sub_one_lt_localNormalizerRadius z hz).le.trans (localNormalizerRadius_le hl))
    hlin (abs_nonneg _) (by positivity)

/-- Almost-sure convergence is weakly uniform in the epidemic parameter and
uniform in the complex tilt throughout the source domain. -/
theorem localNormalizer_uniform_convergence {l₀ : ℝ} (hl₀ : 1 < l₀)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ≥ l₀,
      uniformLaw.real {u | (∀ i, 0 < (localWalk l u i : ℝ)) ∧
        ∃ z : ℂ, z.re < 2 * profileRoot l ∧
          ε ≤ ‖localCenteredNormalizerLog l u n z - localNormalizerCorrection l u z‖} < η := by
  have hR : 0 < Real.exp 2 + 1 := by positivity
  have heta : 0 < η / 3 := by positivity
  have heps : 0 < (ε / 2) / (Real.exp 2 + 1) := by positivity
  obtain ⟨M, hM, hMtight⟩ := positiveReciprocal_uniform_tight hl₀ heta
  obtain ⟨J, hJtight⟩ := localSafeCutoff_uniform_tight hl₀ heta
  obtain ⟨NC, hNC⟩ := finiteLocalCenteredReciprocal_uniform_convergence hl₀ heps heta
  have htail : Tendsto (fun n : ℕ ↦ (Real.exp 2 + 1) ^ 2 * M ^ 2 *
      ∑' k : ℕ, 1 / ((k + n + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
    have ht0 : Tendsto (fun n : ℕ ↦ ∑' k : ℕ, 1 / ((k + n + 1 : ℕ) : ℝ) ^ 2)
        atTop (𝓝 (0 : ℝ)) :=
      tendsto_sum_nat_add (fun k : ℕ ↦ 1 / ((k + 1 : ℕ) : ℝ) ^ 2)
    simpa only [mul_zero] using ht0.const_mul ((Real.exp 2 + 1) ^ 2 * M ^ 2)
  obtain ⟨NT, hNT⟩ := eventually_atTop.mp (htail.eventually (Iio_mem_nhds (show 0 < ε / 2 by positivity)))
  refine ⟨max J (max NC NT), ?_⟩
  intro n hn l hl
  have hnJ : J ≤ n := by omega
  have hnC : NC ≤ n := by omega
  have hnT : NT ≤ n := by omega
  have hl1 := hl₀.trans_le hl
  let F₁ : Set (ℕ → ℝ) := {u | ∃ k, M < positiveReciprocal l u k}
  let F₂ : Set (ℕ → ℝ) := {u | J < localSafeCutoff l u}
  let F₃ : Set (ℕ → ℝ) := {u | (ε / 2) / (Real.exp 2 + 1) ≤
    |finiteLocalCenteredReciprocal l u n - localBirthReciprocalLimit l u|}
  have hsub : ∀ᵐ u ∂uniformLaw,
      ((∀ i, 0 < (localWalk l u i : ℝ)) ∧ ∃ z : ℂ, z.re < 2 * profileRoot l ∧
        ε ≤ ‖localCenteredNormalizerLog l u n z - localNormalizerCorrection l u z‖) →
      u ∈ F₁ ∪ F₂ ∪ F₃ := by
    filter_upwards [localSafeCutoff_ae_bddAbove hl1] with u hu
    rintro ⟨hs, z, hz, hbad⟩
    by_cases h₁ : u ∈ F₁
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : u ∈ F₂
    · exact Or.inl (Or.inr h₂)
    by_cases h₃ : u ∈ F₃
    · exact Or.inr h₃
    have hr : ∀ k, positiveReciprocal l u k ≤ M :=
      fun k ↦ le_of_not_gt (fun hh ↦ h₁ ⟨k, hh⟩)
    have hj : localSafeCutoff l u ≤ n := (le_of_not_gt h₂).trans hnJ
    have hc : |finiteLocalCenteredReciprocal l u n - localBirthReciprocalLimit l u| <
        (ε / 2) / (Real.exp 2 + 1) := lt_of_not_ge h₃
    have hlin := mul_lt_mul_of_pos_left hc hR
    rw [mul_div_cancel₀ _ hR.ne'] at hlin
    have hbound := localNormalizer_error_bound hl1 hM u hs hr hu hj z hz
    have ht := hNT n hnT
    exact False.elim (by linarith)
  have hmeasure := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hbound : uniformLaw.real (F₁ ∪ F₂ ∪ F₃) ≤
      uniformLaw.real F₁ + uniformLaw.real F₂ + uniformLaw.real F₃ :=
    (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
  apply hmeasure.trans_lt (hbound.trans_lt _)
  have h₁ := hMtight l hl
  have h₂ := hJtight l hl
  have h₃ := hNC n hnC l hl
  linarith

/-- The analytic correction has a tight common bound over the whole complex
source domain, uniformly over parameters bounded away from criticality. -/
theorem localNormalizerCorrection_uniform_tight {l₀ : ℝ} (hl₀ : 1 < l₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ l ≥ l₀,
      uniformLaw.real {u | ∃ z : ℂ, z.re < 2 * profileRoot l ∧
        A < ‖localNormalizerCorrection l u z‖} ≤ ε := by
  have heta : 0 < ε / 3 := by positivity
  obtain ⟨M, hM, hMtight⟩ := positiveReciprocal_uniform_tight hl₀ heta
  obtain ⟨J, hJtight⟩ := localSafeCutoff_uniform_tight hl₀ heta
  obtain ⟨B, hB, hBtight⟩ := localBirthReciprocalLimit_uniform_tight hl₀ heta
  let A : ℝ := (Real.exp 2 + 1) * (B + J) +
    (Real.exp 2 + 1) ^ 2 * M ^ 2 * ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro l hl
  have hl1 := hl₀.trans_le hl
  let F₁ : Set (ℕ → ℝ) := {u | ∃ k, M < positiveReciprocal l u k}
  let F₂ : Set (ℕ → ℝ) := {u | J < localSafeCutoff l u}
  let F₃ : Set (ℕ → ℝ) := {u | B < |localBirthReciprocalLimit l u|}
  have hsub : ∀ᵐ u ∂uniformLaw,
      (∃ z : ℂ, z.re < 2 * profileRoot l ∧ A < ‖localNormalizerCorrection l u z‖) →
        u ∈ F₁ ∪ F₂ ∪ F₃ := by
    filter_upwards [localSafeCutoff_ae_bddAbove hl1] with u hu
    rintro ⟨z, hz, hbad⟩
    by_cases h₁ : u ∈ F₁
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : u ∈ F₂
    · exact Or.inl (Or.inr h₂)
    by_cases h₃ : u ∈ F₃
    · exact Or.inr h₃
    by_cases hs : ∀ i, 0 < (localWalk l u i : ℝ)
    · have hr : ∀ k, positiveReciprocal l u k ≤ M :=
        fun k ↦ le_of_not_gt (fun hh ↦ h₁ ⟨k, hh⟩)
      have hj : (localSafeCutoff l u : ℝ) ≤ J := by exact_mod_cast le_of_not_gt h₂
      have hzB : |localBirthReciprocalLimit l u| ≤ B := le_of_not_gt h₃
      have hh := localNormalizerCorrection_bound hl1 hM u hs hr hu z hz
      have hfinal : ‖localNormalizerCorrection l u z‖ ≤ A := hh.trans (by
        dsimp only [A]
        gcongr)
      exact False.elim (not_lt_of_ge hfinal hbad)
    · have hz0 : localNormalizerCorrection l u z = 0 := by
        simp only [localNormalizerCorrection, ite_eq_right hs]
      rw [hz0, norm_zero] at hbad
      exact False.elim (not_lt_of_ge hA hbad)
  have hmeasure := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hbound : uniformLaw.real (F₁ ∪ F₂ ∪ F₃) ≤
      uniformLaw.real F₁ + uniformLaw.real F₂ + uniformLaw.real F₃ :=
    (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
  apply hmeasure.trans (hbound.trans _)
  have h₁ := hMtight l hl
  have h₂ := hJtight l hl
  have h₃ := hBtight l hl
  linarith


/-- The actual local version of the paper's complex-normalizer asymptotic:
one measurable analytic correction, almost-sure uniform convergence, and the
exact exponential identity for the prescribed tree product. -/
theorem localNormalizer_ae_source_asymptotic {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw,
      AnalyticOnNhd ℂ (localNormalizerCorrection l u) {z : ℂ | z.re < 2 * profileRoot l} ∧
      ((∀ i, 0 < (localWalk l u i : ℝ)) →
        TendstoUniformlyOn (localCenteredNormalizerLog l u) (localNormalizerCorrection l u)
          atTop {z : ℂ | z.re < 2 * profileRoot l} ∧
        ∀ (n : ℕ) (z : ℂ), z.re < 2 * profileRoot l →
          Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1 (localSafeCutoff l u) n =
            Complex.exp (((l / (l - 1) : ℝ) : ℂ) * (Complex.exp z - 1) * (Real.log n : ℂ) +
              localCenteredNormalizerLog l u n z)) := by
  filter_upwards [localNormalizer_ae_analytic_limit hl, localSafeCutoff_ae_bddAbove hl]
    with u hu hcut
  refine ⟨hu.1, ?_⟩
  intro hs
  exact ⟨hu.2 hs, fun n z hz ↦ localNormalizer_eq_exp_centered l u hs hcut n z hz⟩

/-- The paper's compact-parameter form. The complex domain may be any set
contained in every source half-plane, so compact domains are included. -/
theorem localNormalizer_compact_uniform_convergence {I : Set ℝ} (hI : IsCompact I)
    (hIsub : I ⊆ Set.Ioi 1) {K : Set ℂ}
    (hK : ∀ l ∈ I, ∀ z ∈ K, z.re < profileRoot l)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real {u | (∀ i, 0 < (localWalk l u i : ℝ)) ∧
        ∃ z ∈ K, ε ≤ ‖localCenteredNormalizerLog l u n z - localNormalizerCorrection l u z‖} < η := by
  by_cases hne : I.Nonempty
  · obtain ⟨l₀, hl₀⟩ := hI.exists_isLeast hne
    obtain ⟨N, hN⟩ := localNormalizer_uniform_convergence (hIsub hl₀.1) hε hη
    refine ⟨N, fun n hn l hl ↦ ?_⟩
    apply (measureReal_mono (h₂ := measure_ne_top _ _) ?_).trans_lt (hN n hn l (hl₀.2 hl))
    rintro u ⟨hs, z, hz, hbad⟩
    exact ⟨hs, z, by linarith [hK l hl z hz, profileRoot_pos (hIsub hl)], hbad⟩
  · exact ⟨0, fun _ _ l hl ↦ False.elim (hne ⟨l, hl⟩)⟩

/-- Tightness of the correction in the exact compact-parameter source form. -/
theorem localNormalizerCorrection_compact_uniform_tight {I : Set ℝ} (hI : IsCompact I)
    (hIsub : I ⊆ Set.Ioi 1) {K : Set ℂ}
    (hK : ∀ l ∈ I, ∀ z ∈ K, z.re < profileRoot l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ l ∈ I,
      uniformLaw.real {u | ∃ z ∈ K, A < ‖localNormalizerCorrection l u z‖} ≤ ε := by
  by_cases hne : I.Nonempty
  · obtain ⟨l₀, hl₀⟩ := hI.exists_isLeast hne
    obtain ⟨A, hA, hbound⟩ := localNormalizerCorrection_uniform_tight (hIsub hl₀.1) hε
    refine ⟨A, hA, fun l hl ↦ ?_⟩
    apply (measureReal_mono (h₂ := measure_ne_top _ _) ?_).trans (hbound l (hl₀.2 hl))
    rintro u ⟨z, hz, hbad⟩
    exact ⟨z, by linarith [hK l hl z hz, profileRoot_pos (hIsub hl)], hbad⟩
  · exact ⟨0, le_rfl, fun l hl ↦ False.elim (hne ⟨l, hl⟩)⟩


/-- Joint measurability makes the correction an actual random analytic family,
with its complex argument retained as part of the measurable map. -/
theorem measurable_localNormalizerCorrection_joint (l : ℝ) :
    Measurable (fun p : (ℕ → ℝ) × ℂ ↦ localNormalizerCorrection l p.1 p.2) := by
  have hsurv : MeasurableSet {p : (ℕ → ℝ) × ℂ | ∀ i, 0 < (localWalk l p.1 i : ℝ)} := by
    have hh := MeasurableSet.iInter (fun i ↦
      measurableSet_lt (measurable_const : Measurable (fun _ : (ℕ → ℝ) × ℂ ↦ (0 : ℝ)))
        ((measurable_localWalk_real l i).comp measurable_fst))
    convert hh using 1
    ext p
    simp
  have hw : Measurable (fun p : (ℕ → ℝ) × ℂ ↦ Complex.exp p.2 - 1) :=
    (Complex.continuous_exp.measurable.comp measurable_snd).sub measurable_const
  apply Measurable.ite hsurv _ measurable_const
  apply Measurable.add
  · exact hw.mul (Complex.measurable_ofReal.comp
      (((measurable_localBirthReciprocalLimit l).sub
        (measurable_localBirthPrefixAtCutoff l)).comp measurable_fst))
  · apply Measurable.tsum
    intro k
    have hm : Measurable (fun p : (ℕ → ℝ) × ℂ ↦
        (Complex.exp p.2 - 1) * (localSafeBirthCoefficient l p.1 k : ℂ)) :=
      hw.mul (Complex.measurable_ofReal.comp
        ((measurable_localSafeBirthCoefficient l k).comp measurable_fst))
    exact (measurable_const.add hm).clog.sub hm

end HeightPaper.CountCoupling
