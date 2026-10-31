module

public import HeightPaper.Probability.FiniteLocalProfileMovingTime
public import HeightPaper.Probability.FiniteNormalizerPrefixModulus
public import HeightPaper.Probability.FiniteProfileMomentStrictDecay
public import HeightPaper.Probability.UniformParentLaw
public import HeightPaper.Probability.ConditionalMomentTransfer

/-!
# Small-tilt continuity of the finite profile after the random cutoff

The unshifted analytic profile has a stochastic modulus at diverging times.
The finite prefix normalizer converts this into a modulus for the paper's
shifted profile on the event that the cutoff precedes observation.
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

open Model

noncomputable def finiteShiftedRankProfile (l : ℝ) (n H : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) (k : ℕ) (z : ℂ) : ℂ :=
  prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n q.1)
    (initial n) (finiteSafeCutoff l n H q.1) k
    (rankState (finiteBirth l n q.1) (initial n) q.2 k)

/-- The profile at a fixed complex tilt is measurable on the joint uniform
construction at every time inside the finite event horizon. -/
theorem measurable_finiteShiftedRankProfile (l : ℝ) (n H k : ℕ)
    (hk : k ≤ H) (z : ℂ) :
    Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      finiteShiftedRankProfile l n H q k z) := by
  intro E _
  apply measurableSet_of_finiteBirth_rankStates l n H k k
  intro q q' he hstate _
  change finiteShiftedRankProfile l n H q k z ∈ E ↔
    finiteShiftedRankProfile l n H q' k z ∈ E
  have hJ := finiteSafeCutoff_congr_birth_prefix he
  have hC := prescribedNormalizerFrom_congr_prefix (Complex.exp z) 1
    (finiteSafeCutoff l n H q'.1) he hk
  simp only [finiteShiftedRankProfile, prescribedNormalizedProfile,
    infectious_initial, hstate, hJ, hC]

/-- Simultaneous tilt tails are measurable because the finite word and one
finite tree state form a countable observation code. -/
theorem measurableSet_finiteShiftedRankProfile_tiltTail
    (l : ℝ) (n H k : ℕ) (hk : k ≤ H)
    (K : Set ℂ) (w : ℂ) (a : ℝ) :
    MeasurableSet {r : (ℕ → ℝ) × (ℕ → ℝ) | ∃ z ∈ K,
      a < ‖finiteShiftedRankProfile l n H r k z -
        finiteShiftedRankProfile l n H r k w‖} := by
  apply measurableSet_of_finiteBirth_rankStates l n H k k
  intro r s he hstate _
  have hJ := finiteSafeCutoff_congr_birth_prefix he
  have hprof (z : ℂ) : finiteShiftedRankProfile l n H r k z =
      finiteShiftedRankProfile l n H s k z := by
    have hC := prescribedNormalizerFrom_congr_prefix (Complex.exp z) 1
      (finiteSafeCutoff l n H s.1) he hk
    simp only [finiteShiftedRankProfile, prescribedNormalizedProfile,
      infectious_initial, hstate, hJ, hC]
  simp only [mem_ofPred_eq, hprof]

/-- The conditional moment of the shifted rank profile under the parent
uniforms is exactly the prescribed-word moment used in the source controls. -/
theorem finiteShiftedRankProfile_parent_moment_eq (l : ℝ) (n H k : ℕ)
    (u : ℕ → ℝ) (z : ℂ) (p : ℝ) :
    (∫ v, ‖finiteShiftedRankProfile l n H (u, v) k z‖ ^ p ∂uniformLaw) =
      finiteProfileMoment (Complex.exp z) p l n H u k := by
  unfold finiteShiftedRankProfile finiteProfileMoment
  rw [← rankHistory_law (finiteBirth l n u) (initial n) k]
  rw [integral_map (measurable_rankHistory (finiteBirth l n u) (initial n) k).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  rfl

/-- The same exact conditional-law identity for two different complex tilts
at the same observation time. -/
theorem finiteShiftedRankProfile_parent_difference_moment_eq
    (l : ℝ) (n H k : ℕ) (u : ℕ → ℝ) (z w : ℂ) (p : ℝ) :
    (∫ v, ‖finiteShiftedRankProfile l n H (u, v) k z -
      finiteShiftedRankProfile l n H (u, v) k w‖ ^ p ∂uniformLaw) =
      ∫ path, ‖normalizedActiveWeight (Complex.exp z) path.last /
          finiteComplexNormalizer l n H u k z -
        normalizedActiveWeight (Complex.exp w) path.last /
          finiteComplexNormalizer l n H u k w‖ ^ p
        ∂kernelPathMeasure
          (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k := by
  unfold finiteShiftedRankProfile finiteComplexNormalizer
  rw [← rankHistory_law (finiteBirth l n u) (initial n) k]
  rw [integral_map (measurable_rankHistory (finiteBirth l n u) (initial n) k).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  rfl

/-- Every fixed-word two-tilt difference has all finite real moments under
the parent-uniform law, since the finite tree history has finite support. -/
theorem finiteShiftedRankProfile_parent_difference_integrable
    (l : ℝ) (n H k : ℕ) (u : ℕ → ℝ) (z w : ℂ) (p : ℝ) :
    Integrable (fun v ↦ ‖finiteShiftedRankProfile l n H (u, v) k z -
      finiteShiftedRankProfile l n H (u, v) k w‖ ^ p) uniformLaw := by
  let g : FinitePath k → ℝ := fun path ↦
    ‖normalizedActiveWeight (Complex.exp z) path.last /
        finiteComplexNormalizer l n H u k z -
      normalizedActiveWeight (Complex.exp w) path.last /
        finiteComplexNormalizer l n H u k w‖ ^ p
  have hg : Integrable g (kernelPathMeasure
      (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k) :=
    integrable_kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i))
      (fun i s ↦ finite_support_prescribedStep _ s) (initial n) k g
  have hgmap : Integrable g
      (uniformLaw.map (rankHistory (finiteBirth l n u) (initial n) k)) := by
    rw [rankHistory_law]
    exact hg
  have hcomp := hgmap.comp_measurable
    (measurable_rankHistory (finiteBirth l n u) (initial n) k)
  convert hcomp using 1
  ext v
  rfl

/-- A higher conditional moment of the difference is bounded by the two
single-profile moments at the same event time. -/
theorem finiteShiftedRankProfile_parent_difference_moment_le
    (l : ℝ) (n H k : ℕ) (u : ℕ → ℝ) (z w : ℂ)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    (∫ v, ‖finiteShiftedRankProfile l n H (u, v) k z -
      finiteShiftedRankProfile l n H (u, v) k w‖ ^ p ∂uniformLaw) ≤
      2 * (finiteProfileMoment (Complex.exp z) p l n H u k +
        finiteProfileMoment (Complex.exp w) p l n H u k) := by
  rw [finiteShiftedRankProfile_parent_difference_moment_eq]
  let μ := kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k
  let F (path : FinitePath k) : ℂ :=
    normalizedActiveWeight (Complex.exp z) path.last /
      finiteComplexNormalizer l n H u k z
  let G (path : FinitePath k) : ℂ :=
    normalizedActiveWeight (Complex.exp w) path.last /
      finiteComplexNormalizer l n H u k w
  have hpoint (path : FinitePath k) :
      ‖F path - G path‖ ^ p ≤ 2 * (‖F path‖ ^ p + ‖G path‖ ^ p) := by
    have ht : ‖F path - G path‖ ≤ ‖F path‖ + ‖G path‖ := norm_sub_le _ _
    have hc : (‖F path‖ + ‖G path‖) ^ p ≤
        (2 : ℝ) ^ (p - 1) * (‖F path‖ ^ p + ‖G path‖ ^ p) := by
      simpa [Fin.sum_univ_succ] using
        Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ)
          (f := ![‖F path‖, ‖G path‖]) hp
          (fun i _ ↦ by fin_cases i <;> simp)
    have htwo : (2 : ℝ) ^ (p - 1) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ 2 by norm_num) (show p - 1 ≤ 1 by linarith)
    exact ((Real.rpow_le_rpow (norm_nonneg _) ht (by linarith)).trans hc).trans
      (mul_le_mul_of_nonneg_right htwo (by positivity))
  have hInt (f : FinitePath k → ℝ) : Integrable f μ :=
    integrable_kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i))
      (fun i s ↦ finite_support_prescribedStep _ s) (initial n) k f
  change (∫ path, ‖F path - G path‖ ^ p ∂μ) ≤ _
  calc
    _ ≤ ∫ path, 2 * (‖F path‖ ^ p + ‖G path‖ ^ p) ∂μ :=
      integral_mono (hInt _) (hInt _) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_add (hInt _) (hInt _)]
      rfl

def finiteShiftedTiltMomentBad (C η l : ℝ) (n H : ℕ) : Set (ℕ → ℝ) :=
  {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
    ∃ k, 1 ≤ k ∧ k ≤ H ∧ finiteSafeCutoff l n H u ≤ k ∧
      ∃ z w : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
        0 ≤ w.re ∧ w.re ≤ 2 * profileRoot l ∧
        ∃ p ∈ Ioc (1 : ℝ) 2,
          complexProfileMomentExponent l z p ≤ -1 - η ∧
          complexProfileMomentExponent l w p ≤ -1 - η ∧
          C < ∫ v, ‖finiteShiftedRankProfile l n H (u, v) k z -
            finiteShiftedRankProfile l n H (u, v) k w‖ ^ p ∂uniformLaw}

/-- A tight random bound controls the higher conditional moment of every
two-tilt difference in a strictly summable complex window. -/
theorem finiteShiftedTiltMoment_strictDecay_uniform
    {I : Set ℝ≥0} (hI : IsCompact I)
    {T η : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hη : 0 < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real (finiteShiftedTiltMomentBad C η l n ⌊T * n⌋₊) < ε := by
  obtain ⟨C₀, hC₀, N, htail⟩ :=
    finiteProfileMoment_strictDecay_uniform hI hT hparams hη hε
  let C : ℝ := 4 * C₀ + 1
  refine ⟨C, by dsimp [C]; positivity, N, ?_⟩
  intro n hn l hl
  apply lt_of_le_of_lt (measureReal_mono ?_) (htail n hn l hl)
  rintro u ⟨hs, k, hk1, hk, hJk, z, w, hz0, hz, hw0, hw, p, hp,
    hdecayz, hdecayw, hbad⟩
  by_contra hnot
  have hzmoment : finiteProfileMoment (Complex.exp z) p l n ⌊T * n⌋₊ u k ≤ C₀ :=
    le_of_not_gt (fun hh ↦ hnot
      ⟨hs, k, hk1, hk, hJk, z, hz0, hz, p, hp, hdecayz, hh⟩)
  have hwmoment : finiteProfileMoment (Complex.exp w) p l n ⌊T * n⌋₊ u k ≤ C₀ :=
    le_of_not_gt (fun hh ↦ hnot
      ⟨hs, k, hk1, hk, hJk, w, hw0, hw, p, hp, hdecayw, hh⟩)
  have hdiff := finiteShiftedRankProfile_parent_difference_moment_le
    l n ⌊T * n⌋₊ k u z w hp.1.le hp.2
  have hle : (∫ v, ‖finiteShiftedRankProfile l n ⌊T * n⌋₊ (u, v) k z -
      finiteShiftedRankProfile l n ⌊T * n⌋₊ (u, v) k w‖ ^ p ∂uniformLaw) ≤ C := by
    dsimp [C]
    linarith
  exact (not_lt_of_ge hle) hbad

/-- For fixed tilts in a common strict-decay window, a conditional lower
moment failure is bounded by one count-word moment exception and one joint
tail probability.  The numerical truncation parameters are explicit. -/
theorem finiteShiftedProfile_conditional_difference_moment_le_joint_tail
    (l : ℝ) (n H k : ℕ) (hk1 : 1 ≤ k) (hkH : k ≤ H)
    (z w : ℂ) (η : ℝ) (C a R p q δ ε : ℝ)
    (hz0 : 0 ≤ z.re) (hz : z.re ≤ 2 * profileRoot l)
    (hw0 : 0 ≤ w.re) (hw : w.re ≤ 2 * profileRoot l)
    (hq : q ∈ Ioc (1 : ℝ) 2)
    (hdecayz : complexProfileMomentExponent l z q ≤ -1 - η)
    (hdecayw : complexProfileMomentExponent l w q ≤ -1 - η)
    (ha : 0 < a) (haR : a ≤ R) (hp : 0 ≤ p) (hpq : p < q)
    (hδ : 0 < δ)
    (hnum : a ^ p + R ^ p * δ + R ^ (p - q) * C ≤ ε) :
    uniformLaw.real {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
      finiteSafeCutoff l n H u ≤ k ∧
      ε < ∫ v, ‖finiteShiftedRankProfile l n H (u, v) k z -
        finiteShiftedRankProfile l n H (u, v) k w‖ ^ p ∂uniformLaw} ≤
      uniformLaw.real (finiteShiftedTiltMomentBad C η l n H) +
        birthParentLaw.real {r | a < ‖finiteShiftedRankProfile l n H r k z -
          finiteShiftedRankProfile l n H r k w‖} / δ := by
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun r ↦
    ‖finiteShiftedRankProfile l n H r k z -
      finiteShiftedRankProfile l n H r k w‖
  have hF : Measurable F :=
    ((measurable_finiteShiftedRankProfile l n H k hkH z).sub
      (measurable_finiteShiftedRankProfile l n H k hkH w)).norm
  have hhigh (u : ℕ → ℝ)
      (hu : (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
        finiteSafeCutoff l n H u ≤ k)
      (huB : u ∉ finiteShiftedTiltMomentBad C η l n H) :
      (∫ v, F (u, v) ^ q ∂uniformLaw) ≤ C := by
    apply le_of_not_gt
    intro hh
    exact huB ⟨hu.1, k, hk1, hkH, hu.2, z, w,
      hz0, hz, hw0, hw, q, hq, hdecayz, hdecayw, hh⟩
  have ht := conditional_lower_moment_bad_le_joint_tail
    uniformLaw uniformLaw F hF (fun _ ↦ norm_nonneg _)
    {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
      finiteSafeCutoff l n H u ≤ k}
    (finiteShiftedTiltMomentBad C η l n H)
    a R p q C δ ε ha haR hp hpq hδ hnum
    (fun u ↦ finiteShiftedRankProfile_parent_difference_integrable
      l n H k u z w p)
    (fun u ↦ finiteShiftedRankProfile_parent_difference_integrable
      l n H k u z w q)
    hhigh
  simpa only [F, birthParentLaw, mem_ofPred_eq, and_assoc] using ht

/-- The same conditional-moment transfer holds simultaneously over a
possibly uncountable compact tilt set. -/
theorem finiteShiftedProfile_conditional_tilt_moment_le_joint_tail
    (l : ℝ) (n H k : ℕ) (hk1 : 1 ≤ k) (hkH : k ≤ H)
    (K : Set ℂ) (w : ℂ) (η : ℝ) (C a R p q δ ε : ℝ)
    (hw0 : 0 ≤ w.re) (hw : w.re ≤ 2 * profileRoot l)
    (hq : q ∈ Ioc (1 : ℝ) 2)
    (hdecayw : complexProfileMomentExponent l w q ≤ -1 - η)
    (hK : ∀ z ∈ K, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
      complexProfileMomentExponent l z q ≤ -1 - η)
    (ha : 0 < a) (haR : a ≤ R) (hp : 0 ≤ p) (hpq : p < q)
    (hδ : 0 < δ)
    (hnum : a ^ p + R ^ p * δ + R ^ (p - q) * C ≤ ε) :
    uniformLaw.real {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
      finiteSafeCutoff l n H u ≤ k ∧
      ∃ z ∈ K, ε < ∫ v, ‖finiteShiftedRankProfile l n H (u, v) k z -
        finiteShiftedRankProfile l n H (u, v) k w‖ ^ p ∂uniformLaw} ≤
      uniformLaw.real (finiteShiftedTiltMomentBad C η l n H) +
        birthParentLaw.real {r | ((∀ i ≤ H, 0 < finiteWalk l n r.1 i) ∧
          finiteSafeCutoff l n H r.1 ≤ k) ∧ ∃ z ∈ K,
          a < ‖finiteShiftedRankProfile l n H r k z -
            finiteShiftedRankProfile l n H r k w‖} / δ := by
  let F : ℂ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun z r ↦
    ‖finiteShiftedRankProfile l n H r k z -
      finiteShiftedRankProfile l n H r k w‖
  have hhigh (z : ℂ) (hz : z ∈ K) (u : ℕ → ℝ)
      (hu : (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
        finiteSafeCutoff l n H u ≤ k)
      (huB : u ∉ finiteShiftedTiltMomentBad C η l n H) :
      (∫ v, F z (u, v) ^ q ∂uniformLaw) ≤ C := by
    apply le_of_not_gt
    intro hh
    obtain ⟨hz0, hzbound, hdecayz⟩ := hK z hz
    exact huB ⟨hu.1, k, hk1, hkH, hu.2, z, w,
      hz0, hzbound, hw0, hw, q, hq, hdecayz, hdecayw, hh⟩
  have hS : MeasurableSet {u : ℕ → ℝ | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
      finiteSafeCutoff l n H u ≤ k} := by
    apply measurableSet_of_finiteBirth_prefix l n H
    intro u v he
    have hsurv := forall₂_congr (fun i (hi : i ≤ H) =>
      show (0 < finiteWalk l n u i) ↔ (0 < finiteWalk l n v i) by
        rw [finiteWalk_congr_birth_prefix he hi])
    simp only [mem_ofPred_eq, hsurv, finiteSafeCutoff_congr_birth_prefix he]
  have hE : MeasurableSet {r : (ℕ → ℝ) × (ℕ → ℝ) |
      r.1 ∈ {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
        finiteSafeCutoff l n H u ≤ k} ∧
      ∃ z ∈ K, a < F z r} := by
    exact (hS.preimage measurable_fst).inter
      (measurableSet_finiteShiftedRankProfile_tiltTail l n H k hkH K w a)
  have ht := conditional_lower_moment_exists_bad_le_joint_tail
    uniformLaw uniformLaw F K
    (fun z _ _ ↦ norm_nonneg _)
    {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
      finiteSafeCutoff l n H u ≤ k}
    (finiteShiftedTiltMomentBad C η l n H)
    a R p q C δ ε ha haR hp hpq hδ hnum
    hE
    (fun z _ u ↦
      (((measurable_finiteShiftedRankProfile l n H k hkH z).sub
        (measurable_finiteShiftedRankProfile l n H k hkH w)).norm).comp
        (measurable_const.prodMk measurable_id))
    (fun z _ u ↦ finiteShiftedRankProfile_parent_difference_integrable
      l n H k u z w p)
    (fun z _ u ↦ finiteShiftedRankProfile_parent_difference_integrable
      l n H k u z w q)
    hhigh
  simpa only [F, birthParentLaw, mem_ofPred_eq, and_assoc] using ht

def finiteShiftedProfileMovingTiltBad (l : ℝ) (n H j : ℕ)
    (x t ε : ℝ) : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
    finiteSafeCutoff l n H q.1 ≤ j ∧
    ∃ z ∈ closedBall (x : ℂ) t,
      ε < ‖finiteShiftedRankProfile l n H q j z -
        finiteShiftedRankProfile l n H q j (x : ℂ)‖}

/-- On the actual coupled finite tree, the paper's shifted profile at any
diverging preterminal observation time has a uniform stochastic tilt modulus.
The random cutoff is required to occur before that observation time. -/
theorem uniform_finiteShiftedProfile_moving_time_tilt_modulus
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (hp : p ∈ Ioc (1 : ℝ) 2) (hη : 0 < η)
    (hr : 0 < r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ t > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real (finiteShiftedProfileMovingTiltBad l n
        ⌊T * n⌋₊ (A n) x t ε) < δ := by
  have hquarter : 0 < δ / 4 := by positivity
  have hR : 0 < R := hr.trans hrR
  obtain ⟨K, Ncut, hcut⟩ :=
    finiteSafeCutoff_survival_uniform_tight hI hT hparams hquarter
  let M : ℝ := (2 + Real.exp (x + R)) ^ K
  have hM : 0 < M := by dsimp [M]; positivity
  have hεM : 0 < ε / (4 * M) := by positivity
  obtain ⟨tvar, htvar, Nvar, hvar⟩ :=
    uniform_finiteProfile_moving_time_tilt_modulus hI hl₀ hT
      hparams hIlower hx hp hη hr hrR hRρ hright hwindow
      A hA hAH hεM hquarter
  obtain ⟨Ncmp, hcmp⟩ :=
    uniform_finiteLocalProfile_moving_time_comparison hI hl₀ hT
      hparams hIlower hp hη hr.le hrR hRρ hright hwindow
      A hA hAH (by norm_num : 0 < (1 : ℝ)) hquarter
  obtain ⟨r₀, hr₀, _hana, hupper⟩ :=
    exists_localProfile_analytic_upper_disk hl₀ hx
  obtain ⟨B₀, hB₀, hBtail⟩ := hupper (δ / 4) hquarter
  let B : ℝ := B₀ + 1
  have hB : 0 < B := by dsimp [B]; linarith
  let t : ℝ := min (R / 2) (min tvar (ε * R / (8 * B * M)))
  have ht : 0 < t := by dsimp [t]; positivity
  have htR : t < R := by
    have hh : t ≤ R / 2 := min_le_left _ _
    linarith
  have htvar' : t ≤ tvar := (min_le_right _ _).trans (min_le_left _ _)
  have htsmall : t ≤ ε * R / (8 * B * M) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨t, ht, max Ncut (max Nvar Ncmp), ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let Ecut : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | K < (if ∀ i ≤ H, 0 < finiteWalk l n q.1 i then
      finiteSafeCutoff l n H q.1 else 0)}
  let Evar := finiteProfileMovingTimeTiltBad l n H (A n) x tvar (ε / (4 * M))
  let Ecmp := finiteLocalProfileMovingTimeBad l n H (A n)
    (closedBall (x : ℂ) r) 1
  let Elocal : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ z ∈ closedBall (x : ℂ) r₀,
        B₀ < ‖localUnshiftedRankProfileLimit l 0 q z‖}
  have hncut : Ncut ≤ n := (le_max_left _ _).trans hn
  have hnvar : Nvar ≤ n := (le_max_left _ _).trans
    ((le_max_right _ _).trans hn)
  have hncmp : Ncmp ≤ n := (le_max_right _ _).trans
    ((le_max_right _ _).trans hn)
  have hEcut : birthParentLaw.real Ecut < δ / 4 :=
    (birthParentLaw_real_fst_le _).trans_lt (hcut n hncut l hl)
  have hEvar : birthParentLaw.real Evar < δ / 4 := hvar n hnvar l hl
  have hEcmp : birthParentLaw.real Ecmp < δ / 4 := hcmp n hncmp l hl
  have hElocal : birthParentLaw.real Elocal < δ / 4 :=
    hBtail l (hIlower l hl) 0
  have hsub : finiteShiftedProfileMovingTiltBad l n H (A n) x t ε ⊆
      Ecut ∪ (Evar ∪ (Ecmp ∪ Elocal)) := by
    rintro q ⟨hs, hJA, z, hz, hbad⟩
    by_contra hnot
    have hnotC : q ∉ Ecut := fun hq ↦ hnot (Or.inl hq)
    have hnotV : q ∉ Evar := fun hq ↦ hnot (Or.inr (Or.inl hq))
    have hnotP : q ∉ Ecmp := fun hq ↦ hnot (Or.inr (Or.inr (Or.inl hq)))
    have hnotL : q ∉ Elocal := fun hq ↦ hnot (Or.inr (Or.inr (Or.inr hq)))
    have hJK : finiteSafeCutoff l n H q.1 ≤ K := by
      apply le_of_not_gt
      intro hh
      exact hnotC (by simpa only [Ecut, mem_ofPred_eq, ite_eq_left hs] using hh)
    have hsurv : ∀ i, 0 < localWalk l q.1 i := by
      by_contra hh
      exact hnotP ⟨hs, Or.inl hh⟩
    have hval : ‖finiteUnshiftedRankProfile l n q (A n) (x : ℂ) -
        localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ ≤ 1 :=
      le_of_not_gt (fun hh ↦ hnotP ⟨hs, Or.inr
        ⟨x, mem_closedBall_self hr.le, hh⟩⟩)
    have hlocal : ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ ≤ B₀ := by
      apply le_of_not_gt
      intro hh
      exact hnotL ⟨by exact_mod_cast hsurv,
        x, mem_closedBall_self hr₀.le, hh⟩
    have hcenter : ‖finiteUnshiftedRankProfile l n q (A n) (x : ℂ)‖ ≤ B := by
      have hh := norm_add_le
        (finiteUnshiftedRankProfile l n q (A n) (x : ℂ) -
          localUnshiftedRankProfileLimit l 0 q (x : ℂ))
        (localUnshiftedRankProfileLimit l 0 q (x : ℂ))
      calc
        _ ≤ 1 + B₀ := by
          simpa only [sub_add_cancel] using (hh.trans (add_le_add hval hlocal))
        _ = B := by dsimp [B]; ring
    have hzvar : z ∈ closedBall (x : ℂ) tvar :=
      closedBall_subset_closedBall htvar' hz
    have hvariation : ‖finiteUnshiftedRankProfile l n q (A n) z -
        finiteUnshiftedRankProfile l n q (A n) (x : ℂ)‖ ≤ ε / (4 * M) :=
      le_of_not_gt (fun hh ↦ hnotV ⟨hs, z, hzvar, hh⟩)
    have hzball : z ∈ ball (x : ℂ) R :=
      mem_ball.mpr ((mem_closedBall.mp hz).trans_lt htR)
    have hzw : 1 ≤ (Complex.exp z).re :=
      hright z (ball_subset_closedBall hzball)
    have hxw : 1 ≤ (Complex.exp (x : ℂ)).re :=
      hright x (mem_closedBall_self (by linarith : 0 ≤ R))
    have hbound := prescribedNormalizedProfile_shifted_tilt_bound x hR K
      (finiteBirth l n q.1) (initial n)
      (rankState (finiteBirth l n q.1) (initial n) q.2 (A n))
      hJK hJA hzball hzw hxw
    change ‖finiteShiftedRankProfile l n H q (A n) z -
      finiteShiftedRankProfile l n H q (A n) (x : ℂ)‖ ≤
      M * ‖finiteUnshiftedRankProfile l n q (A n) z -
        finiteUnshiftedRankProfile l n q (A n) (x : ℂ)‖ +
      ‖finiteUnshiftedRankProfile l n q (A n) (x : ℂ)‖ *
        (2 * M / R) * ‖z - (x : ℂ)‖ at hbound
    have hdist : ‖z - (x : ℂ)‖ ≤ t := by
      simpa only [mem_closedBall, dist_eq_norm] using hz
    have hfirst : M * ‖finiteUnshiftedRankProfile l n q (A n) z -
        finiteUnshiftedRankProfile l n q (A n) (x : ℂ)‖ ≤ ε / 4 := by
      calc
        _ ≤ M * (ε / (4 * M)) := mul_le_mul_of_nonneg_left hvariation hM.le
        _ = _ := by field_simp [hM.ne']
    have hsecond : ‖finiteUnshiftedRankProfile l n q (A n) (x : ℂ)‖ *
        (2 * M / R) * ‖z - (x : ℂ)‖ ≤ ε / 4 := by
      calc
        _ ≤ B * (2 * M / R) * t := by
          gcongr
        _ ≤ B * (2 * M / R) * (ε * R / (8 * B * M)) := by
          gcongr
        _ = ε / 4 := by field_simp [hR.ne', hB.ne', hM.ne']; ring
    exact (not_lt_of_ge (hbound.trans (by linarith))) hbad
  have hb := (measureReal_mono (μ := birthParentLaw) hsub).trans
    (measureReal_union_le _ _)
  have hu₁ := measureReal_union_le (μ := birthParentLaw) Evar (Ecmp ∪ Elocal)
  have hu₂ := measureReal_union_le (μ := birthParentLaw) Ecmp Elocal
  change birthParentLaw.real (finiteShiftedProfileMovingTiltBad l n H (A n) x t ε) < δ
  linarith

/-- The source's moving shifted profile is continuous in probability along
every shrinking compact complex-tilt family containing the real center.
The count-word conditional moment remains a separate assertion. -/
theorem uniform_finiteShiftedProfile_shrinking_tilts_probability
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (hp : p ∈ Ioc (1 : ℝ) 2) (hη : 0 < η)
    (hr : 0 < r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    (Kset : ℕ → Set ℂ) (hK : ∀ n, IsCompact (Kset n))
    (hxK : ∀ n, (x : ℂ) ∈ Kset n)
    (hdiam : Tendsto (fun n ↦ Metric.diam (Kset n)) atTop (𝓝 0))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real {q | (∀ i ≤ ⌊T * n⌋₊,
        0 < finiteWalk l n q.1 i) ∧
        finiteSafeCutoff l n ⌊T * n⌋₊ q.1 ≤ A n ∧
        ∃ z ∈ Kset n,
          ε < ‖finiteShiftedRankProfile l n ⌊T * n⌋₊ q (A n) z -
            finiteShiftedRankProfile l n ⌊T * n⌋₊ q (A n) (x : ℂ)‖} < δ := by
  obtain ⟨t, ht, N₁, hmod⟩ :=
    uniform_finiteShiftedProfile_moving_time_tilt_modulus hI hl₀ hT
      hparams hIlower hx hp hη hr hrR hRρ hright hwindow
      A hA hAH hε hδ
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (hdiam.eventually (Iio_mem_nhds ht))
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn l hl
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
  apply lt_of_le_of_lt (measureReal_mono ?_) (hmod n hn₁ l hl)
  rintro q ⟨hs, hJ, z, hz, hbad⟩
  refine ⟨hs, hJ, z, ?_, hbad⟩
  apply mem_closedBall.mpr
  exact (Metric.dist_le_diam_of_mem (hK n).isBounded hz (hxK n)).trans
    (hN₂ n hn₂).le

end HeightPaper.CountCoupling
