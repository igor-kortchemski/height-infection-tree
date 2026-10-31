module

public import HeightPaper.Probability.LocalProfileDiskTail
public import HeightPaper.Probability.LocalAnalyticBoundary
public import HeightPaper.Probability.CanonicalCircleLimit

/-!
# Uniform local profile tails on the joint probability space

A measurable boundary summability witness permits Fubini before the common
analytic limit is used. Conditional moment bounds also apply at a measurable
birth-word-dependent later time, including the canonical shifted dyadic times.
-/

@[expose] public section

open MeasureTheory Complex Metric Set Filter
open scoped Topology ENNReal BigOperators

namespace HeightPaper.CountCoupling

open Model

theorem localProfile_joint_ae_summable_boundary {l x p η ρ R : ℝ}
    (hl : 1 < l) (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hR : 0 < R) (hRρ : R < ρ)
    (hwindow : ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η) (n : ℕ) :
    ∀ᵐ q ∂birthParentLaw, (∀ i, 0 < (localWalk l q.1 i : ℝ)) →
      Summable (fun m ↦ localDyadicCircleIncrement l n (x : ℂ) R m q) := by
  have hmeas : MeasurableSet {q : (ℕ → ℝ) × (ℕ → ℝ) |
      (∀ i, 0 < (localWalk l q.1 i : ℝ)) →
        Summable (fun m ↦ localDyadicCircleIncrement l n (x : ℂ) R m q)} := by
    convert ((measurableSet_local_survival l).preimage measurable_fst).compl.union
        (measurableSet_localDyadicCircle_summable l n (x : ℂ) R) using 1
    ext q
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage, imp_iff_not_or]
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [localProfile_ae_moment_decay_on_window hl hp hp2 hη hwindow] with u hu
  by_cases hs : ∀ i, 0 < (localWalk l u i : ℝ)
  · obtain ⟨D, hD, hC, hbound⟩ := hu hs
    have ha := prescribedTrajectory_ae_summable_dyadic_circleL1_of_moment_decay
      (localBirth l u) (initial n) (localSafeCutoff l u) (x : ℂ) hR
      (fun k hk z hz ↦ by
        simpa only [infectious_initial] using hC z ((mem_closedBall.mp hz).trans_lt hRρ) k hk)
      hp.le hD hη (fun j k hJj hj hjk z hz ↦
        hbound n z ((mem_sphere.mp hz).trans_lt hRρ) j k hJj hj hjk)
    rw [← rankTrajectory_law (localBirth l u) (initial n)] at ha
    have hb := ae_of_ae_map (measurable_rankTrajectory (localBirth l u) (initial n)).aemeasurable ha
    exact hb.mono (fun v hv _ ↦ hv)
  · exact ae_of_all _ (fun _ h ↦ False.elim (hs h))

/-- The later time may depend measurably on the birth word. -/
theorem measurableSet_localUnshiftedProfileDiskDifferenceBad_time (l : ℝ) (n j : ℕ)
    (time : (ℕ → ℝ) → ℕ) (htime : Measurable time) (hj : ∀ u, j ≤ time u)
    (K : Set ℂ) (ε : ℝ) :
    MeasurableSet {q : (ℕ → ℝ) × (ℕ → ℝ) |
      q ∈ localUnshiftedProfileDiskDifferenceBad l n j (time q.1) K ε} := by
  have heq : {q : (ℕ → ℝ) × (ℕ → ℝ) |
      q ∈ localUnshiftedProfileDiskDifferenceBad l n j (time q.1) K ε} =
      ⋃ k : ℕ, ⋃ (_ : j ≤ k),
        {q : (ℕ → ℝ) × (ℕ → ℝ) | time q.1 = k} ∩
          localUnshiftedProfileDiskDifferenceBad l n j k K ε := by
    ext q
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨time q.1, hj q.1, rfl, h⟩
    · rintro ⟨k, _, hk, h⟩
      simpa only [hk] using h
  rw [heq]
  exact MeasurableSet.iUnion (fun k ↦ MeasurableSet.iUnion (fun hk ↦
    (measurableSet_eq_fun (htime.comp measurable_fst) measurable_const).inter
      (measurableSet_localUnshiftedProfileDiskDifferenceBad l n j k hk K ε)))

theorem localUnshiftedProfileDiskDifferenceBad_time_le_bad_add (l : ℝ) (n j : ℕ)
    (time : (ℕ → ℝ) → ℕ) (htime : Measurable time) (hjt : ∀ u, j ≤ time u)
    (z₀ : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hright : ∀ z ∈ closedBall z₀ R, 1 ≤ (Complex.exp z).re)
    {p M ε : ℝ} (hp : 1 ≤ p) (hM : 0 ≤ M) (hε : 0 < ε)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hgood : ∀ u, u ∉ B → (∀ i, 0 < (localWalk l u i : ℝ)) →
      localSafeCutoff l u ≤ j ∧
        ∀ z ∈ sphere z₀ R, localProfileMomentDifference l u n z p j (time u) ≤ M) :
    birthParentLaw.real {q : (ℕ → ℝ) × (ℕ → ℝ) |
      q ∈ localUnshiftedProfileDiskDifferenceBad l n j (time q.1) (closedBall z₀ r) ε} ≤
      uniformLaw.real B + (R / (2 * Real.pi * (R - r)) * (2 * Real.pi) * M ^ p⁻¹) / ε := by
  have hR : 0 < R := hr.trans_lt hrR
  have hgap : 0 < R - r := sub_pos.mpr hrR
  apply birthParentLaw_real_le_bad_add
    (measurableSet_localUnshiftedProfileDiskDifferenceBad_time l n j time htime hjt _ ε).nullMeasurableSet
    hB (by positivity)
  apply ae_of_all
  intro u hu
  by_cases hs : ∀ i, 0 < (localWalk l u i : ℝ)
  · obtain ⟨hJj, hm⟩ := hgood u hu hs
    have hC (i : ℕ) (z : ℂ) (hz : z ∈ closedBall z₀ R) :
        prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1 (localSafeCutoff l u) i ≠ 0 :=
      norm_pos_iff.mp (zero_lt_one.trans_le
        (one_le_norm_prescribedNormalizerFrom (hright z hz) (localBirth l u) 1 _ i))
    apply (measureReal_mono (μ := uniformLaw) (show
      {v | (u, v) ∈ localUnshiftedProfileDiskDifferenceBad l n j (time u) (closedBall z₀ r) ε} ⊆
        {v | ∃ z ∈ closedBall z₀ r,
          ε < ‖prescribedNormalizedProfile (Complex.exp z) (localBirth l u) (initial n)
              (localSafeCutoff l u) (time u) (rankState (localBirth l u) (initial n) v (time u)) -
            prescribedNormalizedProfile (Complex.exp z) (localBirth l u) (initial n)
              (localSafeCutoff l u) j (rankState (localBirth l u) (initial n) v j)‖} from ?_)).trans
    · apply (rankTrajectory_measureReal_preimage_le (localBirth l u) (initial n)
        {ω | ∃ z ∈ closedBall z₀ r,
          ε < ‖prescribedNormalizedProfile (Complex.exp z) (localBirth l u) (initial n)
              (localSafeCutoff l u) (time u) (ω (time u)) -
            prescribedNormalizedProfile (Complex.exp z) (localBirth l u) (initial n)
              (localSafeCutoff l u) j (ω j)‖}).trans
      apply prescribedTrajectory_uniform_difference_probability_le_of_two_normalizers
        (localBirth l u) (initial n) (localSafeCutoff l u) z₀ hr hrR hJj (hjt u)
        (by simpa only [infectious_initial] using hC j)
        (by simpa only [infectious_initial] using hC (time u)) hp hε
      exact hm
    · rintro v ⟨_, z, hz, he⟩
      refine ⟨z, hz, he.trans_le ?_⟩
      exact norm_unshifted_profile_difference_le
        (hright z (closedBall_subset_closedBall hrR.le hz)) (localBirth l u) (initial n) _ _
        hJj (hJj.trans (hjt u))
  · simp only [localUnshiftedProfileDiskDifferenceBad, mem_ofPred_eq, hs, false_and,
      Set.ofPred_false, measureReal_empty]
    positivity

/-- One shared late-time threshold controls every pair of local times and
all epidemic parameters above the lower endpoint. -/
theorem localProfile_unshifted_random_time_disk_tail_uniform {l₀ x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hr : 0 ≤ r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ l ≥ l₀, ∀ n j : ℕ, A ≤ j →
      ∀ time : (ℕ → ℝ) → ℕ, Measurable time → (∀ u, j ≤ time u) →
      birthParentLaw.real {q : (ℕ → ℝ) × (ℕ → ℝ) |
        q ∈ localUnshiftedProfileDiskDifferenceBad l n j (time q.1)
          (closedBall (x : ℂ) r) ε} < δ := by
  have hthird : 0 < δ / 3 := by positivity
  obtain ⟨D, hD, hDtight⟩ := localProfileMomentBad_uniform_tight hl₀ hp hp2 hη hwindow hthird
  obtain ⟨J₀, hJtight⟩ := localSafeCutoff_uniform_tight hl₀ hthird
  let M : ℕ → ℝ := fun j ↦ D * (j : ℝ) ^ (-η)
  let C : ℕ → ℝ := fun j ↦
    (R / (2 * Real.pi * (R - r)) * (2 * Real.pi) * (M j) ^ p⁻¹) / ε
  have hMt : Tendsto M atTop (𝓝 0) := by
    simpa only [M, Function.comp_def, mul_zero] using
      (((tendsto_rpow_neg_atTop hη).comp tendsto_natCast_atTop_atTop).const_mul D)
  have hCt : Tendsto C atTop (𝓝 0) := by
    have hh := ((hMt.rpow_const_nhds_zero (inv_pos.mpr (zero_lt_one.trans hp))).const_mul
      (R / (2 * Real.pi * (R - r)) * (2 * Real.pi))).div_const ε
    simpa only [C, mul_zero, zero_div] using hh
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp (hCt.eventually (Iio_mem_nhds hthird))
  let A := max A₀ (max J₀ 1)
  refine ⟨A, (le_max_right J₀ 1).trans (le_max_right A₀ _), ?_⟩
  intro l hl n j hj time htime hjt
  let E₀ : Set (ℕ → ℝ) := {u | j < localSafeCutoff l u}
  let E₁ := localProfileMomentBad p η ρ x D l
  have hE₀ : MeasurableSet E₀ :=
    measurableSet_lt measurable_const (measurable_localSafeCutoff l)
  have hE₁ : MeasurableSet E₁ := measurableSet_localProfileMomentBad _ _ _ _ _ _
  have h₀ : uniformLaw.real E₀ ≤ δ / 3 := by
    apply (measureReal_mono (μ := uniformLaw) (show E₀ ⊆ {u | J₀ < localSafeCutoff l u} from ?_)).trans
      (hJtight l hl)
    intro u hu
    exact ((le_max_left J₀ 1).trans ((le_max_right A₀ _).trans hj)).trans_lt hu
  have h₁ : uniformLaw.real E₁ ≤ δ / 3 := hDtight l hl
  have hCj : C j < δ / 3 := hA₀ j ((le_max_left A₀ _).trans hj)
  have hb := localUnshiftedProfileDiskDifferenceBad_time_le_bad_add l n j time htime hjt (x : ℂ) hr hrR
    hright hp.le (show 0 ≤ M j by dsimp [M]; positivity) hε (E₀ ∪ E₁) (hE₀.union hE₁) ?_
  · change birthParentLaw.real _ ≤ uniformLaw.real (E₀ ∪ E₁) + C j at hb
    have hu := measureReal_union_le (μ := uniformLaw) E₀ E₁
    linarith
  · intro u hu hs
    have hJj : localSafeCutoff l u ≤ j := le_of_not_gt (fun h ↦ hu (Or.inl h))
    refine ⟨hJj, ?_⟩
    intro z hz
    apply le_of_not_gt
    intro hbad
    apply hu (Or.inr ?_)
    refine ⟨hs, n, j, time u, hJj, ?_, hjt u, z, ?_, hbad⟩
    · exact (le_max_right J₀ 1).trans ((le_max_right A₀ _).trans hj)
    · rw [mem_sphere] at hz
      rw [hz]
      exact hRρ


/-- One product-a.e. event gives the same canonical limit simultaneously at
all tilts of the smaller closed disk. -/
theorem localProfile_joint_ae_unshifted_dyadic_limit {l x p η ρ R r : ℝ}
    (hl : 1 < l) (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hr : 0 ≤ r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η) (n : ℕ) :
    ∀ᵐ q ∂birthParentLaw, (∀ i, 0 < (localWalk l q.1 i : ℝ)) →
      TendstoUniformlyOn
        (fun m z ↦ localUnshiftedRankProfile l n q (localSafeCutoff l q.1 + 2 ^ m) z)
        (localUnshiftedRankProfileLimit l n q) atTop (closedBall (x : ℂ) r) := by
  filter_upwards [localProfile_joint_ae_summable_boundary hl hp hp2 hη
    (hr.trans_lt hrR) hRρ hwindow n] with q hq hs
  let F : ℕ → Unit → ℂ → ℂ := fun m _ z ↦
    prescribedNormalizedProfile (Complex.exp z) (localBirth l q.1) (initial n)
      (localSafeCutoff l q.1) (localSafeCutoff l q.1 + 2 ^ m)
      (rankState (localBirth l q.1) (initial n) q.2 (localSafeCutoff l q.1 + 2 ^ m))
  have hF (m : ℕ) : DifferentiableOn ℂ (F m ()) (closedBall (x : ℂ) R) := by
    apply differentiableOn_prescribedNormalizedProfile_exp
    intro z hz
    simpa only [infectious_initial] using (norm_pos_iff.mp (zero_lt_one.trans_le
      (one_le_norm_prescribedNormalizerFrom (hright z hz) (localBirth l q.1) 1
        (localSafeCutoff l q.1) (localSafeCutoff l q.1 + 2 ^ m))))
  have ht := (analyticSequenceLimit_tendstoUniformlyOn_of_summable_circleL1
    F () (x : ℂ) hr hrR hF (hq hs)).1
  have hlimit : analyticSequenceLimit F () = localRankProfileLimit l n q := rfl
  rw [hlimit] at ht
  rw [tendstoUniformlyOn_iff] at ht ⊢
  intro ε hε
  filter_upwards [ht ε hε] with m hm z hz
  have hle := norm_localUnshiftedRankProfileLimit_sub_le l n q
    (Nat.le_add_right (localSafeCutoff l q.1) (2 ^ m))
    (hright z (closedBall_subset_closedBall hrR.le hz))
  simpa only [dist_eq_norm] using hle.trans_lt (by
    simpa only [dist_eq_norm, F] using hm z hz)

def localUnshiftedProfileDiskLimitBad (l : ℝ) (n j : ℕ) (K : Set ℂ) (ε : ℝ) :
    Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧ ∃ z ∈ K,
    ε < ‖localUnshiftedRankProfile l n q j z - localUnshiftedRankProfileLimit l n q z‖}

/-- Actual joint local convergence, uniform over all epidemic parameters
above the fixed endpoint, all initial susceptible counts and all late times. -/
theorem localProfile_unshifted_disk_limit_tail_uniform {l₀ x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hr : 0 ≤ r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ l ≥ l₀, ∀ n j : ℕ, A ≤ j →
      birthParentLaw.real (localUnshiftedProfileDiskLimitBad l n j
        (closedBall (x : ℂ) r) ε) < δ := by
  obtain ⟨A, hA, htail⟩ := localProfile_unshifted_random_time_disk_tail_uniform
    hl₀ hp hp2 hη hr hrR hRρ hright hwindow
    (show 0 < ε / 2 by positivity) (show 0 < δ / 2 by positivity)
  refine ⟨A, hA, ?_⟩
  intro l hl n j hj
  let time : ℕ → (ℕ → ℝ) → ℕ := fun m u ↦ localSafeCutoff l u + 2 ^ m
  let E : ℕ → Set ((ℕ → ℝ) × (ℕ → ℝ)) := fun m ↦
    {q | q ∈ localUnshiftedProfileDiskDifferenceBad l n j (time m q.1)
      (closedBall (x : ℂ) r) (ε / 2)}
  have hb : ∀ᶠ m in atTop, birthParentLaw (E m) ≤ ENNReal.ofReal (δ / 2) := by
    have hpow : Tendsto (fun m : ℕ ↦ (2 : ℕ) ^ m) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    filter_upwards [hpow.eventually (eventually_ge_atTop j)] with m hm
    have hh := htail l hl n j hj (time m)
      ((measurable_localSafeCutoff l).add measurable_const)
      (fun u ↦ hm.trans (Nat.le_add_left _ _))
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ δ / 2 by positivity), Measure.real, E] using hh.le
  have he : birthParentLaw (localUnshiftedProfileDiskLimitBad l n j
      (closedBall (x : ℂ) r) ε) ≤ ENNReal.ofReal (δ / 2) := by
    apply measure_le_of_ae_eventually_mem birthParentLaw _ E hb
    filter_upwards [localProfile_joint_ae_unshifted_dyadic_limit (hl₀.trans_le hl) hp hp2 hη
      hr hrR hRρ hright (hwindow l hl) n] with q hq hbad
    obtain ⟨hs, z, hz, he⟩ := hbad
    have ht := (((hq hs).tendsto_at hz).sub_const (localUnshiftedRankProfile l n q j z)).norm
    have he' : ε / 2 < ‖localUnshiftedRankProfileLimit l n q z -
        localUnshiftedRankProfile l n q j z‖ := by
      rw [norm_sub_rev]
      linarith
    filter_upwards [ht.eventually (Ioi_mem_nhds he')] with m hm
    exact ⟨hs, z, hz, hm⟩
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  have hh : birthParentLaw.real (localUnshiftedProfileDiskLimitBad l n j
      (closedBall (x : ℂ) r) ε) ≤ δ / 2 := by
    simpa only [Measure.real, ENNReal.toReal_ofReal (show 0 ≤ δ / 2 by positivity)] using ht
  exact hh.trans_lt (by linarith)

end HeightPaper.CountCoupling
