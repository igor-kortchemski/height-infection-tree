module

public import HeightPaper.Probability.LocalProfileNonvanishing
public import HeightPaper.Probability.LocalProfileCarrier
public import HeightPaper.Probability.LocalProfileDiskTail
public import HeightPaper.Model.PrescribedSusceptible
public import HeightPaper.Probability.LocalProfileUniformLimit

/-! # Pointwise positivity on the joint birth-parent probability space -/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace HeightPaper.CountCoupling

theorem ae_real_continuousOn_of_local_closedBall
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Set ℝ) (L : Ω → ℂ → ℂ)
    (hlocal : ∀ x ∈ s, ∃ r > (0 : ℝ), ∀ᵐ ω ∂μ,
      ContinuousOn (L ω) (closedBall (x : ℂ) r)) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun x : ℝ => L ω (x : ℂ)) s := by
  classical
  choose r hr hcont using fun x : s => hlocal x x.property
  let U : s → Set ℝ := fun x => ball (x : ℝ) (r x / 2)
  have hcover : s ⊆ ⋃ x : s, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (half_pos (hr ⟨x, hx⟩))⟩
  obtain ⟨t, ht, hsub⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover
    U (fun _ => isOpen_ball) hcover
  have hall : ∀ᵐ ω ∂μ, ∀ x ∈ t, ContinuousOn (L ω) (closedBall (x : ℂ) (r x)) :=
    (ae_ball_iff ht).mpr (fun x _ => hcont x)
  filter_upwards [hall] with ω hω
  intro y hy
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hsub hy)
  obtain ⟨hxt, hyU⟩ := mem_iUnion.mp hx
  have hyball : (y : ℂ) ∈ ball (x : ℂ) (r x) := by
    have hy' : dist y (x : ℝ) < r x / 2 := hyU
    change dist (y : ℂ) ((x : ℝ) : ℂ) < r x
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [Real.dist_eq] at hy'
    linarith [hr x]
  have hnhds : closedBall (x : ℂ) (r x) ∈ 𝓝 (y : ℂ) :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hyball) ball_subset_closedBall
  exact (((hω x hxt).continuousAt hnhds).comp
    Complex.continuous_ofReal.continuousAt).continuousWithinAt

theorem ae_real_locallyUniformlyOn_of_local_uniform
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Set ℝ)
    (F : ℕ → Ω → ℂ → ℂ) (L : Ω → ℂ → ℂ)
    (hlocal : ∀ x ∈ s, ∃ r > (0 : ℝ), ∀ᵐ ω ∂μ,
      TendstoUniformlyOn (fun m => F m ω) (L ω) atTop (closedBall (x : ℂ) r)) :
    ∀ᵐ ω ∂μ, TendstoLocallyUniformlyOn
      (fun (m : ℕ) (x : ℝ) => F m ω (x : ℂ))
      (fun x : ℝ => L ω (x : ℂ)) atTop s := by
  classical
  choose r hr hlim using fun x : s => hlocal x x.property
  let U : s → Set ℝ := fun x => ball (x : ℝ) (r x / 2)
  have hU : ∀ x, IsOpen (U x) := fun _ => isOpen_ball
  have hcover : s ⊆ ⋃ x : s, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (half_pos (hr ⟨x, hx⟩))⟩
  obtain ⟨t, ht, hsub⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover
    U hU hcover
  have hall : ∀ᵐ ω ∂μ, ∀ x ∈ t,
      TendstoUniformlyOn (fun m => F m ω) (L ω) atTop (closedBall (x : ℂ) (r x)) :=
    (ae_ball_iff ht).mpr (fun x _ => hlim x)
  filter_upwards [hall] with ω hω
  apply (tendstoLocallyUniformlyOn_biUnion (fun x _ => hU x) ?_).mono hsub
  intro x hx
  apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
  apply ((hω x hx).comp (fun y : ℝ => (y : ℂ))).mono
  intro y hy
  have hy' : dist y (x : ℝ) < r x / 2 := hy
  change dist (y : ℂ) ((x : ℝ) : ℂ) ≤ r x
  rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [Real.dist_eq] at hy'
  linarith [hr x]

theorem localUnshiftedRankProfileLimit_joint_ae_continuous_disk {l x p η ρ R r : ℝ}
    (hl : 1 < l) (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hr : 0 ≤ r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η) (n : ℕ) :
    ∀ᵐ q ∂birthParentLaw, (∀ i, 0 < (localWalk l q.1 i : ℝ)) →
      ContinuousOn (localUnshiftedRankProfileLimit l n q) (closedBall (x : ℂ) r) := by
  filter_upwards [localProfile_joint_ae_unshifted_dyadic_limit hl hp hp2 hη
    hr hrR hRρ hright hwindow n] with q hq hs
  apply (hq hs).continuousOn
  apply Frequently.of_forall
  intro m
  apply (Model.differentiableOn_prescribedNormalizedProfile_exp
    (localBirth l q.1) (Model.initial n)
    (Model.rankState (localBirth l q.1) (Model.initial n) q.2
      (localSafeCutoff l q.1 + 2 ^ m)) 0 (localSafeCutoff l q.1 + 2 ^ m)
    ?_).continuousOn.mono
    (closedBall_subset_closedBall hrR.le)
  intro z hz
  have hn := Model.one_le_norm_prescribedNormalizer (hright z hz)
    (localBirth l q.1) 1 (localSafeCutoff l q.1 + 2 ^ m)
  simpa only [Model.infectious_initial, Model.prescribedNormalizerFrom_zero] using
    (norm_pos_iff.mp (zero_lt_one.trans_le hn))

/-- The canonical unshifted limit is analytic inside each admissible disk on
the same joint almost-sure event used for its uniform convergence. -/
theorem localUnshiftedRankProfileLimit_joint_ae_differentiable_disk {l x p η ρ R r : ℝ}
    (hl : 1 < l) (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hr : 0 ≤ r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η) (n : ℕ) :
    ∀ᵐ q ∂birthParentLaw, (∀ i, 0 < (localWalk l q.1 i : ℝ)) →
      DifferentiableOn ℂ (localUnshiftedRankProfileLimit l n q) (ball (x : ℂ) r) := by
  filter_upwards [localProfile_joint_ae_summable_boundary hl hp hp2 hη
    (hr.trans_lt hrR) hRρ hwindow n] with q hq hs
  let F : ℕ → Unit → ℂ → ℂ := fun m _ z =>
    Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l q.1) (Model.initial n)
      (localSafeCutoff l q.1) (localSafeCutoff l q.1 + 2 ^ m)
      (Model.rankState (localBirth l q.1) (Model.initial n) q.2
        (localSafeCutoff l q.1 + 2 ^ m))
  have hF (m : ℕ) : DifferentiableOn ℂ (F m ()) (closedBall (x : ℂ) R) := by
    apply Model.differentiableOn_prescribedNormalizedProfile_exp
    intro z hz
    simpa only [Model.infectious_initial] using (norm_pos_iff.mp (zero_lt_one.trans_le
      (Model.one_le_norm_prescribedNormalizerFrom (hright z hz) (localBirth l q.1) 1
        (localSafeCutoff l q.1) (localSafeCutoff l q.1 + 2 ^ m))))
  have hnum := (analyticSequenceLimit_tendstoUniformlyOn_of_summable_circleL1
    F () (x : ℂ) hr hrR hF (hq hs)).2
  have hlimit : analyticSequenceLimit F () = localRankProfileLimit l n q := rfl
  rw [hlimit] at hnum
  have hden : Differentiable ℂ (localProfilePrefixNormalizer l q.1) := by
    unfold localProfilePrefixNormalizer
    simpa only [Model.prescribedNormalizerFrom_zero] using
      (Model.differentiable_prescribedNormalizerFrom_exp
        (localBirth l q.1) 1 0 (localSafeCutoff l q.1))
  have hdenNZ : ∀ z ∈ ball (x : ℂ) r, localProfilePrefixNormalizer l q.1 z ≠ 0 := by
    intro z hz
    have hzin : z ∈ closedBall (x : ℂ) R :=
      closedBall_subset_closedBall hrR.le (ball_subset_closedBall hz)
    have hn := Model.one_le_norm_prescribedNormalizer (hright z hzin)
      (localBirth l q.1) 1 (localSafeCutoff l q.1)
    change 1 ≤ ‖localProfilePrefixNormalizer l q.1 z‖ at hn
    exact norm_pos_iff.mp (zero_lt_one.trans_le hn)
  change DifferentiableOn ℂ
    (fun z => localRankProfileLimit l n q z / localProfilePrefixNormalizer l q.1 z)
    (ball (x : ℂ) r)
  exact hnum.div hden.differentiableOn hdenNZ

theorem localUnshiftedRankProfileLimit_joint_ae_continuous_real {l : ℝ}
    (hl : 1 < l) (n : ℕ) :
    ∀ᵐ q ∂birthParentLaw, (∀ i, 0 < (localWalk l q.1 i : ℝ)) →
      ContinuousOn (fun x : ℝ => localUnshiftedRankProfileLimit l n q (x : ℂ))
        (Ioo (0 : ℝ) (profileRoot l)) := by
  classical
  let L : ((ℕ → ℝ) × (ℕ → ℝ)) → ℂ → ℂ := fun q z =>
    if ∀ i, 0 < (localWalk l q.1 i : ℝ) then localUnshiftedRankProfileLimit l n q z else 0
  have hlocal : ∀ x ∈ Ioo (0 : ℝ) (profileRoot l),
      ∃ r > (0 : ℝ), ∀ᵐ q ∂birthParentLaw,
        ContinuousOn (L q) (closedBall (x : ℂ) r) := by
    intro x hx
    obtain ⟨p, hp, η, hη, ρ, hρ, hw⟩ :=
      exists_localProfile_unshifted_moment_disk hl hx.1 hx.2
    have hr : 0 ≤ ρ / 4 := by positivity
    have hrR : ρ / 4 < ρ / 2 := by linarith
    have hRρ : ρ / 2 < ρ := by linarith
    have hright : ∀ z ∈ closedBall (x : ℂ) (ρ / 2),
        1 ≤ (Complex.exp z).re := by
      intro z hz
      exact (hw l le_rfl z ((mem_closedBall.mp hz).trans_lt hRρ)).1.le
    have hwindow : ∀ z : ℂ, dist z (x : ℂ) < ρ →
        0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
          complexProfileMomentExponent l z p ≤ -1 - η :=
      fun z hz => (hw l le_rfl z hz).2
    refine ⟨ρ / 4, by positivity, ?_⟩
    filter_upwards [localUnshiftedRankProfileLimit_joint_ae_continuous_disk hl
      hp.1 hp.2.le hη hr hrR hRρ hright hwindow n] with q hq
    by_cases hs : ∀ i, 0 < (localWalk l q.1 i : ℝ)
    · simpa only [L, ite_eq_left hs] using hq hs
    · simpa only [L, ite_eq_right hs] using (continuousOn_const :
        ContinuousOn (fun _ : ℂ => (0 : ℂ)) (closedBall (x : ℂ) (ρ / 4)))
  filter_upwards [ae_real_continuousOn_of_local_closedBall birthParentLaw
    (Ioo (0 : ℝ) (profileRoot l)) L hlocal] with q hq hs
  simpa only [L, ite_eq_left hs] using hq

theorem localUnshiftedRankProfileLimit_joint_ae_locallyUniform_real {l : ℝ}
    (hl : 1 < l) (n : ℕ) :
    ∀ᵐ q ∂birthParentLaw, (∀ i, 0 < (localWalk l q.1 i : ℝ)) →
      TendstoLocallyUniformlyOn
        (fun (m : ℕ) (x : ℝ) => localUnshiftedRankProfile l n q
          (localSafeCutoff l q.1 + 2 ^ m) (x : ℂ))
        (fun x : ℝ => localUnshiftedRankProfileLimit l n q (x : ℂ))
        atTop (Ioo (0 : ℝ) (profileRoot l)) := by
  classical
  let F : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℂ → ℂ := fun m q z =>
    if ∀ i, 0 < (localWalk l q.1 i : ℝ) then
      localUnshiftedRankProfile l n q (localSafeCutoff l q.1 + 2 ^ m) z else 0
  let L : ((ℕ → ℝ) × (ℕ → ℝ)) → ℂ → ℂ := fun q z =>
    if ∀ i, 0 < (localWalk l q.1 i : ℝ) then localUnshiftedRankProfileLimit l n q z else 0
  have hlocal : ∀ x ∈ Ioo (0 : ℝ) (profileRoot l),
      ∃ r > (0 : ℝ), ∀ᵐ q ∂birthParentLaw,
        TendstoUniformlyOn (fun m => F m q) (L q) atTop (closedBall (x : ℂ) r) := by
    intro x hx
    obtain ⟨p, hp, η, hη, ρ, hρ, hw⟩ :=
      exists_localProfile_unshifted_moment_disk hl hx.1 hx.2
    have hr : 0 ≤ ρ / 4 := by positivity
    have hrR : ρ / 4 < ρ / 2 := by linarith
    have hRρ : ρ / 2 < ρ := by linarith
    have hright : ∀ z ∈ closedBall (x : ℂ) (ρ / 2),
        1 ≤ (Complex.exp z).re := by
      intro z hz
      exact (hw l le_rfl z ((mem_closedBall.mp hz).trans_lt hRρ)).1.le
    have hwindow : ∀ z : ℂ, dist z (x : ℂ) < ρ →
        0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
          complexProfileMomentExponent l z p ≤ -1 - η :=
      fun z hz => (hw l le_rfl z hz).2
    refine ⟨ρ / 4, by positivity, ?_⟩
    filter_upwards [localProfile_joint_ae_unshifted_dyadic_limit hl hp.1 hp.2.le hη
      hr hrR hRρ hright hwindow n] with q hq
    by_cases hs : ∀ i, 0 < (localWalk l q.1 i : ℝ)
    · simpa only [F, L, ite_eq_left hs] using hq hs
    · simp only [F, L, ite_eq_right hs]
      rw [tendstoUniformlyOn_iff]
      intro ε hε
      exact Eventually.of_forall (fun _ _ _ => by simpa using hε)
  filter_upwards [ae_real_locallyUniformlyOn_of_local_uniform birthParentLaw
    (Ioo (0 : ℝ) (profileRoot l)) F L hlocal] with q hq hs
  simpa only [F, L, ite_eq_left hs] using hq

theorem localUnshiftedRankProfileLimit_initial_independent (l : ℝ) (n : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) (z : ℂ) :
    localUnshiftedRankProfileLimit l n q z = localUnshiftedRankProfileLimit l 0 q z := by
  unfold localUnshiftedRankProfileLimit localRankProfileLimit localAnalyticProfileLimit
  exact congrArg (fun v : ℂ => v / localProfilePrefixNormalizer l q.1 z)
    (Model.rankState_initial_analyticProfileLimit (localBirth l q.1) n
      (localSafeCutoff l q.1) q.2 z)

theorem localUnshiftedRankProfileLimit_ae_nonzero_all_real_nested {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
      ∀ᵐ v ∂uniformLaw, ∀ x ∈ Ioo (0 : ℝ) (profileRoot l),
        localUnshiftedRankProfileLimit l n (u, v) (x : ℂ) ≠ 0 := by
  filter_upwards [localAnalyticProfileLimit_ae_nonzero_all_real hl] with u hu hs n
  filter_upwards [hu hs n] with v hv x hx
  have he : 1 ≤ (Complex.exp (x : ℂ)).re := by
    simpa only [← Complex.ofReal_exp, Complex.ofReal_re] using
      (Real.one_le_exp_iff.mpr hx.1.le)
  have hd : localProfilePrefixNormalizer l u (x : ℂ) ≠ 0 := by
    have hh := Model.one_le_norm_prescribedNormalizer he (localBirth l u) 1
      (localSafeCutoff l u)
    change Model.prescribedNormalizer (Complex.exp (x : ℂ)) (localBirth l u) 1
      (localSafeCutoff l u) ≠ 0
    intro hz
    rw [hz, norm_zero] at hh
    norm_num at hh
  exact div_ne_zero (hv x hx) hd

theorem localUnshiftedRankProfileLimit_ae_nonzero_at {l x : ℝ} (hl : 1 < l)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (n : ℕ) :
    ∀ᵐ q ∂birthParentLaw, (∀ i, 0 < (localWalk l q.1 i : ℝ)) →
      localUnshiftedRankProfileLimit l n q (x : ℂ) ≠ 0 := by
  have hmeas : MeasurableSet {q : (ℕ → ℝ) × (ℕ → ℝ) |
      (∀ i, 0 < (localWalk l q.1 i : ℝ)) → localRankProfileLimit l n q (x : ℂ) ≠ 0} := by
    convert ((measurableSet_local_survival l).preimage measurable_fst).compl.union
      (measurableSet_eq_fun (measurable_localRankProfileLimit l n (x : ℂ))
        (measurable_const : Measurable (fun _ : (ℕ → ℝ) × (ℕ → ℝ) => (0 : ℂ)))).compl using 1
    ext q
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage, imp_iff_not_or]
  have hnum : ∀ᵐ q ∂birthParentLaw, (∀ i, 0 < (localWalk l q.1 i : ℝ)) →
      localRankProfileLimit l n q (x : ℂ) ≠ 0 := by
    change ∀ᵐ q ∂uniformLaw.prod uniformLaw, _
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    filter_upwards [localAnalyticProfileLimit_ae_nonzero_all_real hl] with u hu
    by_cases hs : ∀ i, 0 < (localWalk l u i : ℝ)
    · filter_upwards [hu hs n] with v hv
      intro _
      exact hv x hx
    · exact ae_of_all _ (fun _ h ↦ False.elim (hs h))
  filter_upwards [hnum] with q hq hs
  have he : 1 ≤ (Complex.exp (x : ℂ)).re := by
    simpa only [← Complex.ofReal_exp, Complex.ofReal_re] using
      (Real.one_le_exp_iff.mpr hx.1.le)
  have hd : localProfilePrefixNormalizer l q.1 (x : ℂ) ≠ 0 := by
    have hh := Model.one_le_norm_prescribedNormalizer he (localBirth l q.1) 1
      (localSafeCutoff l q.1)
    change Model.prescribedNormalizer (Complex.exp (x : ℂ)) (localBirth l q.1) 1
      (localSafeCutoff l q.1) ≠ 0
    intro hz
    rw [hz, norm_zero] at hh
    norm_num at hh
  exact div_ne_zero (hq hs) hd

/-- At a fixed admissible tilt the lower tail of the actual joint-law limit
can be made arbitrarily small; no uniformity in the tilt is assumed here. -/
theorem localUnshiftedRankProfileLimit_fixed_tilt_lower_tight {l x : ℝ} (hl : 1 < l)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c > (0 : ℝ), birthParentLaw.real {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖ < c} < δ := by
  let S : ℕ → Set ((ℕ → ℝ) × (ℕ → ℝ)) := fun m =>
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖ ≤ 1 / ((m + 1 : ℕ) : ℝ)}
  have hmeas (m : ℕ) : MeasurableSet (S m) := by
    exact ((measurableSet_local_survival l).preimage measurable_fst).inter
      (measurableSet_le (measurable_localUnshiftedRankProfileLimit l n (x : ℂ)).norm
        measurable_const)
  have hanti : Antitone S := by
    intro m k hmk q hq
    refine ⟨hq.1, hq.2.trans ?_⟩
    apply one_div_le_one_div_of_le (by exact_mod_cast Nat.succ_pos m)
    exact_mod_cast Nat.add_le_add_right hmk 1
  have hlim : Tendsto (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hsubset : (⋂ m, S m) ⊆ {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      localUnshiftedRankProfileLimit l n q (x : ℂ) = 0} := by
    intro q hq
    have hs := (mem_iInter.mp hq 0).1
    have hn : ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖ ≤ 0 :=
      ge_of_tendsto hlim (Eventually.of_forall fun m => (mem_iInter.mp hq m).2)
    exact ⟨hs, norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))⟩
  have hzero : birthParentLaw {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      localUnshiftedRankProfileLimit l n q (x : ℂ) = 0} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [localUnshiftedRankProfileLimit_ae_nonzero_at hl hx n] with q hq
    exact fun h => hq h.1 h.2
  have hInter : birthParentLaw (⋂ m, S m) = 0 :=
    le_antisymm ((measure_mono hsubset).trans_eq hzero) bot_le
  have ht := tendsto_measure_iInter_atTop (μ := birthParentLaw) (s := S)
    (fun m => (hmeas m).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hInter] at ht
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (ht.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hδ)))
  let c : ℝ := 1 / ((M + 1 : ℕ) : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  have hsub : {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖ < c} ⊆ S M := by
    rintro q ⟨hs, hb⟩
    exact ⟨hs, hb.le⟩
  have hb : birthParentLaw.real (S M) < δ := by
    have hh := hM M le_rfl
    change birthParentLaw (S M) < ENNReal.ofReal δ at hh
    rw [← ofReal_measureReal (μ := birthParentLaw) (s := S M)] at hh
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mp hh
  exact (measureReal_mono (μ := birthParentLaw) hsub (measure_ne_top _ _)).trans_lt hb

theorem localUnshiftedRankProfileLimit_fixed_tilt_lower_tight_uniform_n {l x : ℝ}
    (hl : 1 < l) (hx : x ∈ Ioo (0 : ℝ) (profileRoot l))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c > (0 : ℝ), ∀ n : ℕ, birthParentLaw.real
      {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
        ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖ < c} < δ := by
  obtain ⟨c, hc, hb⟩ := localUnshiftedRankProfileLimit_fixed_tilt_lower_tight hl hx 0 hδ
  refine ⟨c, hc, ?_⟩
  intro n
  simpa only [localUnshiftedRankProfileLimit_initial_independent] using hb

/-- On a compact real tilt set, strict smallness can be witnessed on any
dense subset as soon as the profile is continuous there. -/
theorem exists_small_on_dense_iff {K : Set ℝ} {T : Set K} (hT : Dense T)
    {f : ℝ → ℂ} (hf : ContinuousOn f K) (c : ℝ) :
    (∃ x ∈ K, ‖f x‖ < c) ↔ ∃ t ∈ T, ‖f (t : ℝ)‖ < c := by
  have hfc : Continuous (fun t : K => f (t : ℝ)) :=
    continuousOn_iff_continuous_domRestrict.mp hf
  let U : Set K := {t | ‖f (t : ℝ)‖ < c}
  have hU : IsOpen U := isOpen_lt hfc.norm continuous_const
  constructor
  · rintro ⟨x, hx, hsmall⟩
    obtain ⟨t, ht, htu⟩ := hT.exists_mem_open hU ⟨⟨x, hx⟩, hsmall⟩
    exact ⟨t, ht, htu⟩
  · rintro ⟨t, ht, hsmall⟩
    exact ⟨t, t.property, hsmall⟩

/-- For a fixed supercritical parameter, the lower tail is uniform over a
compact set of admissible real tilts and over the initial susceptible count. -/
theorem localUnshiftedRankProfileLimit_compact_lower_tight {l : ℝ} (hl : 1 < l)
    {K : Set ℝ} (hK : IsCompact K) (hKd : K ⊆ Ioo 0 (profileRoot l))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c > (0 : ℝ), ∀ n : ℕ, birthParentLaw.real
      {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
        ∃ x ∈ K, ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖ < c} < δ := by
  classical
  obtain ⟨T, hTc, hTd⟩ := TopologicalSpace.exists_countable_dense K
  let : Countable T := hTc.to_subtype
  let S : ℝ → Set ((ℕ → ℝ) × (ℕ → ℝ)) := fun c =>
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ t : T, ‖localUnshiftedRankProfileLimit l 0 q ((t : K) : ℂ)‖ < c}
  have hmeas (c : ℝ) : MeasurableSet (S c) := by
    apply ((measurableSet_local_survival l).preimage measurable_fst).inter
    have hh : MeasurableSet (⋃ t : T, {q | ‖localUnshiftedRankProfileLimit l 0 q
        ((t : K) : ℂ)‖ < c}) :=
      MeasurableSet.iUnion (fun t : T =>
        measurableSet_lt (measurable_localUnshiftedRankProfileLimit l 0
          ((t : K) : ℂ)).norm measurable_const)
    change MeasurableSet {q | ∃ t : T,
      ‖localUnshiftedRankProfileLimit l 0 q ((t : K) : ℂ)‖ < c}
    simpa only [Set.iUnion_ofPred] using hh
  let A : ℕ → Set ((ℕ → ℝ) × (ℕ → ℝ)) := fun m => S (1 / ((m + 1 : ℕ) : ℝ))
  have hanti : Antitone A := by
    intro m k hmk q hq
    refine ⟨hq.1, ?_⟩
    obtain ⟨t, ht⟩ := hq.2
    refine ⟨t, ht.trans_le ?_⟩
    apply one_div_le_one_div_of_le (by exact_mod_cast Nat.succ_pos m)
    exact_mod_cast Nat.add_le_add_right hmk 1
  have hlim : Tendsto (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hcont := localUnshiftedRankProfileLimit_joint_ae_continuous_real hl 0
  have hzero : birthParentLaw (⋂ m, A m) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    change ∀ᵐ q ∂uniformLaw.prod uniformLaw, q ∉ ⋂ m, A m
    apply (Measure.ae_prod_iff_ae_ae (MeasurableSet.iInter fun m => hmeas _).compl).mpr
    have hcont' := Measure.ae_ae_of_ae_prod hcont
    filter_upwards [localUnshiftedRankProfileLimit_ae_nonzero_all_real_nested hl,
      hcont'] with u hu hcu
    by_cases hs : ∀ i, 0 < (localWalk l u i : ℝ)
    · filter_upwards [hu hs 0, hcu] with v hv hcv hmem
      have hf : ContinuousOn (fun x : ℝ =>
          localUnshiftedRankProfileLimit l 0 (u, v) (x : ℂ)) K :=
        (hcv hs).mono hKd
      have hpos : ∀ x ∈ K, 0 < ‖localUnshiftedRankProfileLimit l 0 (u, v) (x : ℂ)‖ := by
        intro x hx
        exact norm_pos_iff.mpr (hv x (hKd hx))
      obtain ⟨b, hb, hbound⟩ := hK.exists_forall_le' hf.norm hpos
      have hbzero : b ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall fun m => by
        obtain ⟨t, ht⟩ := (mem_iInter.mp hmem m).2
        exact (hbound (t : ℝ) (t : K).property).trans ht.le)
      exact (not_le_of_gt hb) hbzero
    · exact ae_of_all _ (fun v hmem => hs (mem_iInter.mp hmem 0).1)
  have ht := tendsto_measure_iInter_atTop (μ := birthParentLaw) (s := A)
    (fun m => (hmeas _).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hzero] at ht
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (ht.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hδ)))
  let c : ℝ := 1 / ((M + 1 : ℕ) : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro n
  have heq : {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ x ∈ K, ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖ < c} =ᵐ[birthParentLaw]
      S c := by
    filter_upwards [hcont] with q hq
    by_cases hs : ∀ i, 0 < (localWalk l q.1 i : ℝ)
    · apply propext
      change ((∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
        ∃ x ∈ K, ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖ < c) ↔
        ((∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
          ∃ t : T, ‖localUnshiftedRankProfileLimit l 0 q ((t : K) : ℂ)‖ < c)
      constructor
      · rintro ⟨_, hx⟩
        have hx0 : ∃ x ∈ K, ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ < c := by
          simpa only [localUnshiftedRankProfileLimit_initial_independent] using hx
        obtain ⟨t, ht, hsmall⟩ :=
          (exists_small_on_dense_iff hTd ((hq hs).mono hKd) c).mp hx0
        exact ⟨hs, ⟨⟨t, ht⟩, hsmall⟩⟩
      · rintro ⟨_, ⟨t, ht⟩⟩
        obtain ⟨x, hx, hsmall⟩ :=
          (exists_small_on_dense_iff hTd ((hq hs).mono hKd) c).mpr
            ⟨(t : K), t.property, ht⟩
        refine ⟨hs, x, hx, ?_⟩
        simpa only [localUnshiftedRankProfileLimit_initial_independent] using hsmall
    · simp only [S, Set.mem_ofPred_eq, hs, false_and]
  have hb : birthParentLaw.real (S c) < δ := by
    have hh := hM M le_rfl
    change birthParentLaw (S c) < ENNReal.ofReal δ at hh
    rw [← ofReal_measureReal (μ := birthParentLaw) (s := S c)] at hh
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mp hh
  exact (measureReal_congr heq).trans_lt hb

end HeightPaper.CountCoupling
