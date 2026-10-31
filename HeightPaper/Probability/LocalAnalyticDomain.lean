module

public import HeightPaper.Probability.LocalAnalyticProfile
public import HeightPaper.Probability.LocalProfileMomentTightness
public import Mathlib.Topology.Compactness.Lindelof

/-!
# One count-word event for the whole real profile domain

The count controls are selected before the real tilt. A countable open cover
then yields one parent-draw probability-one event of local uniform convergence
and continuity on the entire admissible real interval.
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology BigOperators

namespace HeightPaper

/-- Local complex disk limits can be assembled on one probability-one event
over an arbitrary real set, by a countable open subcover. -/
theorem ae_real_locallyUniformlyOn_of_local_disk_limits
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Set ℝ)
    (F : ℕ → Ω → ℂ → ℂ) (L : Ω → ℂ → ℂ)
    (hlocal : ∀ x ∈ s, ∃ r > (0 : ℝ), ∀ᵐ ω ∂μ,
      TendstoUniformlyOn (fun m => F m ω) (L ω) atTop (closedBall (x : ℂ) r) ∧
      DifferentiableOn ℂ (L ω) (ball (x : ℂ) r)) :
    ∀ᵐ ω ∂μ,
      TendstoLocallyUniformlyOn (fun (m : ℕ) (x : ℝ) => F m ω (x : ℂ))
        (fun x : ℝ => L ω (x : ℂ)) atTop s ∧
      ContinuousOn (fun x : ℝ => L ω (x : ℂ)) s := by
  classical
  choose r hr hlim using fun x : s => hlocal x x.property
  let U : s → Set ℝ := fun x => ball (x : ℝ) (r x / 2)
  have hU : ∀ x, IsOpen (U x) := fun _ => isOpen_ball
  have hcover : s ⊆ ⋃ x : s, U x := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact mem_ball_self (div_pos (hr ⟨x, hx⟩) (by norm_num))
  obtain ⟨t, ht, hcover⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover
    U hU hcover
  have hall : ∀ᵐ ω ∂μ, ∀ x ∈ t,
      TendstoUniformlyOn (fun m => F m ω) (L ω) atTop (closedBall (x : ℂ) (r x)) ∧
      DifferentiableOn ℂ (L ω) (ball (x : ℂ) (r x)) :=
    (ae_ball_iff ht).mpr (fun x _ => hlim x)
  have hUball (x : s) {y : ℝ} (hy : y ∈ U x) : (y : ℂ) ∈ ball (x : ℂ) (r x) := by
    have hy' : dist y (x : ℝ) < r x / 2 := hy
    change dist (y : ℂ) ((x : ℝ) : ℂ) < r x
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [Real.dist_eq] at hy'
    linarith [hr x]
  filter_upwards [hall] with ω hω
  constructor
  · apply (tendstoLocallyUniformlyOn_biUnion (fun x _ => hU x) ?_).mono hcover
    intro x hx
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    exact ((hω x hx).1.comp (fun y : ℝ => (y : ℂ))).mono
      (fun y hy => ball_subset_closedBall (hUball x hy))
  · intro y hy
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hcover hy)
    obtain ⟨hxt, hyU⟩ := mem_iUnion.mp hx
    have hd := (hω x hxt).2.differentiableAt (isOpen_ball.mem_nhds (hUball x hyU))
    exact (hd.continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt

namespace CountCoupling

/-- This event is selected once, before every real tilt and every initial
state. Each disk uses the same explicit canonical function. -/
theorem localProfile_ae_canonical_analytic_limit_all_real {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
      ∀ x : ℝ, 0 < x → x < profileRoot l → ∃ R > (0 : ℝ), ∀ n : ℕ,
        (∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
          ∀ r : ℝ, 0 ≤ r → r < R →
            TendstoUniformlyOn
              (fun m z => Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + 2 ^ m)
                (ω (localSafeCutoff l u + 2 ^ m)))
              (localAnalyticProfileLimit l n u ω) atTop (closedBall (x : ℂ) r) ∧
            DifferentiableOn ℂ (localAnalyticProfileLimit l n u ω) (ball (x : ℂ) r)) ∧
        ∀ r : ℝ, 0 ≤ r → r < R → ∀ ε > (0 : ℝ),
          Tendsto (fun k =>
            (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)).real
              {ω | ∃ z ∈ closedBall (x : ℂ) r,
                ε < ‖localAnalyticProfileLimit l n u ω z -
                  Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                    (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
                    (ω (localSafeCutoff l u + k))‖}) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_finiteLocalCenteredReciprocal hl,
    positiveReciprocal_ae_uniform_bounded hl, localSafeCutoff_ae_bddAbove hl]
    with u hconv hratio hcut
  intro hs
  obtain ⟨M₀, hM₀⟩ := hratio
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hr : ∀ k, positiveReciprocal l u k ≤ M :=
    fun k => (hM₀ l le_rfl k).trans (le_max_left _ _)
  obtain ⟨B, hB, hBbound⟩ := (Metric.isBounded_range_of_tendsto _ hconv).exists_pos_norm_le
  have hcenter : ∀ k, |(∑ i ∈ Finset.range k, localBirthCoefficient l u i) -
      growthFactor l * Real.log k| ≤ B := by
    intro k
    have hh := hBbound (finiteLocalCenteredReciprocal l u k) ⟨k, rfl⟩
    simpa only [Real.norm_eq_abs, finiteLocalCenteredReciprocal, localBirthCoefficient,
      ite_eq_left (show ∀ i ≤ k, 0 < (localWalk l u i : ℝ) from fun i _ => hs i),
      one_mul, growthFactor] using hh
  intro x hx hxr
  obtain ⟨p, hp, η, hη, r₀, hr₀, hwindow⟩ := exists_localProfile_moment_disk hl hx hxr
  let D := localProfileMomentEnvelope M B (localSafeCutoff l u) p η
  have hD : 0 ≤ D := localProfileMomentEnvelope_nonneg hM hη _
  refine ⟨r₀ / 2, by positivity, ?_⟩
  intro n
  have hC : ∀ k ≥ localSafeCutoff l u, ∀ z ∈ closedBall (x : ℂ) (r₀ / 2),
      Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u)
        (Model.infectious (Model.initial n)) (localSafeCutoff l u) k ≠ 0 := by
    intro k _ z hz
    have hz' : dist z (x : ℂ) < r₀ := lt_of_le_of_lt hz (by linarith)
    have hzr := (hwindow l le_rfl z hz').2.1
    simp only [Model.infectious_initial]
    rw [localNormalizer_eq_exp_centered l u hs hcut k z (by linarith [profileRoot_pos hl])]
    exact Complex.exp_ne_zero _
  apply Model.prescribedTrajectory_canonical_analytic_limit_in_probability_of_moment_decay
    (localBirth l u) (Model.initial n) (localSafeCutoff l u) (x : ℂ)
    (show 0 < r₀ / 2 by positivity) hC hp.1.le hD hη
  intro j N hJj hj hjN z hz
  have hz' : dist z (x : ℂ) < r₀ := by rw [mem_sphere] at hz; rw [hz]; linarith
  obtain ⟨hz0, hzr, hpz, he⟩ := hwindow l le_rfl z hz'
  exact localProfileMomentDifference_le_envelope hl hM hB.le hp.1 hp.2.le hη
    u hs hr hcut hcenter (localSafeCutoff l u) le_rfl n z hz0 hzr hpz he j N hJj hj hjN

/-- Both probability-one quantifiers precede the entire real interval. This
is the domain-wide continuity required by the closed-zero-set argument. -/
theorem localProfile_ae_real_domain_convergence {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
      ∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
        TendstoLocallyUniformlyOn
          (fun (m : ℕ) (x : ℝ) => Model.prescribedNormalizedProfile (Complex.exp (x : ℂ))
            (localBirth l u) (Model.initial n) (localSafeCutoff l u)
            (localSafeCutoff l u + 2 ^ m) (ω (localSafeCutoff l u + 2 ^ m)))
          (fun x : ℝ => localAnalyticProfileLimit l n u ω (x : ℂ))
          atTop (Ioo (0 : ℝ) (profileRoot l)) ∧
        ContinuousOn (fun x : ℝ => localAnalyticProfileLimit l n u ω (x : ℂ))
          (Ioo (0 : ℝ) (profileRoot l)) := by
  filter_upwards [localProfile_ae_canonical_analytic_limit_all_real hl] with u hu
  intro hs n
  apply ae_real_locallyUniformlyOn_of_local_disk_limits
    (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n))
    (Ioo (0 : ℝ) (profileRoot l))
    (fun m ω z => Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
      (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + 2 ^ m)
      (ω (localSafeCutoff l u + 2 ^ m))) (localAnalyticProfileLimit l n u)
  intro x hx
  obtain ⟨R, hR, hlim⟩ := hu hs x hx.1 hx.2
  refine ⟨R / 2, by positivity, ?_⟩
  exact (hlim n).1.mono (fun ω hω => hω (R / 2) (by positivity) (by linarith))

end CountCoupling
end HeightPaper
