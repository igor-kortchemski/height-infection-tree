module

public import HeightPaper.Model.AnalyticProfileAlmostSure
public import HeightPaper.Probability.LocalProfileGeneralComplexAnalytic

/-!
# Almost-sure compact-uniform convergence for every physical time

This supplies the full-time almost-sure conclusion of the paper's
`proposition cv unif martingale`, to the existing canonical analytic limit.
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology

namespace HeightPaper.CountCoupling

theorem localProfile_ae_canonical_complex_disk_limit_ae
    {l p : ℝ} {z₀ : ℂ} (hl : 1 < l) (hp : 1 < p) (hp2 : p ≤ 2)
    (hz : z₀.re < profileRoot l)
    (he : complexProfileMomentExponent l z₀ p < -1) :
    ∃ r > (0 : ℝ), ∀ᵐ u ∂uniformLaw,
      (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
        ∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
          TendstoUniformlyOn
            (fun k z ↦ Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
              (Model.initial n) (localSafeCutoff l u) k (ω k))
            (localAnalyticProfileLimit l n u ω) atTop (closedBall z₀ r) := by
  obtain ⟨η, hη, ρ, hρ, hwindow⟩ := exists_localProfile_complex_moment_disk hl hp hp2 hz he
  obtain ⟨R₀, hR₀, hcan⟩ := localProfile_ae_canonical_complex_analytic_limit hl hp hp2 hz he
  let r := min (ρ / 4) (R₀ / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrρ : r < ρ / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrR₀ : r < R₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hRρ : ρ / 2 < ρ := by linarith
  refine ⟨r, hr, ?_⟩
  filter_upwards [hcan l le_rfl,
    localProfile_ae_complex_window_moment_decay hl hp hp2 hη (hwindow l le_rfl)]
    with u hcanU hmU
  intro hs n
  obtain ⟨D, hD, hC, hm⟩ := hmU hs
  let J := localSafeCutoff l u
  have hCR : ∀ k ≥ J, ∀ z ∈ closedBall z₀ (ρ / 2),
      Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u)
        (Model.infectious (Model.initial n)) J k ≠ 0 := by
    intro k hk z hz'
    simpa only [Model.infectious_initial] using hC z (hz'.trans_lt hRρ) k hk
  have hCr : ∀ k ≥ J, ∀ z ∈ closedBall z₀ r,
      Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u)
        (Model.infectious (Model.initial n)) J k ≠ 0 :=
    fun k hk z hz' ↦ hCR k hk z (closedBall_subset_closedBall hrρ.le hz')
  have hpos : ∀ i, 0 < Model.prescribedWalk (localBirth l u)
      (Model.infectious (Model.initial n)) i := by
    intro i
    simp only [Model.infectious_initial]
    apply prescribedWalk_local_pos (H := i) _ le_rfl
    intro j _
    exact_mod_cast hs j
  have hfull := Model.prescribedTrajectory_ae_full_time_of_dyadic
    (localBirth l u) (Model.initial n) J z₀ r (ρ / 2) hr.le hrρ hCr hCR hpos p hp.le D η hD
    (fun z hz' j N hJj hj hjN ↦ hm n z
      (by rw [mem_sphere] at hz'; rw [hz']; exact hRρ) j N hJj hj hjN)
  filter_upwards [(hcanU hs n).1, hfull] with ω hω hωfull
  have huni := (hω r hr.le hrR₀).1
  have hcont : ContinuousOn (localAnalyticProfileLimit l n u ω) (closedBall z₀ r) := by
    apply huni.continuousOn
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro m
    exact (Model.differentiableOn_prescribedNormalizedProfile_exp (localBirth l u)
      (Model.initial n) (ω (J + 2 ^ m)) J (J + 2 ^ m)
      (hCr (J + 2 ^ m) (Nat.le_add_right _ _))).continuousOn
  let L : C(↥(closedBall z₀ r), ℂ) :=
    ⟨fun z ↦ localAnalyticProfileLimit l n u ω z,
      continuousOn_iff_continuous_domRestrict.mp hcont⟩
  let G := Model.continuousPrescribedProfile (localBirth l u) (Model.initial n) J z₀ r hCr
  have hsub : Tendsto (fun m ↦ G (J + 2 ^ m) (ω (J + 2 ^ m))) atTop (𝓝 L) := by
    apply (Model.continuousMap_tendsto_iff_uniformlyOn _ _).mpr
    rw [tendstoUniformlyOn_univ]
    exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp huni
  have ht := hωfull L hsub
  have hphysical : Tendsto (fun k ↦ G k (ω k)) atTop (𝓝 L) :=
    (tendsto_add_atTop_iff_nat J).mp (by simpa only [Nat.add_comm] using ht)
  have hu := (Model.continuousMap_tendsto_iff_uniformlyOn _ _).mp hphysical
  rw [tendstoUniformlyOn_univ] at hu
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hu

/-- The complete source assertion, with one parent-trajectory null set for
all tilts in the fixed compact and the entire physical time sequence. -/
theorem localProfile_ae_canonical_complex_compact_limit_ae_physical
    {l : ℝ} (hl : 1 < l) {K : Set ℂ}
    (hK : IsCompact K) (hKd : K ⊆ complexProfileMomentDomain l) :
    ∀ᵐ u ∂uniformLaw,
      (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
        ∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
          TendstoUniformlyOn
            (fun k z ↦ Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
              (Model.initial n) (localSafeCutoff l u) k (ω k))
            (localAnalyticProfileLimit l n u ω) atTop K := by
  classical
  have hpoint (x : K) : ∃ R > (0 : ℝ), ∀ᵐ u ∂uniformLaw,
      (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
        ∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
          TendstoUniformlyOn
            (fun k z ↦ Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
              (Model.initial n) (localSafeCutoff l u) k (ω k))
            (localAnalyticProfileLimit l n u ω) atTop (closedBall (x : ℂ) R) := by
    obtain ⟨hx, p, hp, hp2, he⟩ := hKd x.property
    exact localProfile_ae_canonical_complex_disk_limit_ae hl hp hp2 hx he
  choose R hR hlocal using hpoint
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K ↦ ball (x : ℂ) (R x / 2)) (fun _ ↦ isOpen_ball)
    (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩,
      mem_ball_self (div_pos (hR ⟨x, hx⟩) (by norm_num))⟩)
  have hAE := (ae_ball_iff s.countable_toSet).mpr (fun x (_ : x ∈ s) ↦ hlocal x)
  filter_upwards [hAE] with u hu
  intro hsurv n
  have hinner := (ae_ball_iff s.countable_toSet).mpr
    (fun x (hx : x ∈ s) ↦ hu x hx hsurv n)
  filter_upwards [hinner] with ω hω
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have ht : ∀ x ∈ s, ∀ᶠ k : ℕ in atTop, ∀ z ∈ closedBall (x : ℂ) (R x),
      dist (localAnalyticProfileLimit l n u ω z)
        (Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
          (Model.initial n) (localSafeCutoff l u) k (ω k)) < ε :=
    fun x hx ↦ Metric.tendstoUniformlyOn_iff.mp (hω x hx) ε hε
  have htall : ∀ᶠ k : ℕ in atTop, ∀ x ∈ s, ∀ z ∈ closedBall (x : ℂ) (R x),
      dist (localAnalyticProfileLimit l n u ω z)
        (Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
          (Model.initial n) (localSafeCutoff l u) k (ω k)) < ε := by
    exact (Filter.eventually_all_finset s).mpr ht
  filter_upwards [htall] with k hk
  intro z hz
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hs hz)
  obtain ⟨hx, hzx⟩ := mem_iUnion.mp hx
  exact hk x hx z (closedBall_subset_closedBall
    (by linarith [hR x] : R x / 2 ≤ R x) (ball_subset_closedBall hzx))

end HeightPaper.CountCoupling
