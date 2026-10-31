module

public import HeightPaper.Probability.LocalProfileGeneralComplexBounds
public import HeightPaper.Probability.LocalAnalyticProfile

/-!
# Analytic profile limits on the full complex moment domain

The conditional moment window no longer requires a positive real center.
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology BigOperators

namespace HeightPaper.CountCoupling

/-- A strict complex moment point has one canonical analytic limit on a
deterministic disk, with full-time locally uniform convergence in conditional
probability. The disk also works at larger epidemic parameters. -/
theorem localProfile_ae_canonical_complex_analytic_limit
    {l₀ p : ℝ} {z₀ : ℂ} (hl₀ : 1 < l₀)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (hz : z₀.re < profileRoot l₀)
    (he : complexProfileMomentExponent l₀ z₀ p < -1) :
    ∃ R > (0 : ℝ), ∀ l ≥ l₀, ∀ᵐ u ∂uniformLaw,
      (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
        (∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
            ∀ r : ℝ, 0 ≤ r → r < R →
              TendstoUniformlyOn
                (fun m z => Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                  (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + 2 ^ m)
                  (ω (localSafeCutoff l u + 2 ^ m)))
                (localAnalyticProfileLimit l n u ω) atTop (closedBall z₀ r) ∧
              DifferentiableOn ℂ (localAnalyticProfileLimit l n u ω) (ball z₀ r)) ∧
          ∀ r : ℝ, 0 ≤ r → r < R → ∀ ε > (0 : ℝ),
            Tendsto (fun k =>
              (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)).real
                {ω | ∃ z ∈ closedBall z₀ r,
                  ε < ‖localAnalyticProfileLimit l n u ω z -
                    Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                    (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
                    (ω (localSafeCutoff l u + k))‖}) atTop (𝓝 0) := by
  obtain ⟨η, hη, ρ, hρ, hwindow⟩ :=
    exists_localProfile_complex_moment_disk hl₀ hp hp2 hz he
  refine ⟨ρ / 2, by positivity, ?_⟩
  intro l hl
  have hl1 := hl₀.trans_le hl
  have hwindow' : ∀ z : ℂ, dist z z₀ < ρ →
      z.re < profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η :=
    fun z hz' ↦ hwindow l hl z hz'
  filter_upwards [localProfile_ae_complex_window_moment_decay hl1 hp hp2 hη hwindow']
    with u hu
  intro hs n
  obtain ⟨D, hD, hC, hm⟩ := hu hs
  have hC' : ∀ k ≥ localSafeCutoff l u, ∀ z ∈ closedBall z₀ (ρ / 2),
      Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u)
        (Model.infectious (Model.initial n)) (localSafeCutoff l u) k ≠ 0 := by
    intro k hk z hz'
    simpa only [Model.infectious_initial] using
      hC z (lt_of_le_of_lt hz' (by linarith : ρ / 2 < ρ)) k hk
  apply Model.prescribedTrajectory_canonical_analytic_limit_in_probability_of_moment_decay
    (localBirth l u) (Model.initial n) (localSafeCutoff l u) z₀
    (show 0 < ρ / 2 by positivity) hC' hp.le hD hη
  intro j k hJj hj hjk z hz'
  exact hm n z (by rw [mem_sphere] at hz'; rw [hz']; linarith) j k hJj hj hjk

/-- The union of all strict complex moment windows at a fixed epidemic
parameter. This is the paper's domain `𝒱` in explicit Lean notation. -/
def complexProfileMomentDomain (l : ℝ) : Set ℂ :=
  {z | z.re < profileRoot l ∧ ∃ p : ℝ,
    1 < p ∧ p ≤ 2 ∧ complexProfileMomentExponent l z p < -1}

/-- For each fixed compact subset of the full complex moment domain, the
canonical limit is attained uniformly in conditional probability. -/
theorem localProfile_ae_canonical_complex_compact_limit
    {l : ℝ} (hl : 1 < l) {K : Set ℂ}
    (hK : IsCompact K) (hKd : K ⊆ complexProfileMomentDomain l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
      ∀ n : ℕ, ∀ ε > (0 : ℝ),
        Tendsto (fun k =>
          (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)).real
            {ω | ∃ z ∈ K,
              ε < ‖localAnalyticProfileLimit l n u ω z -
                Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                  (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
                  (ω (localSafeCutoff l u + k))‖}) atTop (𝓝 0) := by
  classical
  have hpoint (x : K) :
      ∃ R > (0 : ℝ), ∀ᵐ u ∂uniformLaw,
        (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
          ∀ r : ℝ, 0 ≤ r → r < R → ∀ ε > (0 : ℝ),
            Tendsto (fun k =>
              (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)).real
                {ω | ∃ z ∈ closedBall (x : ℂ) r,
                  ε < ‖localAnalyticProfileLimit l n u ω z -
                    Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                      (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
                      (ω (localSafeCutoff l u + k))‖}) atTop (𝓝 0) := by
    obtain ⟨hz, p, hp, hp2, he⟩ := hKd x.property
    obtain ⟨R, hR, hlocal⟩ :=
      localProfile_ae_canonical_complex_analytic_limit hl hp hp2 hz he
    refine ⟨R, hR, ?_⟩
    filter_upwards [hlocal l le_rfl] with u hu
    intro hs n r hr hrR ε hε
    exact (hu hs n).2 r hr hrR ε hε
  choose R hR hlocal using hpoint
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => ball (x : ℂ) (R x / 2)) (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩,
      mem_ball_self (div_pos (hR ⟨x, hx⟩) (by norm_num))⟩)
  have hAE : ∀ᵐ u ∂uniformLaw, ∀ x ∈ s,
      (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
        ∀ r : ℝ, 0 ≤ r → r < R x → ∀ ε > (0 : ℝ),
          Tendsto (fun k =>
            (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)).real
              {ω | ∃ z ∈ closedBall (x : ℂ) r,
                ε < ‖localAnalyticProfileLimit l n u ω z -
                  Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                    (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
                    (ω (localSafeCutoff l u + k))‖}) atTop (𝓝 0) :=
    (ae_ball_iff s.countable_toSet).mpr (fun x _ => hlocal x)
  filter_upwards [hAE] with u hu
  intro hsurv n ε hε
  let μ := Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)
  let E : K → ℕ → Set (ℕ → Model.State) := fun x k =>
    {ω | ∃ z ∈ closedBall (x : ℂ) (R x / 2),
      ε < ‖localAnalyticProfileLimit l n u ω z -
        Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
          (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
          (ω (localSafeCutoff l u + k))‖}
  have htail (x : K) (hx : x ∈ s) :
      Tendsto (fun k => μ.real (E x k)) atTop (𝓝 0) := by
    exact hu x hx hsurv n (R x / 2) (by positivity [hR x])
      (by linarith [hR x]) ε hε
  have hsum : Tendsto (fun k => ∑ x ∈ s, μ.real (E x k)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum s htail
  have hbound (k : ℕ) :
      μ.real {ω | ∃ z ∈ K,
        ε < ‖localAnalyticProfileLimit l n u ω z -
          Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
            (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
            (ω (localSafeCutoff l u + k))‖} ≤
        ∑ x ∈ s, μ.real (E x k) := by
    apply (measureReal_mono (μ := μ) ?_ (measure_ne_top _ _)).trans
      (measureReal_biUnion_finset_le s (fun x => E x k))
    rintro ω ⟨z, hz, hbad⟩
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hs hz)
    obtain ⟨hx, hzx⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx,
      ⟨z, ball_subset_closedBall hzx, hbad⟩⟩⟩
  have hzero (k : ℕ) : 0 ≤ μ.real {ω | ∃ z ∈ K,
      ε < ‖localAnalyticProfileLimit l n u ω z -
        Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
          (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
          (ω (localSafeCutoff l u + k))‖} := measureReal_nonneg
  exact squeeze_zero' (Filter.Eventually.of_forall hzero)
    (Filter.Eventually.of_forall hbound) hsum

/-- The compact convergence above uses the physical event index of the
paper; deleting the finite random cutoff does not change its limit. -/
theorem localProfile_ae_canonical_complex_compact_limit_physical
    {l : ℝ} (hl : 1 < l) {K : Set ℂ}
    (hK : IsCompact K) (hKd : K ⊆ complexProfileMomentDomain l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
      ∀ n : ℕ, ∀ ε > (0 : ℝ),
        Tendsto (fun k =>
          (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)).real
            {ω | ∃ z ∈ K,
              ε < ‖localAnalyticProfileLimit l n u ω z -
                Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                  (Model.initial n) (localSafeCutoff l u) k (ω k)‖}) atTop (𝓝 0) := by
  filter_upwards [localProfile_ae_canonical_complex_compact_limit hl hK hKd]
    with u hu
  intro hs n ε hε
  have hshift := hu hs n ε hε
  apply (tendsto_add_atTop_iff_nat (localSafeCutoff l u)).mp
  simpa only [Nat.add_comm] using hshift

end HeightPaper.CountCoupling
