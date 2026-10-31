module

public import HeightPaper.Probability.LocalProfileMoments
public import HeightPaper.Model.CanonicalAnalyticProfile

/-!
# Analytic local profiles under the actual iid count-word law

The count-word moment estimates supply all inputs of the analytic trajectory
limit. The surrounding disk is deterministic and common to every parameter
above the prescribed lower bound.
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology BigOperators

namespace HeightPaper.CountCoupling

noncomputable def localAnalyticProfileLimit (l : ℝ) (n : ℕ) (u : ℕ → ℝ)
    (ω : ℕ → Model.State) (z : ℂ) : ℂ :=
  Model.prescribedAnalyticProfileLimit (localBirth l u) (Model.initial n)
    (localSafeCutoff l u) ω z

/-- Joint measurability in the count word and the tree trajectory, with the
paper's random cutoff included in the explicit canonical limit. -/
theorem measurable_localAnalyticProfileLimit_joint (l : ℝ) (n : ℕ) (z : ℂ) :
    Measurable (fun q : (ℕ → ℝ) × (ℕ → Model.State) =>
      localAnalyticProfileLimit l n q.1 q.2 z) := by
  have he : Measurable (fun q : (ℕ → ℝ) × (ℕ → Model.State) => localBirth l q.1) :=
    Measurable.of_eval (fun i => (measurable_localBirth l i).comp measurable_fst)
  have hm : Measurable (fun q : (ℕ → ℝ) × (ℕ → Model.State) =>
      ((localBirth l q.1, q.2), localSafeCutoff l q.1)) :=
    (he.prodMk measurable_snd).prodMk ((measurable_localSafeCutoff l).comp measurable_fst)
  simpa only [localAnalyticProfileLimit, Function.comp_def] using
    (Model.measurable_prescribedAnalyticProfileLimit_joint_cutoff (Model.initial n) z).comp hm

/-- On local survival, almost every iid count word admits a common analytic
profile limit for its actual parent-draw law. The full sequence converges
uniformly in probability on every smaller disk. -/
theorem localProfile_ae_analytic_limit {l₀ x : ℝ} (hl₀ : 1 < l₀)
    (hx : 0 < x) (hxr : x < profileRoot l₀) :
    ∃ R > (0 : ℝ), ∀ l ≥ l₀, ∀ᵐ u ∂uniformLaw,
      (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
        ∃ L : (ℕ → Model.State) → ℂ → ℂ,
          (∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
            ∀ r : ℝ, 0 ≤ r → r < R →
              TendstoUniformlyOn
                (fun m z => Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                  (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + 2 ^ m)
                  (ω (localSafeCutoff l u + 2 ^ m)))
                (L ω) atTop (closedBall (x : ℂ) r) ∧
              DifferentiableOn ℂ (L ω) (ball (x : ℂ) r)) ∧
          ∀ r : ℝ, 0 ≤ r → r < R → ∀ ε > (0 : ℝ),
            Tendsto (fun k =>
              (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)).real
                {ω | ∃ z ∈ closedBall (x : ℂ) r,
                  ε < ‖L ω z - Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                    (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
                    (ω (localSafeCutoff l u + k))‖}) atTop (𝓝 0) := by
  obtain ⟨p, hp, η, hη, r₀, hr₀, hword⟩ :=
    localProfile_uniform_near_real_moment_decay hl₀ hx hxr
  refine ⟨r₀ / 2, by positivity, ?_⟩
  intro l hl
  filter_upwards [hword l hl] with u hu
  intro hs n
  obtain ⟨D, hD, hC, hm⟩ := hu hs
  have hC' : ∀ k ≥ localSafeCutoff l u, ∀ z ∈ closedBall (x : ℂ) (r₀ / 2),
      Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u)
        (Model.infectious (Model.initial n)) (localSafeCutoff l u) k ≠ 0 := by
    intro k hk z hz
    simpa only [Model.infectious_initial] using
      hC z (lt_of_le_of_lt hz (by linarith : r₀ / 2 < r₀)) k hk
  apply Model.prescribedTrajectory_exists_analytic_limit_in_probability_of_moment_decay
    (localBirth l u) (Model.initial n) (localSafeCutoff l u) (x : ℂ)
    (show 0 < r₀ / 2 by positivity) hC' hp.1.le hD hη
  intro j k hJj hj hjk z hz
  exact hm n z (by rw [mem_sphere] at hz; rw [hz]; linarith) j k hJj hj hjk

/-- The same convergence uses the explicit jointly measurable limit above. -/
theorem localProfile_ae_canonical_analytic_limit {l₀ x : ℝ} (hl₀ : 1 < l₀)
    (hx : 0 < x) (hxr : x < profileRoot l₀) :
    ∃ R > (0 : ℝ), ∀ l ≥ l₀, ∀ᵐ u ∂uniformLaw,
      (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
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
                  ε < ‖localAnalyticProfileLimit l n u ω z - Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                    (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + k)
                    (ω (localSafeCutoff l u + k))‖}) atTop (𝓝 0) := by
  obtain ⟨p, hp, η, hη, r₀, hr₀, hword⟩ :=
    localProfile_uniform_near_real_moment_decay hl₀ hx hxr
  refine ⟨r₀ / 2, by positivity, ?_⟩
  intro l hl
  filter_upwards [hword l hl] with u hu
  intro hs n
  obtain ⟨D, hD, hC, hm⟩ := hu hs
  have hC' : ∀ k ≥ localSafeCutoff l u, ∀ z ∈ closedBall (x : ℂ) (r₀ / 2),
      Model.prescribedNormalizerFrom (Complex.exp z) (localBirth l u)
        (Model.infectious (Model.initial n)) (localSafeCutoff l u) k ≠ 0 := by
    intro k hk z hz
    simpa only [Model.infectious_initial] using
      hC z (lt_of_le_of_lt hz (by linarith : r₀ / 2 < r₀)) k hk
  apply Model.prescribedTrajectory_canonical_analytic_limit_in_probability_of_moment_decay
    (localBirth l u) (Model.initial n) (localSafeCutoff l u) (x : ℂ)
    (show 0 < r₀ / 2 by positivity) hC' hp.1.le hD hη
  intro j k hJj hj hjk z hz
  exact hm n z (by rw [mem_sphere] at hz; rw [hz]; linarith) j k hJj hj hjk

end HeightPaper.CountCoupling
