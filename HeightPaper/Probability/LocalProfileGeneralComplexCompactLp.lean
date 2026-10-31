module

public import HeightPaper.Probability.LocalProfileGeneralComplexLp

/-!
# One moment order on each compact complex profile domain
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology ENNReal BigOperators

namespace HeightPaper.CountCoupling

/-- The paper's compact complex domain admits one moment order, chosen before
the count word, for conditional convergence to the canonical analytic limit.
The parameter is fixed here; parameter-uniform tightness is a separate step. -/
theorem localProfile_ae_complex_compact_uniform_lp
    {l : ℝ} (hl : 1 < l) {K : Set ℂ}
    (hK : IsCompact K) (hKd : K ⊆ complexProfileMomentDomain l) :
    ∃ q : ℝ, 1 < q ∧ q ≤ 2 ∧
      ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
        ∀ ε > (0 : ℝ), ∀ᶠ j : ℕ in atTop,
          ∀ n : ℕ, ∀ z ∈ K,
            (∫ ω, ‖localAnalyticProfileLimit l n u ω z -
              Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ q
              ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤ ε := by
  classical
  by_cases hKne : K.Nonempty
  swap
  · refine ⟨2, by norm_num, le_rfl, ae_of_all _ (fun u _ ε hε => ?_)⟩
    have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    exact Filter.Eventually.of_forall (fun _ _ z hz => False.elim (by simpa [hKe] using hz))
  have hpoint (x : K) :
      ∃ p : ℝ, 1 < p ∧ p ≤ 2 ∧
        ∃ η : ℝ, 0 < η ∧ ∃ r : ℝ, 0 < r ∧
          ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
            ∃ D : ℝ, 0 ≤ D ∧
              ∀ n : ℕ, ∀ z ∈ closedBall (x : ℂ) r, ∀ j : ℕ,
                localSafeCutoff l u ≤ j → 1 ≤ j →
                Integrable (fun ω ↦ ‖localAnalyticProfileLimit l n u ω z -
                  Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                    (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p)
                  (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
                (∫ ω, ‖localAnalyticProfileLimit l n u ω z -
                  Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                    (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p
                  ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤
                    D * (j : ℝ) ^ (-η) := by
    obtain ⟨hz, p, hp, hp2, he⟩ := hKd x.property
    obtain ⟨η, hη, r, hr, hword⟩ :=
      localProfile_ae_complex_disk_limit_moment_tail hl hp hp2 hz he
    exact ⟨p, hp, hp2, η, hη, r, hr, hword⟩
  choose p hp hp2 η hη r hr hword using hpoint
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => ball (x : ℂ) (r x)) (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hy, _⟩ := mem_iUnion.mp hy
    exact ⟨y, hy⟩
  let q := s.inf' hsne p
  have hq : 1 < q := (Finset.lt_inf'_iff hsne).mpr (fun x _ => hp x)
  have hq2 : q ≤ 2 := (Finset.inf'_le _ hsne.choose_spec).trans (hp2 hsne.choose)
  have hqp (x : K) (hx : x ∈ s) : q ≤ p x := Finset.inf'_le _ hx
  refine ⟨q, hq, hq2, ?_⟩
  have hAE : ∀ᵐ u ∂uniformLaw, ∀ x ∈ s,
      (∀ i, 0 < (localWalk l u i : ℝ)) →
        ∃ D : ℝ, 0 ≤ D ∧
          ∀ n : ℕ, ∀ z ∈ closedBall (x : ℂ) (r x), ∀ j : ℕ,
            localSafeCutoff l u ≤ j → 1 ≤ j →
            Integrable (fun ω ↦ ‖localAnalyticProfileLimit l n u ω z -
              Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p x)
              (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
            (∫ ω, ‖localAnalyticProfileLimit l n u ω z -
              Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
                (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ p x
              ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤
                D * (j : ℝ) ^ (-η x) :=
    (ae_ball_iff s.countable_toSet).mpr (fun x _ => hword x)
  filter_upwards [hAE] with u hu
  intro hsurv
  choose D hD htail using fun x : s => hu x.1 x.2 hsurv
  let C : s → ℕ → ℝ := fun x j =>
    (D x * (j : ℝ) ^ (-η x.1)) ^ (q / p x.1)
  have hCnonneg (x : s) (j : ℕ) : 0 ≤ C x j := by
    dsimp [C]
    exact Real.rpow_nonneg
      (mul_nonneg (hD x) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) _
  have hCt (x : s) : Tendsto (fun j => C x j) atTop (𝓝 0) := by
    have hbase : Tendsto (fun j : ℕ => D x * (j : ℝ) ^ (-η x.1)) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using
        (((tendsto_rpow_neg_atTop (hη x.1)).comp tendsto_natCast_atTop_atTop).const_mul (D x))
    have hpow := hbase.rpow_const_nhds_zero
      (div_pos (zero_lt_one.trans hq) (zero_lt_one.trans (hp x.1)))
    simpa only [C] using hpow
  have hsum : Tendsto (fun j => ∑ x ∈ s.attach, C x j) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum s.attach (fun x _ => hCt x)
  intro ε hε
  filter_upwards [eventually_ge_atTop (localSafeCutoff l u), eventually_ge_atTop 1,
    hsum.eventually (Iio_mem_nhds hε)] with j hJj hj hsmall
  intro n z hz
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hs hz)
  obtain ⟨hx, hzx⟩ := mem_iUnion.mp hx
  let f : (ℕ → Model.State) → ℂ := fun ω =>
    localAnalyticProfileLimit l n u ω z -
      Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
        (Model.initial n) (localSafeCutoff l u) j (ω j)
  let μ := Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)
  have hf : AEStronglyMeasurable f μ := by
    have hg := Model.measurable_prescribedAnalyticProfileLimit_eval
      (localBirth l u) (Model.initial n) (localSafeCutoff l u) z
    have hh := (Model.measurable_state
      (Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
        (Model.initial n) (localSafeCutoff l u) j)).comp
      (measurable_pi_apply (X := fun _ : ℕ => Model.State) j)
    exact (hg.sub hh).aestronglyMeasurable
  have hhigh := htail ⟨x, hx⟩ n z (ball_subset_closedBall hzx) j hJj hj
  have hlow := integral_norm_rpow_le_high_moment μ f hf
    (zero_lt_one.trans hq) (hqp x hx) hhigh.1
  have hpow := Real.rpow_le_rpow
    (integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg (f ω)) _))
    hhigh.2 (div_nonneg (zero_lt_one.trans hq).le
      (zero_lt_one.trans (hp x)).le)
  have hsingle : (∫ ω, ‖f ω‖ ^ q ∂μ) ≤ C ⟨x, hx⟩ j := hlow.trans hpow
  have hsumle : C ⟨x, hx⟩ j ≤ ∑ y ∈ s.attach, C y j :=
    Finset.single_le_sum (fun y _ => hCnonneg y j) (Finset.mem_attach s ⟨x, hx⟩)
  exact (hsingle.trans hsumle).trans hsmall.le

end HeightPaper.CountCoupling
