module

public import HeightPaper.Probability.LocalProfileGeneralComplexLimitTightness
public import HeightPaper.Probability.LocalProfileGeneralComplexCompactLp

/-!
# Common-order conditional profile convergence on compact complex domains
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology ENNReal BigOperators

namespace HeightPaper.CountCoupling

/-- An outer bad-moment event, including the paper's survival and cutoff
indicators. -/
def localComplexCompactLpBad (l q : ℝ) (K : Set ℂ) (j : ℕ) (ε : ℝ) :
    Set (ℕ → ℝ) :=
  {u | (∀ i, 0 < (localWalk l u i : ℝ)) ∧ localSafeCutoff l u ≤ j ∧
    ∃ n : ℕ, ∃ z ∈ K,
      ε < (∫ ω, ‖localAnalyticProfileLimit l n u ω z -
        Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
          (Model.initial n) (localSafeCutoff l u) j (ω j)‖ ^ q
        ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n))}

/-- The paper's common-moment compact convergence, with the probability
of a bad conditional moment tending to zero uniformly over every parameter
above the lower endpoint. -/
theorem localComplexCompactLpBad_uniform_tendsto
    {l₀ : ℝ} (hl₀ : 1 < l₀) {K : Set ℂ}
    (hK : IsCompact K) (hKd : K ⊆ complexProfileMomentDomain l₀) :
    ∃ q : ℝ, 1 < q ∧ q ≤ 2 ∧
      ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ), ∃ A : ℕ,
        ∀ l ≥ l₀, ∀ j ≥ A,
          uniformLaw.real (localComplexCompactLpBad l q K j ε) < δ := by
  classical
  by_cases hKne : K.Nonempty
  swap
  · refine ⟨2, by norm_num, le_rfl, ?_⟩
    intro ε hε δ hδ
    refine ⟨0, ?_⟩
    intro l hl j hj
    have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    simp [localComplexCompactLpBad, hKe, hδ]
  have hpoint (x : K) :
      ∃ p : ℝ, 1 < p ∧ p ≤ 2 ∧
        ∃ η : ℝ, 0 < η ∧ ∃ r : ℝ, 0 < r ∧
          ∀ δ > (0 : ℝ), ∃ D : ℝ, 0 ≤ D ∧ ∀ l ≥ l₀,
            uniformLaw.real (localComplexMomentBad p η (2 * r) (x : ℂ) D l) ≤ δ ∧
            (∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
              u ∉ localComplexMomentBad p η (2 * r) (x : ℂ) D l →
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
                    D * (j : ℝ) ^ (-η)) := by
    obtain ⟨hz, p, hp, hp2, he⟩ := hKd x.property
    obtain ⟨η, hη, r, hr, hresult⟩ :=
      localComplexLimitMomentBad_uniform_tight hl₀ hp hp2 hz he
    exact ⟨p, hp, hp2, η, hη, r, hr, hresult⟩
  choose p hp hp2 η hη r hr hresult using hpoint
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
  intro ε hε δ hδ
  have hδ0 : 0 < δ / ((s.card : ℝ) + 1) := by positivity
  choose D hD hDtight hgood using fun x : K => hresult x
    (δ / ((s.card : ℝ) + 1)) hδ0
  let C : s → ℕ → ℝ := fun x j =>
    (D x.1 * (j : ℝ) ^ (-η x.1)) ^ (q / p x.1)
  have hCnonneg (x : s) (j : ℕ) : 0 ≤ C x j := by
    dsimp [C]
    exact Real.rpow_nonneg
      (mul_nonneg (hD x.1) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) _
  have hCt (x : s) : Tendsto (fun j => C x j) atTop (𝓝 0) := by
    have hbase : Tendsto (fun j : ℕ => D x.1 * (j : ℝ) ^ (-η x.1)) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using
        (((tendsto_rpow_neg_atTop (hη x.1)).comp tendsto_natCast_atTop_atTop).const_mul (D x.1))
    have hpow := hbase.rpow_const_nhds_zero
      (div_pos (zero_lt_one.trans hq) (zero_lt_one.trans (hp x.1)))
    simpa only [C] using hpow
  have hsum : Tendsto (fun j => ∑ x ∈ s.attach, C x j) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum s.attach (fun x _ => hCt x)
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp (hsum.eventually (Iio_mem_nhds hε))
  let A := max A₀ 1
  refine ⟨A, ?_⟩
  intro l hl j hj
  have hl1 := hl₀.trans_le hl
  have hj1 : 1 ≤ j := (le_max_right A₀ 1).trans hj
  have hsumj : ∑ x ∈ s.attach, C x j < ε :=
    hA₀ j ((le_max_left A₀ 1).trans hj)
  let Bad : K → Set (ℕ → ℝ) := fun x =>
    localComplexMomentBad (p x) (η x) (2 * r x) (x : ℂ) (D x) l
  have hAE : ∀ᵐ u ∂uniformLaw, ∀ x ∈ s,
      (∀ i, 0 < (localWalk l u i : ℝ)) → u ∉ Bad x →
        ∀ n : ℕ, ∀ z ∈ closedBall (x : ℂ) (r x), ∀ k : ℕ,
          localSafeCutoff l u ≤ k → 1 ≤ k →
          Integrable (fun ω ↦ ‖localAnalyticProfileLimit l n u ω z -
            Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
              (Model.initial n) (localSafeCutoff l u) k (ω k)‖ ^ p x)
            (Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ∧
          (∫ ω, ‖localAnalyticProfileLimit l n u ω z -
            Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l u)
              (Model.initial n) (localSafeCutoff l u) k (ω k)‖ ^ p x
            ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n)) ≤
              D x * (k : ℝ) ^ (-η x) :=
    (ae_ball_iff s.countable_toSet).mpr (fun x _ => hgood x l hl)
  have hsub : ∀ᵐ u ∂uniformLaw,
      u ∈ localComplexCompactLpBad l q K j ε → u ∈ ⋃ x ∈ s, Bad x := by
    filter_upwards [hAE] with u hu
    rintro ⟨hsurv, hJj, n, z, hz, hbad⟩
    by_contra hnot
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hs hz)
    obtain ⟨hx, hzx⟩ := mem_iUnion.mp hx
    have hnotx : u ∉ Bad x := by
      intro hh
      exact hnot (mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, hh⟩⟩)
    have hhigh := hu x hx hsurv hnotx n z (ball_subset_closedBall hzx) j hJj hj1
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
    have hlow := integral_norm_rpow_le_high_moment μ f hf
      (zero_lt_one.trans hq) (hqp x hx) hhigh.1
    have hpow := Real.rpow_le_rpow
      (integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg (f ω)) _))
      hhigh.2 (div_nonneg (zero_lt_one.trans hq).le
        (zero_lt_one.trans (hp x)).le)
    have hsingle : (∫ ω, ‖f ω‖ ^ q ∂μ) ≤ C ⟨x, hx⟩ j := hlow.trans hpow
    have hsumle : C ⟨x, hx⟩ j ≤ ∑ y ∈ s.attach, C y j :=
      Finset.single_le_sum (fun y _ => hCnonneg y j) (Finset.mem_attach s ⟨x, hx⟩)
    exact not_lt_of_ge ((hsingle.trans hsumle).trans hsumj.le) hbad
  have hmeasure := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hunion := measureReal_biUnion_finset_le (μ := uniformLaw) s Bad
  have hsumBad : (∑ x ∈ s, uniformLaw.real (Bad x)) ≤
      (s.card : ℝ) * (δ / ((s.card : ℝ) + 1)) := by
    calc
      _ ≤ ∑ _x ∈ s, δ / ((s.card : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro x hx
        exact (hDtight x l hl)
      _ = _ := by simp
  have hnum : (s.card : ℝ) * (δ / ((s.card : ℝ) + 1)) < δ := by
    have heq : (δ / ((s.card : ℝ) + 1)) * ((s.card : ℝ) + 1) = δ :=
      div_mul_cancel₀ δ (by positivity)
    nlinarith
  exact hmeasure.trans_lt ((hunion.trans hsumBad).trans_lt hnum)

end HeightPaper.CountCoupling
