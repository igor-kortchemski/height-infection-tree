module

public import HeightPaper.Model.LateRecoveryEndpoint
public import HeightPaper.Model.OutgrowthSamplePath

/-!
# Conditional late-recovery control from good cutoff states

The endpoint representation lets the path-level recovery-control estimate be
disintegrated over the cutoff state.  A vanishing averaged error can then be
converted to a set of cutoff states with uniformly vanishing conditional error.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal Classical

namespace HeightPaper.Model

noncomputable def lateRecoveryConditionalFailure (rate : ℝ≥0) (l η : ℝ) (K : ℕ)
    (s : State) : ℝ :=
  (continuationLaw rate s K).toMeasure.real
    {t | ¬ lateRecoveryEndpoints rate l η s t}

/-- The complete-path failure probability restricted to source survival is
the cutoff-state average of the genuine conditional continuation failure. -/
theorem sourceSurvival_lateRecovery_failure_eq_cutoff_integral
    (rate : ℝ≥0) {l δ η : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    (pathMeasure rate n (2 * n + 1)).real
      {p | p.last ∈ sourceSurvivalEvent l δ n ∧
        p ∉ lateRecoveryEvent rate l δ η n} =
      ∫ s, (sourceSurvivalEvent l δ n).indicator
        (lateRecoveryConditionalFailure rate l η
          (2 * n + 1 - sourceCutoff l δ n)) s
        ∂(evolve rate n (sourceCutoff l δ n)).toMeasure := by
  let H := sourceCutoff l δ n
  let N := 2 * n + 1
  let K := N - H
  let E : Set ContinuationSample :=
    {x | x.cutoff ∈ sourceSurvivalEvent l δ n ∧
      ¬ lateRecoveryEndpoints rate l η x.cutoff x.final}
  have hHN : H ≤ N := sourceCutoff_le_steps hl hδ n
  have hsum : sourceCutoff l δ n +
      (2 * n + 1 - sourceCutoff l δ n) = 2 * n + 1 := by omega
  have hsample := pathMeasure_continuationSample_event rate n H K E
  simp only [H, N, K] at hsample
  rw [hsum] at hsample
  have hsample' : (pathMeasure rate n N).real
      {p | (⟨p.eval H, p.last⟩ : ContinuationSample) ∈ E} =
      (continuationSampleLaw (evolve rate n H) rate K).toMeasure.real E := by
    simpa only [H, N, K] using hsample
  have hpath : (pathMeasure rate n N).real
      {p | p.last ∈ sourceSurvivalEvent l δ n ∧
        p ∉ lateRecoveryEvent rate l δ η n} =
      (pathMeasure rate n N).real
        {p | (⟨p.eval H, p.last⟩ : ContinuationSample) ∈ E} := by
    apply measureReal_congr
    filter_upwards [ae_supportedPath rate n N] with p hp
    apply propext
    have hs := sourceSurvivalEvent_iff_cutoffState hl hδ hp
    have hr := lateRecoveryEvent_iff_endpoints (η := η) hl hδ hp
    exact and_congr hs (not_congr hr)
  rw [hpath, hsample']
  have hcond := continuationSampleLaw_restricted_event
    (evolve rate n H) (evolve_support_finite rate n H) rate K
    (sourceSurvivalEvent l δ n)
    (fun s ↦ {t | ¬ lateRecoveryEndpoints rate l η s t})
  unfold lateRecoveryConditionalFailure
  simpa only [E, H, N, K, Set.mem_ofPred_eq] using hcond

/-- A square-root threshold turns a small mean nonnegative failure into a
large set of states with a uniform conditional failure bound. The small
positive summand keeps the threshold valid when the mean is zero. -/
theorem finitePMF_goodStates_badMass_le_sqrt
    (μ : PMF State) (hμ : μ.support.Finite) (A : Set State)
    (f : State → ℝ) (hf : ∀ s, 0 ≤ f s) (n : ℕ) :
    let e := ∫ s, A.indicator f s ∂μ.toMeasure
    let θ := Real.sqrt e + 1 / ((n + 1 : ℕ) : ℝ)
    μ.toMeasure.real (A \ {s | s ∈ A ∧ f s ≤ θ}) ≤ Real.sqrt e := by
  let e := ∫ s, A.indicator f s ∂μ.toMeasure
  let θ := Real.sqrt e + 1 / ((n + 1 : ℕ) : ℝ)
  let G : Set State := {s | s ∈ A ∧ f s ≤ θ}
  have hf' : ∀ s, 0 ≤ A.indicator f s := by
    intro s
    by_cases hs : s ∈ A
    · simpa only [Set.indicator_of_mem hs] using hf s
    · simp [Set.indicator, hs]
  have he0 : 0 ≤ e := integral_nonneg_of_ae (ae_of_all _ hf')
  have hθ : 0 < θ := by
    dsimp [θ]
    positivity
  have hsub : A \ G ⊆ {s | θ ≤ A.indicator f s} := by
    rintro s ⟨hs, hnot⟩
    have hlt : θ < f s := lt_of_not_ge (fun h ↦ hnot ⟨hs, h⟩)
    change θ ≤ A.indicator f s
    rw [Set.indicator_of_mem hs]
    exact hlt.le
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ.toMeasure) (ae_of_all _ hf')
    (FinitePMF.integrable_of_finite_support μ hμ _) θ
  have hmass : θ * μ.toMeasure.real (A \ G) ≤ e :=
    (mul_le_mul_of_nonneg_left
      (measureReal_mono hsub (measure_ne_top _ _)) hθ.le).trans hmarkov
  have heθ : e ≤ θ * Real.sqrt e := by
    have hsqrt := Real.sq_sqrt he0
    have hδ : 0 ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
    dsimp [θ]
    nlinarith [mul_nonneg (Real.sqrt_nonneg e) hδ]
  change μ.toMeasure.real (A \ G) ≤ Real.sqrt e
  exact le_of_mul_le_mul_left (hmass.trans heθ) hθ

noncomputable def lateRecoveryAverage (rates : ℕ → ℝ≥0)
    (l δ η : ℝ) (n : ℕ) : ℝ :=
  ∫ s, (sourceSurvivalEvent l δ n).indicator
    (lateRecoveryConditionalFailure (rates n) l η
      (2 * n + 1 - sourceCutoff l δ n)) s
    ∂(evolve (rates n) n (sourceCutoff l δ n)).toMeasure

noncomputable def lateRecoveryGoodThreshold (rates : ℕ → ℝ≥0)
    (l δ η : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (lateRecoveryAverage rates l δ η n) +
    1 / ((n + 1 : ℕ) : ℝ)

noncomputable def lateRecoveryGoodCutoffStates (rates : ℕ → ℝ≥0)
    (l δ η : ℝ) (n : ℕ) : Set State :=
  {s | s ∈ sourceSurvivalEvent l δ n ∧
    lateRecoveryConditionalFailure (rates n) l η
      (2 * n + 1 - sourceCutoff l δ n) s ≤
      lateRecoveryGoodThreshold rates l δ η n}

/-- The source survival mass can be read at the cutoff state itself. -/
theorem sourceCutoffState_survival_probability_tendsto
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦
      (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
        (sourceSurvivalEvent l δ n)) atTop (𝓝 (1 - 1 / l)) := by
  have hsource := sourceSurvivalEvent_probability_tendsto rates hl hδ hrates
  apply hsource.congr'
  apply Eventually.of_forall
  intro n
  let H := sourceCutoff l δ n
  let N := 2 * n + 1
  let S := sourceSurvivalEvent l δ n
  have hHN : H ≤ N := sourceCutoff_le_steps hl hδ n
  have hcut := pathMeasure_event_at (rates n) n N H hHN S
  have hterminal := pathMeasure_event_at (rates n) n N N le_rfl S
  have heq : (pathMeasure (rates n) n N).real {p | p.eval H ∈ S} =
      (pathMeasure (rates n) n N).real {p | p.last ∈ S} := by
    apply measureReal_congr
    filter_upwards [ae_supportedPath (rates n) n N] with p hp
    exact propext (sourceSurvivalEvent_iff_cutoffState hl hδ hp).symm
  calc
    (terminalStateMeasure (rates n) n).real S =
        (pathMeasure (rates n) n N).real {p | p.last ∈ S} := by
          simpa only [N, terminalStateMeasure, FinitePath.eval_last] using hterminal.symm
    _ = (pathMeasure (rates n) n N).real {p | p.eval H ∈ S} := heq.symm
    _ = (evolve (rates n) n H).toMeasure.real S := hcut

/-- On a good cutoff state, the genuine continuation event has probability
at least one minus the good-state threshold. -/
theorem lateRecoveryGoodCutoffState_success_lower_bound
    (rates : ℕ → ℝ≥0) (l δ η : ℝ) (n : ℕ)
    {s : State} (hs : s ∈ lateRecoveryGoodCutoffStates rates l δ η n) :
    1 - lateRecoveryGoodThreshold rates l δ η n ≤
      (continuationLaw (rates n) s
        (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
        {t | lateRecoveryEndpoints (rates n) l η s t} := by
  have hcompl : lateRecoveryConditionalFailure (rates n) l η
      (2 * n + 1 - sourceCutoff l δ n) s =
      1 - (continuationLaw (rates n) s
        (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
        {t | lateRecoveryEndpoints (rates n) l η s t} := by
    unfold lateRecoveryConditionalFailure
    rw [show {t | ¬ lateRecoveryEndpoints (rates n) l η s t} =
      {t | lateRecoveryEndpoints (rates n) l η s t}ᶜ from rfl,
      measureReal_compl (show MeasurableSet
        {t | lateRecoveryEndpoints (rates n) l η s t} from trivial),
      probReal_univ]
  linarith [hs.2]

/-- For all sufficiently small fixed cutoff fractions, the good-state
threshold tends to zero and the source-surviving cutoff states outside the
good set have vanishing probability. Every good state has conditional
late-recovery failure bounded by that same threshold. -/
theorem eventually_lateRecoveryGoodCutoffStates
    (rates : ℕ → ℝ≥0) {l η : ℝ} (hl : 1 < l)
    (hη : 0 < η) (hηm : η < offspringMean l)
    (hη1 : η < 1 - offspringMean l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      Tendsto (lateRecoveryGoodThreshold rates l δ η) atTop (𝓝 0) ∧
      Tendsto (fun n ↦
        (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
          (sourceSurvivalEvent l δ n \
            lateRecoveryGoodCutoffStates rates l δ η n)) atTop (𝓝 0) ∧
      ∀ n, ∀ s ∈ lateRecoveryGoodCutoffStates rates l δ η n,
        lateRecoveryConditionalFailure (rates n) l η
          (2 * n + 1 - sourceCutoff l δ n) s ≤
          lateRecoveryGoodThreshold rates l δ η n := by
  obtain ⟨δ₀, hδ₀, hbad⟩ := eventually_sourceSurvival_lateRecovery
    rates hl hη hηm hη1 hrates
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ
  have hδ1 : δ ∈ Ioo (0 : ℝ) 1 :=
    ⟨hδ.1, hδ.2.trans (hδ₀.2.trans (by norm_num))⟩
  have hmean : Tendsto (lateRecoveryAverage rates l δ η) atTop (𝓝 0) := by
    apply (hbad δ hδ).congr'
    apply Eventually.of_forall
    intro n
    simpa only [lateRecoveryAverage, FinitePath.eval_last] using
      sourceSurvival_lateRecovery_failure_eq_cutoff_integral
        (rates n) (η := η) hl hδ1 n
  have hsqrt : Tendsto (fun n ↦ Real.sqrt (lateRecoveryAverage rates l δ η n))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hmean
  have hθ : Tendsto (lateRecoveryGoodThreshold rates l δ η) atTop (𝓝 0) := by
    unfold lateRecoveryGoodThreshold
    simpa only [Nat.cast_add, Nat.cast_one, zero_add] using
      hsqrt.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨hθ, ?_, ?_⟩
  · apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsqrt
    apply Eventually.of_forall
    intro n
    let μ := evolve (rates n) n (sourceCutoff l δ n)
    let A := sourceSurvivalEvent l δ n
    let f := lateRecoveryConditionalFailure (rates n) l η
      (2 * n + 1 - sourceCutoff l δ n)
    have hb := finitePMF_goodStates_badMass_le_sqrt μ
      (evolve_support_finite (rates n) n (sourceCutoff l δ n)) A f
      (fun s ↦ measureReal_nonneg) n
    simpa only [μ, A, f, lateRecoveryAverage, lateRecoveryGoodCutoffStates,
      lateRecoveryGoodThreshold] using hb
  · intro n s hs
    exact hs.2

/-- Conditional on survival to the cutoff, asymptotically all cutoff states
have a uniformly vanishing late-recovery failure probability. The quotient
is the conditional probability of the good set under the cutoff-state law. -/
theorem eventually_lateRecoveryGoodCutoffStates_conditional
    (rates : ℕ → ℝ≥0) {l η : ℝ} (hl : 1 < l)
    (hη : 0 < η) (hηm : η < offspringMean l)
    (hη1 : η < 1 - offspringMean l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      Tendsto (lateRecoveryGoodThreshold rates l δ η) atTop (𝓝 0) ∧
      Tendsto (fun n ↦
        (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
          (lateRecoveryGoodCutoffStates rates l δ η n) /
        (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
          (sourceSurvivalEvent l δ n)) atTop (𝓝 1) ∧
      ∀ n, ∀ s ∈ lateRecoveryGoodCutoffStates rates l δ η n,
        1 - lateRecoveryGoodThreshold rates l δ η n ≤
          (continuationLaw (rates n) s
            (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
            {t | lateRecoveryEndpoints (rates n) l η s t} := by
  obtain ⟨δ₀, hδ₀, hgood⟩ := eventually_lateRecoveryGoodCutoffStates
    rates hl hη hηm hη1 hrates
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ
  obtain ⟨hθ, hbad, hpoint⟩ := hgood δ hδ
  have hδ1 : δ ∈ Ioo (0 : ℝ) 1 :=
    ⟨hδ.1, hδ.2.trans (hδ₀.2.trans (by norm_num))⟩
  have hS := sourceCutoffState_survival_probability_tendsto
    rates hl hδ1 hrates
  have hpos : 0 < 1 - 1 / l := by
    have hl0 : 0 < l := by linarith
    have hdiv : 1 / l < 1 := (div_lt_iff₀ hl0).mpr (by linarith)
    linarith
  have hG : Tendsto (fun n ↦
      (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
        (lateRecoveryGoodCutoffStates rates l δ η n)) atTop
        (𝓝 (1 - 1 / l)) := by
    have hdiff := hS.sub hbad
    simpa only [sub_zero] using hdiff.congr' (Eventually.of_forall (by
      intro n
      let μ := (evolve (rates n) n (sourceCutoff l δ n)).toMeasure
      let S := sourceSurvivalEvent l δ n
      let G := lateRecoveryGoodCutoffStates rates l δ η n
      have hGS : G ⊆ S := fun _ hs ↦ hs.1
      have hsd := measureReal_sdiff (μ := μ) hGS
        (show MeasurableSet G from trivial) (measure_ne_top μ _)
      dsimp [μ, S, G] at hsd ⊢
      linarith))
  have hratio := hG.div hS hpos.ne'
  have hratio' : Tendsto (fun n ↦
        (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
          (lateRecoveryGoodCutoffStates rates l δ η n) /
        (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
          (sourceSurvivalEvent l δ n)) atTop (𝓝 1) := by
    change Tendsto (fun n ↦
      (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
        (lateRecoveryGoodCutoffStates rates l δ η n) /
      (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
        (sourceSurvivalEvent l δ n)) atTop
        (𝓝 ((1 - 1 / l) / (1 - 1 / l))) at hratio
    simpa only [div_self hpos.ne'] using hratio
  exact ⟨hθ, hratio', fun n s hs ↦
    lateRecoveryGoodCutoffState_success_lower_bound rates l δ η n hs⟩

/-- The source's good cutoff trees are taken from the support of the actual
cutoff-state law. This has the same conditional mass as the larger good-state
set, and is eventually nonempty. -/
noncomputable def lateRecoverySupportedGoodCutoffStates (rates : ℕ → ℝ≥0)
    (l δ η : ℝ) (n : ℕ) : Set State :=
  lateRecoveryGoodCutoffStates rates l δ η n ∩
    (evolve (rates n) n (sourceCutoff l δ n)).support

theorem eventually_lateRecoverySupportedGoodCutoffStates_conditional
    (rates : ℕ → ℝ≥0) {l η : ℝ} (hl : 1 < l)
    (hη : 0 < η) (hηm : η < offspringMean l)
    (hη1 : η < 1 - offspringMean l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      Tendsto (lateRecoveryGoodThreshold rates l δ η) atTop (𝓝 0) ∧
      Tendsto (fun n ↦
        (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
          (lateRecoverySupportedGoodCutoffStates rates l δ η n) /
        (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
          (sourceSurvivalEvent l δ n)) atTop (𝓝 1) ∧
      (∀ᶠ n in atTop,
        (lateRecoverySupportedGoodCutoffStates rates l δ η n).Nonempty) ∧
      ∀ n, ∀ s ∈ lateRecoverySupportedGoodCutoffStates rates l δ η n,
        s ∈ (evolve (rates n) n (sourceCutoff l δ n)).support ∧
        s ∈ sourceSurvivalEvent l δ n ∧
        1 - lateRecoveryGoodThreshold rates l δ η n ≤
          (continuationLaw (rates n) s
            (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
            {t | lateRecoveryEndpoints (rates n) l η s t} := by
  obtain ⟨δ₀, hδ₀, hbase⟩ :=
    eventually_lateRecoveryGoodCutoffStates_conditional
      rates hl hη hηm hη1 hrates
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ
  obtain ⟨hθ, hratio, hpoint⟩ := hbase δ hδ
  have hδ1 : δ ∈ Ioo (0 : ℝ) 1 :=
    ⟨hδ.1, hδ.2.trans (hδ₀.2.trans (by norm_num))⟩
  have hmeasure (n : ℕ) :
      (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
        (lateRecoverySupportedGoodCutoffStates rates l δ η n) =
      (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
        (lateRecoveryGoodCutoffStates rates l δ η n) := by
    unfold lateRecoverySupportedGoodCutoffStates Measure.real
    exact congrArg ENNReal.toReal (PMF.toMeasure_apply_inter_support
      (evolve (rates n) n (sourceCutoff l δ n))
      (show MeasurableSet (lateRecoveryGoodCutoffStates rates l δ η n) from trivial))
  have hratio' : Tendsto (fun n ↦
        (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
          (lateRecoverySupportedGoodCutoffStates rates l δ η n) /
        (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
          (sourceSurvivalEvent l δ n)) atTop (𝓝 1) := by
    simpa only [hmeasure] using hratio
  have hS := sourceCutoffState_survival_probability_tendsto
    rates hl hδ1 hrates
  have hlimitPos : 0 < 1 - 1 / l := by
    have hl0 : 0 < l := by linarith
    have hdiv : 1 / l < 1 := (div_lt_iff₀ hl0).mpr (by linarith)
    linarith
  have hSpos : ∀ᶠ n in atTop,
      0 < (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
        (sourceSurvivalEvent l δ n) :=
    hS.eventually (Ioi_mem_nhds hlimitPos)
  have hGpos : ∀ᶠ n in atTop,
      0 < (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
        (lateRecoverySupportedGoodCutoffStates rates l δ η n) /
        (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
          (sourceSurvivalEvent l δ n) :=
    hratio'.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hne : ∀ᶠ n in atTop,
      (lateRecoverySupportedGoodCutoffStates rates l δ η n).Nonempty := by
    filter_upwards [hSpos, hGpos] with n _hsp hgp
    by_contra hnot
    have hempty : lateRecoverySupportedGoodCutoffStates rates l δ η n = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnot
    simp only [hempty, measureReal_empty, zero_div] at hgp
    exact (not_lt_of_ge le_rfl) hgp
  refine ⟨hθ, hratio', hne, ?_⟩
  intro n s hs
  exact ⟨hs.2, hs.1.1, hpoint n s hs.1⟩

/-- The infimum of continuation success probabilities over the reachable good
cutoff states is the source lemma's minimum, with the usual infimum convention
at the finitely many indices where the set may be empty. -/
noncomputable def lateRecoverySupportedGoodSuccessInf (rates : ℕ → ℝ≥0)
    (l δ η : ℝ) (n : ℕ) : ℝ :=
  sInf ((fun s : State ↦
    (continuationLaw (rates n) s
      (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
      {t | lateRecoveryEndpoints (rates n) l η s t}) ''
    lateRecoverySupportedGoodCutoffStates rates l δ η n)

theorem eventually_lateRecoverySupportedGoodSuccessInf_tendsto_one
    (rates : ℕ → ℝ≥0) {l η : ℝ} (hl : 1 < l)
    (hη : 0 < η) (hηm : η < offspringMean l)
    (hη1 : η < 1 - offspringMean l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      Tendsto (lateRecoverySupportedGoodSuccessInf rates l δ η) atTop (𝓝 1) := by
  obtain ⟨δ₀, hδ₀, hgood⟩ :=
    eventually_lateRecoverySupportedGoodCutoffStates_conditional
      rates hl hη hηm hη1 hrates
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ
  obtain ⟨hθ, _hratio, hne, hpoint⟩ := hgood δ hδ
  have hbound : ∀ᶠ n in atTop,
      0 ≤ 1 - lateRecoverySupportedGoodSuccessInf rates l δ η n ∧
      1 - lateRecoverySupportedGoodSuccessInf rates l δ η n ≤
        lateRecoveryGoodThreshold rates l δ η n := by
    filter_upwards [hne] with n ⟨s, hs⟩
    let A : Set ℝ := (fun s : State ↦
      (continuationLaw (rates n) s
        (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
        {t | lateRecoveryEndpoints (rates n) l η s t}) ''
          lateRecoverySupportedGoodCutoffStates rates l δ η n
    have hA : A.Nonempty := ⟨_, s, hs, rfl⟩
    have hbdd : BddBelow A := by
      refine ⟨0, ?_⟩
      rintro y ⟨u, hu, rfl⟩
      exact measureReal_nonneg
    have hlow : 1 - lateRecoveryGoodThreshold rates l δ η n ≤ sInf A := by
      apply le_csInf hA
      rintro y ⟨u, hu, rfl⟩
      exact (hpoint n u hu).2.2
    have hupp : sInf A ≤ 1 := by
      have hle : sInf A ≤
          (continuationLaw (rates n) s
            (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
            {t | lateRecoveryEndpoints (rates n) l η s t} :=
        csInf_le hbdd ⟨s, hs, rfl⟩
      exact hle.trans measureReal_le_one
    change 0 ≤ 1 - sInf A ∧ 1 - sInf A ≤ lateRecoveryGoodThreshold rates l δ η n
    constructor <;> linarith
  have hzero : Tendsto (fun n ↦
      1 - lateRecoverySupportedGoodSuccessInf rates l δ η n) atTop (𝓝 0) := by
    apply squeeze_zero' (hbound.mono fun _ h ↦ h.1) _ hθ
    exact hbound.mono fun _ h ↦ h.2
  have hlim : Tendsto (fun n ↦ (1 : ℝ) -
      (1 - lateRecoverySupportedGoodSuccessInf rates l δ η n)) atTop
      (𝓝 (1 - 0)) := tendsto_const_nhds.sub hzero
  have hfun : (fun n ↦ (1 : ℝ) -
      (1 - lateRecoverySupportedGoodSuccessInf rates l δ η n)) =
      lateRecoverySupportedGoodSuccessInf rates l δ η := by
    funext n
    ring
  rw [hfun, sub_zero] at hlim
  exact hlim

end HeightPaper.Model
