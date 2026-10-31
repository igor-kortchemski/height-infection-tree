module

public import HeightPaper.Probability.EarlyBranchJointLaw
public import HeightPaper.Probability.TerminalEventMixture

/-!
# Joint early variables and fluid trajectories on the common coupling

The existing full-path fluid bounds are transported to the birth-parent
uniform space, where the stopped early time-height pair has already been
coupled to its local limit.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal symmDiff Classical

namespace HeightPaper.CountCoupling

def sourceJointFluidBad (l δ C ε : ℝ) (n : ℕ) :
    Set (Model.FinitePath (2 * n + 1)) :=
  {p | (∃ t ∈ Icc (0 : ℝ) C,
      ε ≤ |(Model.infectious (p.eval ⌊t * n⌋₊) : ℝ) / n -
        if p.eval (2 * n + 1) ∈ Model.sourceSurvivalEvent l δ n then
          fluidInfectious l t else 0|) ∨
    (∃ t ∈ Icc (0 : ℝ) (fluidExtinctionTime l),
      ε ≤ |(p.eval ⌊t * n⌋₊).susceptible / (n : ℝ) -
        if p.eval (2 * n + 1) ∈ Model.sourceSurvivalEvent l δ n then
          fluidSusceptible l t else 1|)}

def localJointFluidBad (a l C ε : ℝ) (n : ℕ) :
    Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {q | (∃ t ∈ Icc (0 : ℝ) C,
      ε ≤ |(Model.infectious ((coupledTreeHistory a n (2 * n + 1) q).eval
          ⌊t * n⌋₊) : ℝ) / n -
        if q.1 ∈ localSurvival l then fluidInfectious l t else 0|) ∨
    (∃ t ∈ Icc (0 : ℝ) (fluidExtinctionTime l),
      ε ≤ |((coupledTreeHistory a n (2 * n + 1) q).eval
          ⌊t * n⌋₊).susceptible / (n : ℝ) -
        if q.1 ∈ localSurvival l then fluidSusceptible l t else 1|)}

/-- Both real-time fluid coordinates obey the proved joint concentration bound
after transfer from the actual epidemic path law to its exact common-uniform
realization. -/
theorem coupled_source_joint_fluid_compact_time_concentration
    (rates : ℕ → ℝ≥0) {l δ C ε : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) :
    Tendsto (fun n ↦ birthParentLaw.real
      ((coupledTreeHistory (rates n * n) n (2 * n + 1)) ⁻¹'
        sourceJointFluidBad l δ C ε n)) atTop (𝓝 0) := by
  have hflow : Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (sourceJointFluidBad l δ C ε n)) atTop (𝓝 0) := by
    simpa only [sourceJointFluidBad] using
      Model.source_joint_fluid_compact_time_mixture_concentration
        rates hl hδ hC hrates hε
  apply hflow.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  let a : ℝ≥0 := rates n * n
  let N := 2 * n + 1
  let A := sourceJointFluidBad l δ C ε n
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hrate : a / n = rates n := by
    dsimp [a]
    field_simp [hn0]
  have hLaw := coupledTreeHistory_law a n N
  rw [hrate] at hLaw
  have hreal := congrArg (fun μ : Measure (Model.FinitePath N) ↦ μ.real A) hLaw
  change ENNReal.toReal ((birthParentLaw.map (coupledTreeHistory a n N)) A) =
    ENNReal.toReal ((Model.pathMeasure (rates n) n N) A) at hreal
  rw [Measure.map_apply (measurable_coupledTreeHistory a n N) hA] at hreal
  simpa only [Measure.real, Set.preimage, a, N, A,
    NNReal.coe_mul, NNReal.coe_natCast] using hreal.symm

/-- The two fluid coordinates converge jointly to the trajectories selected
by the local infinite-survival event on the same common-uniform space. -/
theorem coupled_local_joint_fluid_compact_time_concentration
    (rates : ℕ → ℝ≥0) {l δ C ε : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) :
    Tendsto (fun n ↦ birthParentLaw.real
      (localJointFluidBad ((rates n : ℝ) * n) l C ε n)) atTop (𝓝 0) := by
  have hsource := coupled_source_joint_fluid_compact_time_concentration
    rates hl hδ hC hrates hε
  have hsurv := sourceSurvivalEvent_localSurvival_disagreement_tendsto_zero
    rates hl hδ hrates
  have hsum := hsource.add hsurv
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  let a : ℝ := (rates n : ℝ) * n
  let p : ((ℕ → ℝ) × (ℕ → ℝ)) → Model.FinitePath (2 * n + 1) :=
    coupledTreeHistory a n (2 * n + 1)
  let S : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | ¬ ((p q).last ∈ Model.sourceSurvivalEvent l δ n ↔
      q.1 ∈ localSurvival l)}
  have hsub : localJointFluidBad a l C ε n ⊆
      (p ⁻¹' sourceJointFluidBad l δ C ε n) ∪ S := by
    intro q hq
    by_cases hs : (p q).last ∈ Model.sourceSurvivalEvent l δ n ↔
        q.1 ∈ localSurvival l
    · apply Or.inl
      change (∃ t ∈ Icc (0 : ℝ) C,
          ε ≤ |(Model.infectious ((p q).eval ⌊t * n⌋₊) : ℝ) / n -
            if q.1 ∈ localSurvival l then fluidInfectious l t else 0|) ∨
        (∃ t ∈ Icc (0 : ℝ) (fluidExtinctionTime l),
          ε ≤ |((p q).eval ⌊t * n⌋₊).susceptible / (n : ℝ) -
            if q.1 ∈ localSurvival l then fluidSusceptible l t else 1|) at hq
      have heq : (p q).eval (2 * n + 1) ∈ Model.sourceSurvivalEvent l δ n ↔
          q.1 ∈ localSurvival l := by
        simpa only [Model.FinitePath.eval_last] using hs
      change (∃ t ∈ Icc (0 : ℝ) C,
          ε ≤ |(Model.infectious ((p q).eval ⌊t * n⌋₊) : ℝ) / n -
            if (p q).eval (2 * n + 1) ∈ Model.sourceSurvivalEvent l δ n then
              fluidInfectious l t else 0|) ∨
        (∃ t ∈ Icc (0 : ℝ) (fluidExtinctionTime l),
          ε ≤ |((p q).eval ⌊t * n⌋₊).susceptible / (n : ℝ) -
            if (p q).eval (2 * n + 1) ∈ Model.sourceSurvivalEvent l δ n then
              fluidSusceptible l t else 1|)
      by_cases hlocal : q.1 ∈ localSurvival l
      · have hsource : (p q).eval (2 * n + 1) ∈
            Model.sourceSurvivalEvent l δ n := heq.mpr hlocal
        simpa only [ite_eq_left hlocal, ite_eq_left hsource] using hq
      · have hsource : (p q).eval (2 * n + 1) ∉
            Model.sourceSurvivalEvent l δ n :=
          fun h ↦ hlocal (heq.mp h)
        simpa only [ite_eq_right hlocal, ite_eq_right hsource] using hq
    · right
      simpa only [S, Set.mem_ofPred_eq] using hs
  calc
    birthParentLaw.real (localJointFluidBad a l C ε n) ≤
        birthParentLaw.real (p ⁻¹' sourceJointFluidBad l δ C ε n) +
          birthParentLaw.real S :=
      (measureReal_mono hsub (measure_ne_top _ _)).trans
        (measureReal_union_le _ _)
    _ = birthParentLaw.real
          ((coupledTreeHistory (rates n * n) n (2 * n + 1)) ⁻¹'
            sourceJointFluidBad l δ C ε n) +
        birthParentLaw.real {q |
          ¬ ((coupledTreeHistory (rates n * n) n (2 * n + 1) q).last ∈
            Model.sourceSurvivalEvent l δ n ↔ q.1 ∈ localSurvival l)} := by
      simp only [p, S, a]

/-- The stopped early time-height pair and the two fluid paths satisfy their
limit controls simultaneously on the common-uniform probability space. -/
theorem coupled_early_pair_and_local_joint_fluid_concentration
    (rates : ℕ → ℝ≥0) {l δ C ε : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) :
    Tendsto (fun n ↦ birthParentLaw.real
      ({q | finiteEarlyExtinctionTime ((rates n : ℝ) * n) n
          ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ q.1 ≠
            localEarlyExtinctionTime l q.1 ∨
        finiteEarlyHeight ((rates n : ℝ) * n) n
          ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ q ≠
            localEarlyHeight l q} ∪
        localJointFluidBad ((rates n : ℝ) * n) l C ε n)) atTop (𝓝 0) := by
  have hT : (1 - δ) * fluidExtinctionTime l ∈
      Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  have hearly := finiteEarly_joint_disagreement_tendsto_zero rates hl hT hrates
  have hfluid := coupled_local_joint_fluid_compact_time_concentration
    rates hl hδ hC hrates hε
  have hsum := hearly.add hfluid
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  exact Eventually.of_forall (fun n ↦ measureReal_union_le _ _)

/-- The stopped early pair read at an intermediate time from a complete
epidemic path. -/
noncomputable def earlyTerminalPairAt {N : ℕ} (H : ℕ)
    (p : Model.FinitePath N) : ℕ × ℕ :=
  if 0 < Model.infectious (p.eval H) then (0, 0)
  else (Model.eventCount (p.eval H), Model.height (p.eval H))

theorem coupledTreeHistory_eval_eq_state (a : ℝ) (n H N : ℕ)
    (hHN : H ≤ N) (q : (ℕ → ℝ) × (ℕ → ℝ)) :
    (coupledTreeHistory a n N q).eval H =
      (coupledTreeHistory a n H q).last := by
  simp only [coupledTreeHistory, Model.rankHistory,
    Model.trajectoryPrefix_eval _ _ _ hHN, Model.trajectoryPrefix_last]

/-- The intermediate path observable exactly equals the coupled stopped
time-height pair whenever its horizon lies inside the complete path. -/
theorem finiteEarly_pair_eq_terminalPathAt (a : ℝ) (n H N : ℕ)
    (hHN : H ≤ N) (q : (ℕ → ℝ) × (ℕ → ℝ)) :
    (finiteEarlyExtinctionTime a n H q.1, finiteEarlyHeight a n H q) =
      earlyTerminalPairAt H (coupledTreeHistory a n N q) := by
  rw [finiteEarly_pair_eq_terminalPath]
  simp only [earlyTerminalPairAt, coupledTreeHistory_eval_eq_state a n H N hHN q]

/-- Exact law of the intermediate early pair under the complete epidemic
path measure, realized with the same birth-parent uniforms. -/
theorem finiteEarly_pairAt_law (a : ℝ≥0) (n H N : ℕ) (hHN : H ≤ N) :
    birthParentLaw.map (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      (finiteEarlyExtinctionTime a n H q.1, finiteEarlyHeight a n H q)) =
      (Model.pathMeasure (a / n) n N).map (earlyTerminalPairAt H) := by
  have heq : (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      (finiteEarlyExtinctionTime a n H q.1, finiteEarlyHeight a n H q)) =
      earlyTerminalPairAt H ∘ coupledTreeHistory a n N := by
    funext q
    exact finiteEarly_pair_eq_terminalPathAt a n H N hHN q
  rw [heq, ← Measure.map_map (Model.FinitePath.measurable _)
    (measurable_coupledTreeHistory a n N), coupledTreeHistory_law]

/-- The stopped early pair also converges setwise when read from the full
epidemic path used for the fluid coordinates. -/
theorem earlyTerminalPairAt_event_probability_tendsto
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (B : Set (ℕ × ℕ)) :
    Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (earlyTerminalPairAt ⌊T * n⌋₊ ⁻¹' B)) atTop
      (𝓝 (birthParentLaw.real {q |
        (localEarlyExtinctionTime l q.1, localEarlyHeight l q) ∈ B})) := by
  have hshort := earlyTerminalPair_event_probability_tendsto rates hl hT hrates B
  have hB : MeasurableSet B := (Set.to_countable B).measurableSet
  have hHN (n : ℕ) : ⌊T * n⌋₊ ≤ 2 * n + 1 := by
    apply Nat.floor_le_of_le
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right
      (hT.2.trans (fluidExtinctionTime_lt_two hl)).le
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  apply hshort.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  let a : ℝ≥0 := rates n * n
  let H := ⌊T * n⌋₊
  let N := 2 * n + 1
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hrate : a / n = rates n := by
    dsimp [a]
    field_simp [hn0]
  have hfull := finiteEarly_pairAt_law a n H N (hHN n)
  have hsmall := finiteEarly_pair_law a n H
  rw [hrate] at hfull hsmall
  have hLaw := hfull.symm.trans hsmall
  have hreal := congrArg (fun μ : Measure (ℕ × ℕ) ↦ μ.real B) hLaw
  change ENNReal.toReal (((Model.pathMeasure (rates n) n N).map
      (earlyTerminalPairAt H)) B) =
    ENNReal.toReal (((Model.pathMeasure (rates n) n H).map earlyTerminalPair) B)
    at hreal
  rw [Measure.map_apply (Model.FinitePath.measurable _) hB,
    Measure.map_apply (Model.FinitePath.measurable _) hB] at hreal
  simpa only [N, H, Measure.real] using hreal.symm

/-- Under the original complete-path law, any event in the early stopped
time-height pair occurs jointly with both compact-time fluid estimates with
the limiting probability of the corresponding local pair event. -/
theorem earlyTerminalPairAt_and_source_joint_fluid_good_probability_tendsto
    (rates : ℕ → ℝ≥0) {l δ C ε : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) (B : Set (ℕ × ℕ)) :
    Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        ((earlyTerminalPairAt
          ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ ⁻¹' B) \
          sourceJointFluidBad l δ C ε n)) atTop
      (𝓝 (birthParentLaw.real {q |
        (localEarlyExtinctionTime l q.1, localEarlyHeight l q) ∈ B})) := by
  have hT : (1 - δ) * fluidExtinctionTime l ∈
      Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  have hpair := earlyTerminalPairAt_event_probability_tendsto rates hl hT hrates B
  have hbad : Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (sourceJointFluidBad l δ C ε n)) atTop (𝓝 0) := by
    simpa only [sourceJointFluidBad] using
      Model.source_joint_fluid_compact_time_mixture_concentration
        rates hl hδ hC hrates hε
  have habs : Tendsto (fun n ↦
      |(Model.pathMeasure (rates n) n (2 * n + 1)).real
          ((earlyTerminalPairAt
            ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ ⁻¹' B) \
            sourceJointFluidBad l δ C ε n) -
        (Model.pathMeasure (rates n) n (2 * n + 1)).real
          (earlyTerminalPairAt
            ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ ⁻¹' B)|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hbad
    apply Eventually.of_forall
    intro n
    let μ := Model.pathMeasure (rates n) n (2 * n + 1)
    let A : Set (Model.FinitePath (2 * n + 1)) := earlyTerminalPairAt
      ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ ⁻¹' B
    let F := sourceJointFluidBad l δ C ε n
    have hsub : (A \ F) ∆ A ⊆ F := by
      intro p hp
      simp only [mem_symmDiff, Set.mem_sdiff] at hp
      rcases hp with ⟨⟨hA, _⟩, hnA⟩ | ⟨hA, hnDiff⟩
      · exact (hnA hA).elim
      · by_contra hnotF
        exact hnDiff ⟨hA, hnotF⟩
    have hbound := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := μ) (show MeasurableSet (A \ F) from trivial).nullMeasurableSet
      (show MeasurableSet A from trivial).nullMeasurableSet
    exact hbound.trans (measureReal_mono hsub (measure_ne_top _ _))
  have hzero := (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  have hresult := hzero.add hpair
  simpa only [sub_add_cancel, zero_add] using hresult

/-- On complete epidemic paths, the paper's source cutoff survival flag and
the zero value of the stopped early extinction coordinate disagree with
vanishing probability. -/
theorem sourceSurvivalEvent_earlyTerminalPairAt_zero_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      {p | ¬ (p.last ∈ Model.sourceSurvivalEvent l δ n ↔
        (earlyTerminalPairAt
          ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ p).1 = 0)})
      atTop (𝓝 0) := by
  have hT : (1 - δ) * fluidExtinctionTime l ∈
      Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  have hsource := sourceSurvivalEvent_localSurvival_disagreement_tendsto_zero
    rates hl hδ hrates
  have hearly := finiteEarly_joint_disagreement_tendsto_zero rates hl hT hrates
  have hsum := hsource.add hearly
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [eventually_gt_atTop 0] with n hn
  let a : ℝ≥0 := rates n * n
  let H := ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊
  let N := 2 * n + 1
  let p : ((ℕ → ℝ) × (ℕ → ℝ)) → Model.FinitePath N :=
    coupledTreeHistory a n N
  let A : Set (Model.FinitePath N) :=
    {v | ¬ (v.last ∈ Model.sourceSurvivalEvent l δ n ↔
      (earlyTerminalPairAt H v).1 = 0)}
  let L : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | ¬ ((p q).last ∈ Model.sourceSurvivalEvent l δ n ↔
      q.1 ∈ localSurvival l)}
  let E : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | finiteEarlyExtinctionTime a n H q.1 ≠ localEarlyExtinctionTime l q.1 ∨
      finiteEarlyHeight a n H q ≠ localEarlyHeight l q}
  let M : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | ¬ ((p q).last ∈ Model.sourceSurvivalEvent l δ n ↔
      finiteEarlyExtinctionTime a n H q.1 = 0)}
  have hHN : H ≤ N := by
    dsimp [H, N]
    apply Nat.floor_le_of_le
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right
      (hT.2.trans (fluidExtinctionTime_lt_two hl)).le
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hsub : M ⊆ L ∪ E := by
    intro q hq
    by_cases hs : (p q).last ∈ Model.sourceSurvivalEvent l δ n ↔
        q.1 ∈ localSurvival l
    · right
      by_cases he : finiteEarlyExtinctionTime a n H q.1 =
          localEarlyExtinctionTime l q.1
      · have hz : finiteEarlyExtinctionTime a n H q.1 = 0 ↔
            q.1 ∈ localSurvival l := by
          rw [he]
          exact localEarlyExtinctionTime_eq_zero_iff l q.1
        have hm : (p q).last ∈ Model.sourceSurvivalEvent l δ n ↔
            finiteEarlyExtinctionTime a n H q.1 = 0 :=
          hs.trans hz.symm
        exact (hq hm).elim
      · exact Or.inl he
    · exact Or.inl hs
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hrate : a / n = rates n := by
    dsimp [a]
    field_simp [hn0]
  have hLaw := coupledTreeHistory_law a n N
  rw [hrate] at hLaw
  have hA : MeasurableSet A := trivial
  have hreal := congrArg (fun μ : Measure (Model.FinitePath N) ↦ μ.real A) hLaw
  change ENNReal.toReal ((birthParentLaw.map p) A) =
    ENNReal.toReal ((Model.pathMeasure (rates n) n N) A) at hreal
  rw [Measure.map_apply (measurable_coupledTreeHistory a n N) hA] at hreal
  have hpre : p ⁻¹' A = M := by
    ext q
    have hfirst := congrArg Prod.fst
      (finiteEarly_pair_eq_terminalPathAt a n H N hHN q)
    change finiteEarlyExtinctionTime a n H q.1 =
      (earlyTerminalPairAt H (p q)).1 at hfirst
    simp only [A, M, mem_preimage, mem_ofPred_eq]
    rw [← hfirst]
  rw [hpre] at hreal
  calc
    (Model.pathMeasure (rates n) n N).real A = birthParentLaw.real M := by
      simpa only [Measure.real] using hreal.symm
    _ ≤ birthParentLaw.real L + birthParentLaw.real E :=
      (measureReal_mono hsub (measure_ne_top _ _)).trans
        (measureReal_union_le _ _)
    _ = birthParentLaw.real {q |
        ¬ ((coupledTreeHistory (rates n * n) n (2 * n + 1) q).last ∈
          Model.sourceSurvivalEvent l δ n ↔ q.1 ∈ localSurvival l)} +
      birthParentLaw.real {q |
        finiteEarlyExtinctionTime ((rates n : ℝ) * n) n H q.1 ≠
          localEarlyExtinctionTime l q.1 ∨
        finiteEarlyHeight ((rates n : ℝ) * n) n H q ≠
          localEarlyHeight l q} := by
      simp only [L, E, p, a, N, NNReal.coe_mul, NNReal.coe_natCast]

/-- Failure of either fluid estimate when the trajectory is selected by the
stopped early extinction coordinate of the same epidemic path. -/
def earlyPairJointFluidBad (l δ C ε : ℝ) (n : ℕ) :
    Set (Model.FinitePath (2 * n + 1)) :=
  {p | (∃ t ∈ Icc (0 : ℝ) C,
      ε ≤ |(Model.infectious (p.eval ⌊t * n⌋₊) : ℝ) / n -
        if (earlyTerminalPairAt
          ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ p).1 = 0 then
          fluidInfectious l t else 0|) ∨
    (∃ t ∈ Icc (0 : ℝ) (fluidExtinctionTime l),
      ε ≤ |(p.eval ⌊t * n⌋₊).susceptible / (n : ℝ) -
        if (earlyTerminalPairAt
          ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ p).1 = 0 then
          fluidSusceptible l t else 1|)}

/-- Both compact-time fluid paths converge under the actual epidemic path law
to the trajectories selected by the stopped early extinction observable. -/
theorem earlyPair_joint_fluid_compact_time_concentration
    (rates : ℕ → ℝ≥0) {l δ C ε : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      (earlyPairJointFluidBad l δ C ε n)) atTop (𝓝 0) := by
  have hsource : Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (sourceJointFluidBad l δ C ε n)) atTop (𝓝 0) := by
    simpa only [sourceJointFluidBad] using
      Model.source_joint_fluid_compact_time_mixture_concentration
        rates hl hδ hC hrates hε
  have hmismatch :=
    sourceSurvivalEvent_earlyTerminalPairAt_zero_disagreement_tendsto_zero
      rates hl hδ hrates
  have hsum := hsource.add hmismatch
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  let H := ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊
  let D : Set (Model.FinitePath (2 * n + 1)) :=
    {p | ¬ (p.last ∈ Model.sourceSurvivalEvent l δ n ↔
      (earlyTerminalPairAt H p).1 = 0)}
  have hsub : earlyPairJointFluidBad l δ C ε n ⊆
      sourceJointFluidBad l δ C ε n ∪ D := by
    intro p hp
    by_cases hs : p.last ∈ Model.sourceSurvivalEvent l δ n ↔
        (earlyTerminalPairAt H p).1 = 0
    · left
      change (∃ t ∈ Icc (0 : ℝ) C,
          ε ≤ |(Model.infectious (p.eval ⌊t * n⌋₊) : ℝ) / n -
            if (earlyTerminalPairAt H p).1 = 0 then
              fluidInfectious l t else 0|) ∨
        (∃ t ∈ Icc (0 : ℝ) (fluidExtinctionTime l),
          ε ≤ |(p.eval ⌊t * n⌋₊).susceptible / (n : ℝ) -
            if (earlyTerminalPairAt H p).1 = 0 then
              fluidSusceptible l t else 1|) at hp
      change (∃ t ∈ Icc (0 : ℝ) C,
          ε ≤ |(Model.infectious (p.eval ⌊t * n⌋₊) : ℝ) / n -
            if p.eval (2 * n + 1) ∈ Model.sourceSurvivalEvent l δ n then
              fluidInfectious l t else 0|) ∨
        (∃ t ∈ Icc (0 : ℝ) (fluidExtinctionTime l),
          ε ≤ |(p.eval ⌊t * n⌋₊).susceptible / (n : ℝ) -
            if p.eval (2 * n + 1) ∈ Model.sourceSurvivalEvent l δ n then
              fluidSusceptible l t else 1|)
      by_cases hearly : (earlyTerminalPairAt H p).1 = 0
      · have hsurv : p.eval (2 * n + 1) ∈
            Model.sourceSurvivalEvent l δ n := by
          simpa only [Model.FinitePath.eval_last] using hs.mpr hearly
        simpa only [ite_eq_left hearly, ite_eq_left hsurv] using hp
      · have hsurv : p.eval (2 * n + 1) ∉
            Model.sourceSurvivalEvent l δ n := by
          simpa only [Model.FinitePath.eval_last] using
            (fun h ↦ hearly (hs.mp h))
        simpa only [ite_eq_right hearly, ite_eq_right hsurv] using hp
    · right
      simpa only [D, mem_ofPred_eq] using hs
  calc
    (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (earlyPairJointFluidBad l δ C ε n) ≤
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (sourceJointFluidBad l δ C ε n) +
      (Model.pathMeasure (rates n) n (2 * n + 1)).real D :=
      (measureReal_mono hsub (measure_ne_top _ _)).trans
        (measureReal_union_le _ _)
    _ = _ := by simp only [D, H]

/-- The complete epidemic path has the limiting early time-height pair while
both fluid coordinates follow the trajectories selected by that same early
pair. This is a joint cylinder-event form of the paper's fluid assertion. -/
theorem earlyTerminalPairAt_and_earlyPair_joint_fluid_good_probability_tendsto
    (rates : ℕ → ℝ≥0) {l δ C ε : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) (B : Set (ℕ × ℕ)) :
    Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        ((earlyTerminalPairAt
          ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ ⁻¹' B) \
          earlyPairJointFluidBad l δ C ε n)) atTop
      (𝓝 (birthParentLaw.real {q |
        (localEarlyExtinctionTime l q.1, localEarlyHeight l q) ∈ B})) := by
  have hT : (1 - δ) * fluidExtinctionTime l ∈
      Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  have hpair := earlyTerminalPairAt_event_probability_tendsto rates hl hT hrates B
  have hbad := earlyPair_joint_fluid_compact_time_concentration
    rates hl hδ hC hrates hε
  have habs : Tendsto (fun n ↦
      |(Model.pathMeasure (rates n) n (2 * n + 1)).real
          ((earlyTerminalPairAt
            ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ ⁻¹' B) \
            earlyPairJointFluidBad l δ C ε n) -
        (Model.pathMeasure (rates n) n (2 * n + 1)).real
          (earlyTerminalPairAt
            ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ ⁻¹' B)|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hbad
    apply Eventually.of_forall
    intro n
    let μ := Model.pathMeasure (rates n) n (2 * n + 1)
    let A : Set (Model.FinitePath (2 * n + 1)) := earlyTerminalPairAt
      ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ ⁻¹' B
    let F := earlyPairJointFluidBad l δ C ε n
    have hsub : (A \ F) ∆ A ⊆ F := by
      intro p hp
      simp only [mem_symmDiff, Set.mem_sdiff] at hp
      rcases hp with ⟨⟨hA, _⟩, hnA⟩ | ⟨hA, hnDiff⟩
      · exact (hnA hA).elim
      · by_contra hnotF
        exact hnDiff ⟨hA, hnotF⟩
    have hbound := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := μ) (show MeasurableSet (A \ F) from trivial).nullMeasurableSet
      (show MeasurableSet A from trivial).nullMeasurableSet
    exact hbound.trans (measureReal_mono hsub (measure_ne_top _ _))
  have hzero := (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  have hresult := hzero.add hpair
  simpa only [sub_add_cancel, zero_add] using hresult

/-- The full epidemic path has negligible probability of extinguishing
exactly at a growing preterminal event horizon. -/
theorem earlyTerminalPairAt_horizon_probability_tendsto_zero
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      {p | (earlyTerminalPairAt ⌊T * n⌋₊ p).1 = ⌊T * n⌋₊})
      atTop (𝓝 0) := by
  have hbase := finiteEarly_horizon_extinction_probability_tendsto_zero
    rates hl hT hrates
  have hHN (n : ℕ) : ⌊T * n⌋₊ ≤ 2 * n + 1 := by
    apply Nat.floor_le_of_le
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right
      (hT.2.trans (fluidExtinctionTime_lt_two hl)).le
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  apply hbase.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  let a : ℝ≥0 := rates n * n
  let H := ⌊T * n⌋₊
  let N := 2 * n + 1
  let B : Set (ℕ × ℕ) := {z | z.1 = H}
  have hB : MeasurableSet B := (Set.to_countable B).measurableSet
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hrate : a / n = rates n := by
    dsimp [a]
    field_simp [hn0]
  have hLaw := finiteEarly_pairAt_law a n H N (hHN n)
  rw [hrate] at hLaw
  have hreal := congrArg (fun μ : Measure (ℕ × ℕ) ↦ μ.real B) hLaw
  change ENNReal.toReal ((birthParentLaw.map
      (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
        (finiteEarlyExtinctionTime a n H q.1, finiteEarlyHeight a n H q))) B) =
    ENNReal.toReal (((Model.pathMeasure (rates n) n N).map
      (earlyTerminalPairAt H)) B) at hreal
  have hF : Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      (finiteEarlyExtinctionTime a n H q.1, finiteEarlyHeight a n H q)) :=
    ((measurable_finiteEarlyExtinctionTime a n H).comp measurable_fst).prodMk
      (measurable_finiteEarlyHeight a n H)
  rw [Measure.map_apply hF hB,
    Measure.map_apply (Model.FinitePath.measurable _) hB] at hreal
  change birthParentLaw.real
      {q | finiteEarlyExtinctionTime a n H q.1 = H} =
    (Model.pathMeasure (rates n) n N).real
      {p | (earlyTerminalPairAt H p).1 = H} at hreal
  simpa only [a, H, N, NNReal.coe_mul, NNReal.coe_natCast] using hreal

end HeightPaper.CountCoupling
