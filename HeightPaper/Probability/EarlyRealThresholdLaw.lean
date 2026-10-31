module

public import HeightPaper.Probability.EarlyFluidJointLaw

/-!
# The paper's real threshold for the early extinction time

The epidemic path is already coupled to its local early-time limit. This
module identifies its first-extinction coordinate with the terminal event
count and compares the real threshold in the TeX statement with the floored
cutoff used by the finite coupling.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal symmDiff Classical

namespace HeightPaper.CountCoupling

/-- On every supported epidemic path, the first coordinate of the stopped
early pair is the terminal extinction time clipped to zero after its horizon. -/
theorem earlyTerminalPairAt_fst_eq_ite_terminalTime
    {rate : ℝ≥0} {n N H : ℕ} (hN : 2 * n + 1 ≤ N) (hH : H ≤ N)
    {p : Model.FinitePath N} (hp : Model.SupportedPath rate n N p.eval) :
    (earlyTerminalPairAt H p).1 =
      if 2 * p.last.vertices - 1 ≤ H then 2 * p.last.vertices - 1 else 0 := by
  let τ := 2 * (p.eval N).vertices - 1
  have hτ : τ = 2 * p.last.vertices - 1 := by
    simp only [τ, Model.FinitePath.eval_last]
  have hfirst := hp.first_extinction hN
  change 0 < τ ∧ τ ≤ N ∧ (p.eval τ).active = ∅ ∧
    ∀ k < τ, (p.eval k).active.Nonempty at hfirst
  rw [← hτ]
  by_cases hτH : τ ≤ H
  · have hHstate := hp.absorbed_stable hτH hH hfirst.2.2.1
    have hNstate := hp.absorbed_stable hfirst.2.1 le_rfl hfirst.2.2.1
    have hlast : p.last = p.eval τ := by
      simpa only [Model.FinitePath.eval_last] using hNstate
    have hdead : ¬ 0 < Model.infectious (p.eval H) := by
      rw [hHstate]
      simp [Model.infectious, hfirst.2.2.1]
    have hterminal : p.last.active = ∅ := by
      rw [hlast]
      exact hfirst.2.2.1
    have hcount : Model.eventCount (p.eval H) = τ := by
      rw [hHstate, ← hlast]
      simpa only [hτ] using Model.eventCount_absorbed hterminal
    change (if 0 < Model.infectious (p.eval H) then (0, 0)
      else (Model.eventCount (p.eval H), Model.height (p.eval H))).1 =
        if τ ≤ H then τ else 0
    rw [ite_eq_right hdead, ite_eq_left hτH]
    exact hcount
  · have hactive := hfirst.2.2.2 H (lt_of_not_ge hτH)
    have hpos : 0 < Model.infectious (p.eval H) := by
      change 0 < (p.eval H).active.card
      exact Finset.card_pos.mpr hactive
    change (if 0 < Model.infectious (p.eval H) then (0, 0)
      else (Model.eventCount (p.eval H), Model.height (p.eval H))).1 =
        if τ ≤ H then τ else 0
    rw [ite_eq_left hpos, ite_eq_right hτH]

/-- The full stopped early pair is the terminal extinction time and tree
height when extinction precedes its horizon, and is zero otherwise. -/
theorem earlyTerminalPairAt_eq_ite_terminalPair
    {rate : ℝ≥0} {n N H : ℕ} (hN : 2 * n + 1 ≤ N) (hH : H ≤ N)
    {p : Model.FinitePath N} (hp : Model.SupportedPath rate n N p.eval) :
    earlyTerminalPairAt H p =
      if 2 * p.last.vertices - 1 ≤ H then
        (2 * p.last.vertices - 1, Model.height p.last) else (0, 0) := by
  let τ := 2 * (p.eval N).vertices - 1
  have hτ : τ = 2 * p.last.vertices - 1 := by
    simp only [τ, Model.FinitePath.eval_last]
  have hfirst := hp.first_extinction hN
  change 0 < τ ∧ τ ≤ N ∧ (p.eval τ).active = ∅ ∧
    ∀ k < τ, (p.eval k).active.Nonempty at hfirst
  rw [← hτ]
  by_cases hτH : τ ≤ H
  · have hHstate := hp.absorbed_stable hτH hH hfirst.2.2.1
    have hNstate := hp.absorbed_stable hfirst.2.1 le_rfl hfirst.2.2.1
    have hlast : p.last = p.eval τ := by
      simpa only [Model.FinitePath.eval_last] using hNstate
    have hfinal : p.eval H = p.last := hHstate.trans hlast.symm
    have hdead : ¬ 0 < Model.infectious (p.eval H) := by
      rw [hHstate]
      simp [Model.infectious, hfirst.2.2.1]
    have hterminal : p.last.active = ∅ := by
      rw [hlast]
      exact hfirst.2.2.1
    have hcount : Model.eventCount p.last = τ := by
      simpa only [hτ] using Model.eventCount_absorbed hterminal
    change (if 0 < Model.infectious (p.eval H) then (0, 0)
      else (Model.eventCount (p.eval H), Model.height (p.eval H))) =
        if τ ≤ H then (τ, Model.height p.last) else (0, 0)
    rw [ite_eq_right hdead, ite_eq_left hτH, hfinal, hcount]
  · have hactive := hfirst.2.2.2 H (lt_of_not_ge hτH)
    have hpos : 0 < Model.infectious (p.eval H) := by
      change 0 < (p.eval H).active.card
      exact Finset.card_pos.mpr hactive
    change (if 0 < Model.infectious (p.eval H) then (0, 0)
      else (Model.eventCount (p.eval H), Model.height (p.eval H))) =
        if τ ≤ H then (τ, Model.height p.last) else (0, 0)
    rw [ite_eq_left hpos, ite_eq_right hτH]

/-- The first height coordinate in the paper, using the strict inequality
against the floored preterminal cutoff. -/
noncomputable def strictEarlyHeight (l δ : ℝ) (n : ℕ)
    (p : Model.FinitePath (2 * n + 1)) : ℕ :=
  if 2 * p.last.vertices - 1 < Model.sourceCutoff l δ n then
    Model.height p.last else 0

theorem strictEarlyHeight_eq_earlyTerminalPairAt_snd_of_ne_horizon
    {rate : ℝ≥0} {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (n : ℕ)
    {p : Model.FinitePath (2 * n + 1)}
    (hp : Model.SupportedPath rate n (2 * n + 1) p.eval)
    (hne : 2 * p.last.vertices - 1 ≠ Model.sourceCutoff l δ n) :
    strictEarlyHeight l δ n p =
      (earlyTerminalPairAt (Model.sourceCutoff l δ n) p).2 := by
  rw [earlyTerminalPairAt_eq_ite_terminalPair le_rfl
    (Model.sourceCutoff_le_steps hl hδ n) hp]
  change (if 2 * p.last.vertices - 1 < Model.sourceCutoff l δ n then
      Model.height p.last else 0) =
    (if 2 * p.last.vertices - 1 ≤ Model.sourceCutoff l δ n then
      (2 * p.last.vertices - 1, Model.height p.last) else (0, 0)).2
  by_cases hlt : 2 * p.last.vertices - 1 < Model.sourceCutoff l δ n
  · simp only [ite_eq_left hlt, ite_eq_left hlt.le]
  · have hnotle : ¬ 2 * p.last.vertices - 1 ≤ Model.sourceCutoff l δ n := by
      omega
    simp only [ite_eq_right hlt, ite_eq_right hnotle]

/-- The paper's strict-cutoff early height and the non-strict stopped early
height differ with vanishing probability under the original path law. -/
theorem strictEarlyHeight_earlyTerminalPairAt_snd_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      {p | strictEarlyHeight l δ n p ≠
        (earlyTerminalPairAt (Model.sourceCutoff l δ n) p).2})
      atTop (𝓝 0) := by
  have hT : (1 - δ) * fluidExtinctionTime l ∈
      Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  have hboundary := earlyTerminalPairAt_horizon_probability_tendsto_zero
    rates hl hT hrates
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hboundary
  apply Eventually.of_forall
  intro n
  let H := Model.sourceCutoff l δ n
  let μ := Model.pathMeasure (rates n) n (2 * n + 1)
  let A : Set (Model.FinitePath (2 * n + 1)) :=
    {p | strictEarlyHeight l δ n p ≠ (earlyTerminalPairAt H p).2}
  let B : Set (Model.FinitePath (2 * n + 1)) :=
    {p | (earlyTerminalPairAt H p).1 = H}
  have hsub : A ≤ᵐ[μ] B := by
    filter_upwards [Model.ae_supportedPath (rates n) n (2 * n + 1)] with p hp
    intro hmis
    by_cases hne : 2 * p.last.vertices - 1 ≠ H
    · exact (hmis (strictEarlyHeight_eq_earlyTerminalPairAt_snd_of_ne_horizon
        hl hδ n hp hne)).elim
    · have heq : 2 * p.last.vertices - 1 = H := not_ne_iff.mp hne
      have hpair := earlyTerminalPairAt_eq_ite_terminalPair le_rfl
        (Model.sourceCutoff_le_steps hl hδ n) hp
      change (earlyTerminalPairAt H p).1 = H
      rw [hpair]
      simp only [heq, H, ite_eq_left le_rfl]
  have hbound : μ.real A ≤ μ.real B :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  simpa only [μ, A, B, H, Model.sourceCutoff] using hbound

/-- The paper's strict-cutoff early tree height converges setwise to the
explicit local early tree height under the original epidemic path law. -/
theorem strictEarlyHeight_event_probability_tendsto
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (B : Set ℕ) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      (strictEarlyHeight l δ n ⁻¹' B)) atTop
      (𝓝 (birthParentLaw.real {q | localEarlyHeight l q ∈ B})) := by
  let T := (1 - δ) * fluidExtinctionTime l
  let B' : Set (ℕ × ℕ) := {z | z.2 ∈ B}
  have hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  have hbase := earlyTerminalPairAt_event_probability_tendsto
    rates hl hT hrates B'
  change Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      {p | (earlyTerminalPairAt ⌊T * n⌋₊ p).2 ∈ B}) atTop
    (𝓝 (birthParentLaw.real {q | localEarlyHeight l q ∈ B})) at hbase
  have hbad := strictEarlyHeight_earlyTerminalPairAt_snd_disagreement_tendsto_zero
    rates hl hδ hrates
  have habs : Tendsto (fun n ↦
      |(Model.pathMeasure (rates n) n (2 * n + 1)).real
          (strictEarlyHeight l δ n ⁻¹' B) -
        (Model.pathMeasure (rates n) n (2 * n + 1)).real
          {p | (earlyTerminalPairAt ⌊T * n⌋₊ p).2 ∈ B}|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hbad
    apply Eventually.of_forall
    intro n
    let H := Model.sourceCutoff l δ n
    let μ := Model.pathMeasure (rates n) n (2 * n + 1)
    let A : Set (Model.FinitePath (2 * n + 1)) :=
      strictEarlyHeight l δ n ⁻¹' B
    let C : Set (Model.FinitePath (2 * n + 1)) :=
      {p | (earlyTerminalPairAt H p).2 ∈ B}
    let D : Set (Model.FinitePath (2 * n + 1)) :=
      {p | strictEarlyHeight l δ n p ≠ (earlyTerminalPairAt H p).2}
    have hsub : A ∆ C ⊆ D := by
      intro p hp
      by_contra heq
      simp only [A, C, mem_symmDiff, mem_preimage, mem_ofPred_eq] at hp
      rw [not_ne_iff.mp heq] at hp
      rcases hp with ⟨h, hn⟩ | ⟨h, hn⟩
      · exact hn h
      · exact hn h
    have hbound := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := μ) (show MeasurableSet A from trivial).nullMeasurableSet
      (show MeasurableSet C from trivial).nullMeasurableSet
    exact hbound.trans (measureReal_mono hsub (measure_ne_top _ _))
  have hzero := (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  have hresult := hzero.add hbase
  simpa only [sub_add_cancel, zero_add] using hresult

/-- The paper's real-threshold clipped extinction time is exactly the first
coordinate of the floored stopped pair on every supported path. -/
theorem earlyTerminalPairAt_fst_eq_realThreshold
    {rate : ℝ≥0} {n N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hN : 2 * n + 1 ≤ N) (hH : ⌊T * n⌋₊ ≤ N)
    {p : Model.FinitePath N} (hp : Model.SupportedPath rate n N p.eval) :
    (earlyTerminalPairAt ⌊T * n⌋₊ p).1 =
      if ((2 * p.last.vertices - 1 : ℕ) : ℝ) ≤ T * n then
        2 * p.last.vertices - 1 else 0 := by
  rw [earlyTerminalPairAt_fst_eq_ite_terminalTime hN hH hp]
  have hx : 0 ≤ T * n := mul_nonneg hT (Nat.cast_nonneg n)
  have hcond : 2 * p.last.vertices - 1 ≤ ⌊T * n⌋₊ ↔
      ((2 * p.last.vertices - 1 : ℕ) : ℝ) ≤ T * n :=
    Nat.le_floor_iff hx
  simp only [hcond]

/-- Away from an extinction exactly at the floored cutoff, the paper's
real-threshold survival flag agrees with the source's integer-cutoff flag. -/
theorem sourceSurvivalEvent_iff_realThreshold_of_ne_horizon
    {l δ : ℝ} (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (n : ℕ) {p : Model.FinitePath (2 * n + 1)}
    (hne : 2 * p.last.vertices - 1 ≠ Model.sourceCutoff l δ n) :
    p.last ∈ Model.sourceSurvivalEvent l δ n ↔
      (1 - δ) * fluidExtinctionTime l * n ≤
        ((2 * p.last.vertices - 1 : ℕ) : ℝ) := by
  let x : ℝ := (1 - δ) * fluidExtinctionTime l * n
  let H : ℕ := Model.sourceCutoff l δ n
  let τ : ℕ := 2 * p.last.vertices - 1
  have hx : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hδ.2.le)
      (fluidExtinctionTime_pos hl).le) (Nat.cast_nonneg n)
  have hfloor : (H : ℝ) ≤ x := by
    simpa only [H, Model.sourceCutoff, x] using Nat.floor_le hx
  have hupper : x < (H : ℝ) + 1 := by
    simpa only [H, Model.sourceCutoff, x] using Nat.lt_floor_add_one x
  change H ≤ τ ↔ x ≤ (τ : ℝ)
  constructor
  · intro hle
    have hsucc : H + 1 ≤ τ := by
      have hne' : τ ≠ H := hne
      omega
    have hcast : (H : ℝ) + 1 ≤ (τ : ℝ) := by exact_mod_cast hsucc
    exact hupper.le.trans hcast
  · intro hle
    exact_mod_cast hfloor.trans hle

/-- The real-threshold Bernoulli flag in the TeX lemma and the source's
terminal-state cutoff flag disagree with vanishing probability under the
original full epidemic path law. -/
theorem sourceSurvivalEvent_realThreshold_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      {p | ¬ (p.last ∈ Model.sourceSurvivalEvent l δ n ↔
        (1 - δ) * fluidExtinctionTime l * n ≤
          ((2 * p.last.vertices - 1 : ℕ) : ℝ))})
      atTop (𝓝 0) := by
  have hT : (1 - δ) * fluidExtinctionTime l ∈
      Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  have hboundary := earlyTerminalPairAt_horizon_probability_tendsto_zero
    rates hl hT hrates
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hboundary
  apply Eventually.of_forall
  intro n
  let μ := Model.pathMeasure (rates n) n (2 * n + 1)
  let A : Set (Model.FinitePath (2 * n + 1)) :=
    {p | ¬ (p.last ∈ Model.sourceSurvivalEvent l δ n ↔
      (1 - δ) * fluidExtinctionTime l * n ≤
        ((2 * p.last.vertices - 1 : ℕ) : ℝ))}
  let B : Set (Model.FinitePath (2 * n + 1)) :=
    {p | (earlyTerminalPairAt (Model.sourceCutoff l δ n) p).1 =
      Model.sourceCutoff l δ n}
  have hsub : A ≤ᵐ[μ] B := by
    filter_upwards [Model.ae_supportedPath (rates n) n (2 * n + 1)] with p hp
    intro hbad
    have hτeq : 2 * p.last.vertices - 1 = Model.sourceCutoff l δ n := by
      by_contra hne
      exact hbad
        (sourceSurvivalEvent_iff_realThreshold_of_ne_horizon hl hδ n hne)
    have hfirst := earlyTerminalPairAt_fst_eq_ite_terminalTime
      (rate := rates n) (n := n) (N := 2 * n + 1)
      (H := Model.sourceCutoff l δ n) le_rfl
      (Model.sourceCutoff_le_steps hl hδ n) hp
    change (earlyTerminalPairAt (Model.sourceCutoff l δ n) p).1 =
      Model.sourceCutoff l δ n
    simpa only [hτeq, ite_eq_left le_rfl] using hfirst
  have hbound : μ.real A ≤ μ.real B :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  simpa only [μ, A, B, Model.sourceCutoff] using hbound

/-- The paper's real-threshold indicator agrees asymptotically with the
zero value of the stopped early extinction coordinate. -/
theorem realThreshold_earlyTerminalPairAt_zero_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      {p | ¬ ((1 - δ) * fluidExtinctionTime l * n ≤
          ((2 * p.last.vertices - 1 : ℕ) : ℝ) ↔
        (earlyTerminalPairAt
          ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ p).1 = 0)})
      atTop (𝓝 0) := by
  have hreal := sourceSurvivalEvent_realThreshold_disagreement_tendsto_zero
    rates hl hδ hrates
  have hearly :=
    sourceSurvivalEvent_earlyTerminalPairAt_zero_disagreement_tendsto_zero
      rates hl hδ hrates
  have hsum := hreal.add hearly
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  let R : Set (Model.FinitePath (2 * n + 1)) :=
    {p | ¬ (p.last ∈ Model.sourceSurvivalEvent l δ n ↔
      (1 - δ) * fluidExtinctionTime l * n ≤
        ((2 * p.last.vertices - 1 : ℕ) : ℝ))}
  let E : Set (Model.FinitePath (2 * n + 1)) :=
    {p | ¬ (p.last ∈ Model.sourceSurvivalEvent l δ n ↔
      (earlyTerminalPairAt
        ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ p).1 = 0)}
  have hsub : {p | ¬ ((1 - δ) * fluidExtinctionTime l * n ≤
        ((2 * p.last.vertices - 1 : ℕ) : ℝ) ↔
      (earlyTerminalPairAt
        ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ p).1 = 0)} ⊆
      R ∪ E := by
    intro p hp
    by_cases hr : p.last ∈ Model.sourceSurvivalEvent l δ n ↔
        (1 - δ) * fluidExtinctionTime l * n ≤
          ((2 * p.last.vertices - 1 : ℕ) : ℝ)
    · by_cases he : p.last ∈ Model.sourceSurvivalEvent l δ n ↔
          (earlyTerminalPairAt
            ⌊((1 - δ) * fluidExtinctionTime l) * n⌋₊ p).1 = 0
      · exact (hp (hr.symm.trans he)).elim
      · exact Or.inr he
    · exact Or.inl hr
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (measureReal_union_le R E)

/-- The two coordinates of the paper's early real-threshold statement,
expressed directly from the terminal vertex count of the full path. -/
noncomputable def realThresholdEarlyPair (l δ : ℝ) (n : ℕ)
    (p : Model.FinitePath (2 * n + 1)) : ℕ × Bool :=
  (if ((2 * p.last.vertices - 1 : ℕ) : ℝ) ≤
      (1 - δ) * fluidExtinctionTime l * n then
      2 * p.last.vertices - 1 else 0,
    decide ((1 - δ) * fluidExtinctionTime l * n ≤
      ((2 * p.last.vertices - 1 : ℕ) : ℝ)))

/-- The common-space local limit of the paper's early pair. -/
noncomputable def localEarlyTimeSurvivalPair (l : ℝ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) : ℕ × Bool :=
  (localEarlyExtinctionTime l q.1, decide (q.1 ∈ localSurvival l))

/-- The complete real-threshold early time and survival pair from the TeX
lemma converges setwise to the explicit coupled local pair. -/
theorem realThresholdEarlyPair_event_probability_tendsto
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (B : Set (ℕ × Bool)) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      (realThresholdEarlyPair l δ n ⁻¹' B)) atTop
      (𝓝 (birthParentLaw.real (localEarlyTimeSurvivalPair l ⁻¹' B))) := by
  let T := (1 - δ) * fluidExtinctionTime l
  let f : (ℕ × ℕ) → (ℕ × Bool) :=
    fun z ↦ (z.1, decide (z.1 = 0))
  let B' : Set (ℕ × ℕ) := f ⁻¹' B
  have hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  have hbase := earlyTerminalPairAt_event_probability_tendsto
    rates hl hT hrates B'
  have hlimset : {q : (ℕ → ℝ) × (ℕ → ℝ) |
      (localEarlyExtinctionTime l q.1, localEarlyHeight l q) ∈ B'} =
      localEarlyTimeSurvivalPair l ⁻¹' B := by
    ext q
    have hz := localEarlyExtinctionTime_eq_zero_iff l q.1
    have hpair : f (localEarlyExtinctionTime l q.1, localEarlyHeight l q) =
        localEarlyTimeSurvivalPair l q := by
      apply Prod.ext
      · rfl
      · exact Bool.decide_congr hz
    change f (localEarlyExtinctionTime l q.1, localEarlyHeight l q) ∈ B ↔
      localEarlyTimeSurvivalPair l q ∈ B
    rw [hpair]
  rw [hlimset] at hbase
  have hbad := realThreshold_earlyTerminalPairAt_zero_disagreement_tendsto_zero
    rates hl hδ hrates
  have habs : Tendsto (fun n ↦
      |(Model.pathMeasure (rates n) n (2 * n + 1)).real
          (realThresholdEarlyPair l δ n ⁻¹' B) -
        (Model.pathMeasure (rates n) n (2 * n + 1)).real
          (earlyTerminalPairAt ⌊T * n⌋₊ ⁻¹' B')|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hbad
    apply Eventually.of_forall
    intro n
    let H := Model.sourceCutoff l δ n
    let μ := Model.pathMeasure (rates n) n (2 * n + 1)
    let A : Set (Model.FinitePath (2 * n + 1)) :=
      realThresholdEarlyPair l δ n ⁻¹' B
    let C : Set (Model.FinitePath (2 * n + 1)) :=
      earlyTerminalPairAt H ⁻¹' B'
    let D : Set (Model.FinitePath (2 * n + 1)) :=
      {p | ¬ (T * n ≤ ((2 * p.last.vertices - 1 : ℕ) : ℝ) ↔
        (earlyTerminalPairAt H p).1 = 0)}
    have hsub : (A ∆ C) ≤ᵐ[μ] D := by
      filter_upwards [Model.ae_supportedPath (rates n) n (2 * n + 1)] with p hp
      intro hdiff
      by_cases hs : T * n ≤ ((2 * p.last.vertices - 1 : ℕ) : ℝ) ↔
          (earlyTerminalPairAt H p).1 = 0
      · have hfirst := earlyTerminalPairAt_fst_eq_realThreshold
          (rate := rates n) (n := n) (N := 2 * n + 1)
          hT.1.le le_rfl (Model.sourceCutoff_le_steps hl hδ n) hp
        have hpair : realThresholdEarlyPair l δ n p =
            f (earlyTerminalPairAt H p) := by
          apply Prod.ext
          · change (if ((2 * p.last.vertices - 1 : ℕ) : ℝ) ≤ T * n then
                2 * p.last.vertices - 1 else 0) =
              (earlyTerminalPairAt H p).1
            exact hfirst.symm
          · change decide (T * n ≤ ((2 * p.last.vertices - 1 : ℕ) : ℝ)) =
              decide ((earlyTerminalPairAt H p).1 = 0)
            exact Bool.decide_congr hs
        have hAC : p ∈ A ↔ p ∈ C := by
          change realThresholdEarlyPair l δ n p ∈ B ↔
            f (earlyTerminalPairAt H p) ∈ B
          rw [hpair]
        have hfalse : False := by
          rcases Set.mem_symmDiff.mp hdiff with ⟨ha, hnc⟩ | ⟨hc, hna⟩
          · exact hnc (hAC.mp ha)
          · exact hna (hAC.mpr hc)
        exact hfalse.elim
      · exact hs
    have hbound := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := μ) (show MeasurableSet A from trivial).nullMeasurableSet
      (show MeasurableSet C from trivial).nullMeasurableSet
    have hmono : μ.real (A ∆ C) ≤ μ.real D :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    exact hbound.trans hmono
  have hzero := (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  have hresult := hzero.add hbase
  simpa only [sub_add_cancel, zero_add] using hresult

/-- The local survival bit in the real-threshold limit has exactly the
Bernoulli parameter stated in the paper. -/
theorem localEarlyTimeSurvivalPair_survival_probability_eq
    {l : ℝ} (hl : 1 < l) :
    birthParentLaw.real
      {q | (localEarlyTimeSurvivalPair l q).2 = true} = 1 - 1 / l := by
  have hset : {q : (ℕ → ℝ) × (ℕ → ℝ) |
      (localEarlyTimeSurvivalPair l q).2 = true} =
      Prod.fst ⁻¹' localSurvival l := by
    ext q
    change decide (q.1 ∈ localSurvival l) = true ↔ q.1 ∈ localSurvival l
    exact Bool.decide_iff (q.1 ∈ localSurvival l)
  rw [hset]
  calc
    birthParentLaw.real (Prod.fst ⁻¹' localSurvival l) =
        uniformLaw.real (localSurvival l) := by
      rw [← birthParentLaw_map_fst]
      simp only [Measure.real, Measure.map_apply measurable_fst
        (measurableSet_localSurvival l)]
    _ = 1 - 1 / l := localSurvival_probability_eq hl

/-- Failure of either compact-time fluid estimate when the limiting
trajectory is selected by the exact real-threshold survival event in TeX. -/
def realThresholdJointFluidBad (l δ C ε : ℝ) (n : ℕ) :
    Set (Model.FinitePath (2 * n + 1)) :=
  {p | (∃ t ∈ Icc (0 : ℝ) C,
      ε ≤ |(Model.infectious (p.eval ⌊t * n⌋₊) : ℝ) / n -
        if (1 - δ) * fluidExtinctionTime l * n ≤
            ((2 * p.last.vertices - 1 : ℕ) : ℝ) then
          fluidInfectious l t else 0|) ∨
    (∃ t ∈ Icc (0 : ℝ) (fluidExtinctionTime l),
      ε ≤ |(p.eval ⌊t * n⌋₊).susceptible / (n : ℝ) -
        if (1 - δ) * fluidExtinctionTime l * n ≤
            ((2 * p.last.vertices - 1 : ℕ) : ℝ) then
          fluidSusceptible l t else 1|)}

/-- The paper's two fluid trajectories jointly concentrate under the
original full-path measure, with the mixture chosen by its real-threshold
survival indicator. -/
theorem realThreshold_joint_fluid_compact_time_concentration
    (rates : ℕ → ℝ≥0) {l δ C ε : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      (realThresholdJointFluidBad l δ C ε n)) atTop (𝓝 0) := by
  have hprev := earlyPair_joint_fluid_compact_time_concentration
    rates hl hδ hC hrates hε
  have hdis := realThreshold_earlyTerminalPairAt_zero_disagreement_tendsto_zero
    rates hl hδ hrates
  have hsum := hprev.add hdis
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  let H := Model.sourceCutoff l δ n
  let D : Set (Model.FinitePath (2 * n + 1)) :=
    {p | ¬ ((1 - δ) * fluidExtinctionTime l * n ≤
        ((2 * p.last.vertices - 1 : ℕ) : ℝ) ↔
      (earlyTerminalPairAt H p).1 = 0)}
  have hsub : realThresholdJointFluidBad l δ C ε n ⊆
      earlyPairJointFluidBad l δ C ε n ∪ D := by
    intro p hp
    by_cases hs : (1 - δ) * fluidExtinctionTime l * n ≤
        ((2 * p.last.vertices - 1 : ℕ) : ℝ) ↔
      (earlyTerminalPairAt H p).1 = 0
    · left
      change (∃ t ∈ Icc (0 : ℝ) C,
          ε ≤ |(Model.infectious (p.eval ⌊t * n⌋₊) : ℝ) / n -
            if (1 - δ) * fluidExtinctionTime l * n ≤
                ((2 * p.last.vertices - 1 : ℕ) : ℝ) then
              fluidInfectious l t else 0|) ∨
        (∃ t ∈ Icc (0 : ℝ) (fluidExtinctionTime l),
          ε ≤ |(p.eval ⌊t * n⌋₊).susceptible / (n : ℝ) -
            if (1 - δ) * fluidExtinctionTime l * n ≤
                ((2 * p.last.vertices - 1 : ℕ) : ℝ) then
              fluidSusceptible l t else 1|) at hp
      change (∃ t ∈ Icc (0 : ℝ) C,
          ε ≤ |(Model.infectious (p.eval ⌊t * n⌋₊) : ℝ) / n -
            if (earlyTerminalPairAt H p).1 = 0 then
              fluidInfectious l t else 0|) ∨
        (∃ t ∈ Icc (0 : ℝ) (fluidExtinctionTime l),
          ε ≤ |(p.eval ⌊t * n⌋₊).susceptible / (n : ℝ) -
            if (earlyTerminalPairAt H p).1 = 0 then
              fluidSusceptible l t else 1|)
      by_cases hreal : (1 - δ) * fluidExtinctionTime l * n ≤
          ((2 * p.last.vertices - 1 : ℕ) : ℝ)
      · have hearly : (earlyTerminalPairAt H p).1 = 0 := hs.mp hreal
        simpa only [ite_eq_left hreal, ite_eq_left hearly] using hp
      · have hearly : (earlyTerminalPairAt H p).1 ≠ 0 :=
          fun h ↦ hreal (hs.mpr h)
        simpa only [ite_eq_right hreal, ite_eq_right hearly] using hp
    · right
      simpa only [D, mem_ofPred_eq] using hs
  calc
    (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (realThresholdJointFluidBad l δ C ε n) ≤
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (earlyPairJointFluidBad l δ C ε n) +
      (Model.pathMeasure (rates n) n (2 * n + 1)).real D :=
      (measureReal_mono hsub (measure_ne_top _ _)).trans
        (measureReal_union_le _ _)
    _ = _ := by simp only [D, H, Model.sourceCutoff]

/-- Every event of the paper's real-threshold early pair occurs jointly with
both prescribed compact-time fluid estimates with its limiting local-pair
probability. This is the source's joint early/fluid assertion in event form. -/
theorem realThresholdEarlyPair_and_joint_fluid_good_probability_tendsto
    (rates : ℕ → ℝ≥0) {l δ C ε : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) (B : Set (ℕ × Bool)) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      ((realThresholdEarlyPair l δ n ⁻¹' B) \
        realThresholdJointFluidBad l δ C ε n)) atTop
      (𝓝 (birthParentLaw.real (localEarlyTimeSurvivalPair l ⁻¹' B))) := by
  have hpair := realThresholdEarlyPair_event_probability_tendsto
    rates hl hδ hrates B
  have hbad := realThreshold_joint_fluid_compact_time_concentration
    rates hl hδ hC hrates hε
  have habs : Tendsto (fun n ↦
      |(Model.pathMeasure (rates n) n (2 * n + 1)).real
          ((realThresholdEarlyPair l δ n ⁻¹' B) \
            realThresholdJointFluidBad l δ C ε n) -
        (Model.pathMeasure (rates n) n (2 * n + 1)).real
          (realThresholdEarlyPair l δ n ⁻¹' B)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hbad
    apply Eventually.of_forall
    intro n
    let μ := Model.pathMeasure (rates n) n (2 * n + 1)
    let A : Set (Model.FinitePath (2 * n + 1)) :=
      realThresholdEarlyPair l δ n ⁻¹' B
    let F := realThresholdJointFluidBad l δ C ε n
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

/-- The TeX early-time, survival, and strict early-height coordinates as one
observable of the complete epidemic path. -/
noncomputable def realThresholdEarlyTriple (l δ : ℝ) (n : ℕ)
    (p : Model.FinitePath (2 * n + 1)) : (ℕ × Bool) × ℕ :=
  (realThresholdEarlyPair l δ n p, strictEarlyHeight l δ n p)

noncomputable def localEarlyTriple (l : ℝ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) : (ℕ × Bool) × ℕ :=
  (localEarlyTimeSurvivalPair l q, localEarlyHeight l q)

/-- The paper's three unscaled early coordinates converge jointly and
setwise under the original complete-path law. -/
theorem realThresholdEarlyTriple_event_probability_tendsto
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (B : Set ((ℕ × Bool) × ℕ)) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      (realThresholdEarlyTriple l δ n ⁻¹' B)) atTop
      (𝓝 (birthParentLaw.real (localEarlyTriple l ⁻¹' B))) := by
  let T := (1 - δ) * fluidExtinctionTime l
  let f : (ℕ × ℕ) → ((ℕ × Bool) × ℕ) :=
    fun z ↦ ((z.1, decide (z.1 = 0)), z.2)
  let B' : Set (ℕ × ℕ) := f ⁻¹' B
  have hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  have hbase := earlyTerminalPairAt_event_probability_tendsto
    rates hl hT hrates B'
  have hlimset : {q : (ℕ → ℝ) × (ℕ → ℝ) |
      (localEarlyExtinctionTime l q.1, localEarlyHeight l q) ∈ B'} =
      localEarlyTriple l ⁻¹' B := by
    ext q
    have hz := localEarlyExtinctionTime_eq_zero_iff l q.1
    have htriple : f (localEarlyExtinctionTime l q.1, localEarlyHeight l q) =
        localEarlyTriple l q := by
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · exact Bool.decide_congr hz
      · rfl
    change f (localEarlyExtinctionTime l q.1, localEarlyHeight l q) ∈ B ↔
      localEarlyTriple l q ∈ B
    rw [htriple]
  rw [hlimset] at hbase
  have hflag := realThreshold_earlyTerminalPairAt_zero_disagreement_tendsto_zero
    rates hl hδ hrates
  have hheight := strictEarlyHeight_earlyTerminalPairAt_snd_disagreement_tendsto_zero
    rates hl hδ hrates
  have hsum := hflag.add hheight
  simp only [add_zero] at hsum
  have habs : Tendsto (fun n ↦
      |(Model.pathMeasure (rates n) n (2 * n + 1)).real
          (realThresholdEarlyTriple l δ n ⁻¹' B) -
        (Model.pathMeasure (rates n) n (2 * n + 1)).real
          (earlyTerminalPairAt ⌊T * n⌋₊ ⁻¹' B')|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hsum
    apply Eventually.of_forall
    intro n
    let H := Model.sourceCutoff l δ n
    let μ := Model.pathMeasure (rates n) n (2 * n + 1)
    let A : Set (Model.FinitePath (2 * n + 1)) :=
      realThresholdEarlyTriple l δ n ⁻¹' B
    let C : Set (Model.FinitePath (2 * n + 1)) :=
      earlyTerminalPairAt H ⁻¹' B'
    let Dflag : Set (Model.FinitePath (2 * n + 1)) :=
      {p | ¬ (T * n ≤ ((2 * p.last.vertices - 1 : ℕ) : ℝ) ↔
        (earlyTerminalPairAt H p).1 = 0)}
    let Dheight : Set (Model.FinitePath (2 * n + 1)) :=
      {p | strictEarlyHeight l δ n p ≠ (earlyTerminalPairAt H p).2}
    have hsub : (A ∆ C) ≤ᵐ[μ] (Dflag ∪ Dheight) := by
      filter_upwards [Model.ae_supportedPath (rates n) n (2 * n + 1)] with p hp
      intro hdiff
      by_cases hf : T * n ≤ ((2 * p.last.vertices - 1 : ℕ) : ℝ) ↔
          (earlyTerminalPairAt H p).1 = 0
      · by_cases hh : strictEarlyHeight l δ n p =
            (earlyTerminalPairAt H p).2
        · have hfirst := earlyTerminalPairAt_fst_eq_realThreshold
            (rate := rates n) (n := n) (N := 2 * n + 1)
            hT.1.le le_rfl (Model.sourceCutoff_le_steps hl hδ n) hp
          have htriple : realThresholdEarlyTriple l δ n p =
              f (earlyTerminalPairAt H p) := by
            apply Prod.ext
            · apply Prod.ext
              · change (if ((2 * p.last.vertices - 1 : ℕ) : ℝ) ≤ T * n then
                    2 * p.last.vertices - 1 else 0) =
                  (earlyTerminalPairAt H p).1
                exact hfirst.symm
              · change decide (T * n ≤ ((2 * p.last.vertices - 1 : ℕ) : ℝ)) =
                  decide ((earlyTerminalPairAt H p).1 = 0)
                exact Bool.decide_congr hf
            · exact hh
          have hAC : p ∈ A ↔ p ∈ C := by
            change realThresholdEarlyTriple l δ n p ∈ B ↔
              f (earlyTerminalPairAt H p) ∈ B
            rw [htriple]
          have hfalse : False := by
            rcases Set.mem_symmDiff.mp hdiff with ⟨ha, hnc⟩ | ⟨hc, hna⟩
            · exact hnc (hAC.mp ha)
            · exact hna (hAC.mpr hc)
          exact hfalse.elim
        · exact Or.inr hh
      · exact Or.inl hf
    have hbound := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := μ) (show MeasurableSet A from trivial).nullMeasurableSet
      (show MeasurableSet C from trivial).nullMeasurableSet
    have hmono : μ.real (A ∆ C) ≤ μ.real (Dflag ∪ Dheight) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    exact (hbound.trans hmono).trans (measureReal_union_le Dflag Dheight)
  have hzero := (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  have hresult := hzero.add hbase
  simpa only [sub_add_cancel, zero_add] using hresult

/-- The paper's real-threshold early time, survival indicator, strict early
height, and both compact-time fluid paths satisfy their joint limit in
cylinder-event form under the original complete epidemic law. -/
theorem realThresholdEarlyTriple_and_joint_fluid_good_probability_tendsto
    (rates : ℕ → ℝ≥0) {l δ C ε : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) (B : Set ((ℕ × Bool) × ℕ)) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      ((realThresholdEarlyTriple l δ n ⁻¹' B) \
        realThresholdJointFluidBad l δ C ε n)) atTop
      (𝓝 (birthParentLaw.real (localEarlyTriple l ⁻¹' B))) := by
  have htriple := realThresholdEarlyTriple_event_probability_tendsto
    rates hl hδ hrates B
  have hbad := realThreshold_joint_fluid_compact_time_concentration
    rates hl hδ hC hrates hε
  have habs : Tendsto (fun n ↦
      |(Model.pathMeasure (rates n) n (2 * n + 1)).real
          ((realThresholdEarlyTriple l δ n ⁻¹' B) \
            realThresholdJointFluidBad l δ C ε n) -
        (Model.pathMeasure (rates n) n (2 * n + 1)).real
          (realThresholdEarlyTriple l δ n ⁻¹' B)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hbad
    apply Eventually.of_forall
    intro n
    let μ := Model.pathMeasure (rates n) n (2 * n + 1)
    let A : Set (Model.FinitePath (2 * n + 1)) :=
      realThresholdEarlyTriple l δ n ⁻¹' B
    let F := realThresholdJointFluidBad l δ C ε n
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
  have hresult := hzero.add htriple
  simpa only [sub_add_cancel, zero_add] using hresult


end HeightPaper.CountCoupling
