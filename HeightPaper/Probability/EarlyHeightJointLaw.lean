module

public import HeightPaper.Probability.EarlyRealThresholdLaw
public import HeightPaper.Probability.SourceWeakProfile
public import HeightPaper.Probability.EarlyExtinctionTightness

/-!
# The logarithmic preterminal height in the joint fluid limit

The source's surviving height coefficient and the extinct-branch height
estimate are assembled at the same cutoff and on the same full epidemic path
as the real-threshold early variables and fluid trajectories.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal symmDiff Classical

namespace HeightPaper.CountCoupling

/-- After extinction strictly before the source cutoff, the cutoff state is
the terminal state on every supported full epidemic path. -/
theorem eval_sourceCutoff_eq_last_of_not_sourceSurvival
    {rate : ℝ≥0} {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (n : ℕ)
    {p : Model.FinitePath (2 * n + 1)}
    (hp : Model.SupportedPath rate n (2 * n + 1) p.eval)
    (hnot : p.last ∉ Model.sourceSurvivalEvent l δ n) :
    p.eval (Model.sourceCutoff l δ n) = p.last := by
  let N := 2 * n + 1
  let H := Model.sourceCutoff l δ n
  let τ := 2 * (p.eval N).vertices - 1
  have hτ : τ = 2 * p.last.vertices - 1 := by
    simp only [τ, N, Model.FinitePath.eval_last]
  have hfirst := hp.first_extinction le_rfl
  change 0 < τ ∧ τ ≤ N ∧ (p.eval τ).active = ∅ ∧
    ∀ k < τ, (p.eval k).active.Nonempty at hfirst
  have hτH : τ < H := by
    have hn : ¬ H ≤ τ := by
      intro h
      apply hnot
      change H ≤ 2 * p.last.vertices - 1
      simpa only [hτ] using h
    omega
  have hHstate := hp.absorbed_stable hτH.le
    (Model.sourceCutoff_le_steps hl hδ n) hfirst.2.2.1
  have hNstate := hp.absorbed_stable hfirst.2.1 le_rfl hfirst.2.2.1
  have hlast : p.last = p.eval τ := by
    simpa only [N, Model.FinitePath.eval_last] using hNstate
  exact hHstate.trans hlast.symm

/-- The cutoff tree height divided by `log n` is negligible on the source's
early-extinction branch, under the original complete-path law. -/
theorem sourceExtinction_cutoff_height_div_log_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ ε : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      {p | p.last ∉ Model.sourceSurvivalEvent l δ n ∧
        ε ≤ |(Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
          Real.log n|}) atTop (𝓝 0) := by
  have hterminal := Model.sourceExtinction_height_div_log_tendsto_zero
    rates hl hδ hrates hε
  apply hterminal.congr'
  apply Eventually.of_forall
  intro n
  let μ := Model.pathMeasure (rates n) n (2 * n + 1)
  let S := Model.sourceSurvivalEvent l δ n
  let A : Set (Model.FinitePath (2 * n + 1)) :=
    {p | p.last ∉ S ∧
      ε ≤ |(Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) / Real.log n|}
  let C : Set (Model.FinitePath (2 * n + 1)) :=
    {p | p.last ∉ S ∧ ε ≤ |(Model.height p.last : ℝ) / Real.log n|}
  let D : Set Model.State :=
    {s | s ∉ S ∧ ε ≤ |(Model.height s : ℝ) / Real.log n|}
  have hAE : μ.real A = μ.real C := by
    apply measureReal_congr
    filter_upwards [Model.ae_supportedPath (rates n) n (2 * n + 1)] with p hp
    apply propext
    change (p.last ∉ S ∧
      ε ≤ |(Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) / Real.log n|) ↔
      (p.last ∉ S ∧ ε ≤ |(Model.height p.last : ℝ) / Real.log n|)
    by_cases hs : p.last ∈ S
    · simp only [hs, not_true_eq_false, false_and]
    · rw [eval_sourceCutoff_eq_last_of_not_sourceSurvival hl hδ n hp hs]
  have hLaw := Model.pathMeasure_event_at (rates n) n (2 * n + 1)
    (2 * n + 1) le_rfl D
  have hC : μ.real C = (Model.terminalStateMeasure (rates n) n).real D := by
    simpa only [μ, C, D, S, Model.terminalStateMeasure,
      Model.FinitePath.eval_last, mem_ofPred_eq] using hLaw
  calc
    (Model.terminalStateMeasure (rates n) n).real D = μ.real C := hC.symm
    _ = μ.real A := hAE.symm

/-- Failure of the two-branch logarithmic preterminal-height estimate, with
the branch chosen by the source terminal-state survival event. -/
def sourceHeightLogBad (l δ ε : ℝ) (n : ℕ) :
    Set (Model.FinitePath (2 * n + 1)) :=
  {p | ε ≤ |(Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
      Real.log n -
    if p.last ∈ Model.sourceSurvivalEvent l δ n then
      growthFactor l * Real.exp (profileRoot l) else 0|}

/-- The preterminal tree height divided by `log n` concentrates jointly on
the extinct and surviving branches under the complete epidemic path law. -/
theorem sourceHeightLogBad_probability_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ ε : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      (sourceHeightLogBad l δ ε n)) atTop (𝓝 0) := by
  have hsurv : Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | p.last ∈ Model.sourceSurvivalEvent l δ n ∧
          ε ≤ |(Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
            Real.log n - growthFactor l * Real.exp (profileRoot l)|})
      atTop (𝓝 0) := by
    simpa only [Model.FinitePath.eval_last] using
      Model.sourceCutoff_height_log_concentration rates hl hδ hrates ε hε
  have hext := sourceExtinction_cutoff_height_div_log_tendsto_zero
    rates hl hδ hrates hε
  have hsum := hsurv.add hext
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  let S := Model.sourceSurvivalEvent l δ n
  let X : Set (Model.FinitePath (2 * n + 1)) :=
    {p | p.last ∈ S ∧
      ε ≤ |(Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
        Real.log n - growthFactor l * Real.exp (profileRoot l)|}
  let Y : Set (Model.FinitePath (2 * n + 1)) :=
    {p | p.last ∉ S ∧
      ε ≤ |(Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) / Real.log n|}
  have hsub : sourceHeightLogBad l δ ε n ⊆ X ∪ Y := by
    intro p hp
    by_cases hs : p.last ∈ S
    · left
      refine ⟨hs, ?_⟩
      simpa only [sourceHeightLogBad, mem_ofPred_eq, S,
        ite_eq_left hs] using hp
    · right
      refine ⟨hs, ?_⟩
      simpa only [sourceHeightLogBad, mem_ofPred_eq, S,
        ite_eq_right hs, sub_zero] using hp
  calc
    (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (sourceHeightLogBad l δ ε n) ≤
      (Model.pathMeasure (rates n) n (2 * n + 1)).real X +
        (Model.pathMeasure (rates n) n (2 * n + 1)).real Y :=
      (measureReal_mono hsub (measure_ne_top _ _)).trans
        (measureReal_union_le _ _)
    _ = _ := by simp only [X, Y, S]

/-- The logarithmic preterminal-height failure event with the branch chosen
by the paper's exact real-threshold survival indicator. -/
def realThresholdHeightLogBad (l δ ε : ℝ) (n : ℕ) :
    Set (Model.FinitePath (2 * n + 1)) :=
  {p | ε ≤ |(Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
      Real.log n -
    if (1 - δ) * fluidExtinctionTime l * n ≤
        ((2 * p.last.vertices - 1 : ℕ) : ℝ) then
      growthFactor l * Real.exp (profileRoot l) else 0|}

theorem realThresholdHeightLogBad_probability_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ ε : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      (realThresholdHeightLogBad l δ ε n)) atTop (𝓝 0) := by
  have hsource := sourceHeightLogBad_probability_tendsto_zero
    rates hl hδ hrates hε
  have hdis := sourceSurvivalEvent_realThreshold_disagreement_tendsto_zero
    rates hl hδ hrates
  have hsum := hsource.add hdis
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  let D : Set (Model.FinitePath (2 * n + 1)) :=
    {p | ¬ (p.last ∈ Model.sourceSurvivalEvent l δ n ↔
      (1 - δ) * fluidExtinctionTime l * n ≤
        ((2 * p.last.vertices - 1 : ℕ) : ℝ))}
  have hsub : realThresholdHeightLogBad l δ ε n ⊆
      sourceHeightLogBad l δ ε n ∪ D := by
    intro p hp
    by_cases hs : p.last ∈ Model.sourceSurvivalEvent l δ n ↔
        (1 - δ) * fluidExtinctionTime l * n ≤
          ((2 * p.last.vertices - 1 : ℕ) : ℝ)
    · left
      change ε ≤ |(Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
        Real.log n -
          if (1 - δ) * fluidExtinctionTime l * n ≤
              ((2 * p.last.vertices - 1 : ℕ) : ℝ) then
            growthFactor l * Real.exp (profileRoot l) else 0| at hp
      change ε ≤ |(Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
        Real.log n -
          if p.last ∈ Model.sourceSurvivalEvent l δ n then
            growthFactor l * Real.exp (profileRoot l) else 0|
      by_cases hreal : (1 - δ) * fluidExtinctionTime l * n ≤
          ((2 * p.last.vertices - 1 : ℕ) : ℝ)
      · have hsrc : p.last ∈ Model.sourceSurvivalEvent l δ n := hs.mpr hreal
        simpa only [ite_eq_left hreal, ite_eq_left hsrc] using hp
      · have hsrc : p.last ∉ Model.sourceSurvivalEvent l δ n :=
          fun h ↦ hreal (hs.mp h)
        simpa only [ite_eq_right hreal, ite_eq_right hsrc] using hp
    · right
      simpa only [D, mem_ofPred_eq] using hs
  calc
    (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (realThresholdHeightLogBad l δ ε n) ≤
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        (sourceHeightLogBad l δ ε n) +
      (Model.pathMeasure (rates n) n (2 * n + 1)).real D :=
      (measureReal_mono hsub (measure_ne_top _ _)).trans
        (measureReal_union_le _ _)
    _ = _ := by simp only [D]

/-- The real-threshold early time, survival bit, strict early height, both
compact-time fluid paths, and logarithmic preterminal height satisfy the
paper's joint limit in cylinder-and-tube event form. The local early height
remains an explicit common-space random variable here. -/
theorem realThresholdEarlyTriple_fluid_height_joint_good_probability_tendsto
    (rates : ℕ → ℝ≥0) {l δ C ε η : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) (hη : 0 < η)
    (B : Set ((ℕ × Bool) × ℕ)) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      ((realThresholdEarlyTriple l δ n ⁻¹' B) \
        (realThresholdJointFluidBad l δ C ε n ∪
          realThresholdHeightLogBad l δ η n))) atTop
      (𝓝 (birthParentLaw.real (localEarlyTriple l ⁻¹' B))) := by
  have hbase := realThresholdEarlyTriple_and_joint_fluid_good_probability_tendsto
    rates hl hδ hC hrates hε B
  have hbad := realThresholdHeightLogBad_probability_tendsto_zero
    rates hl hδ hrates hη
  have habs : Tendsto (fun n ↦
      |(Model.pathMeasure (rates n) n (2 * n + 1)).real
          ((realThresholdEarlyTriple l δ n ⁻¹' B) \
            (realThresholdJointFluidBad l δ C ε n ∪
              realThresholdHeightLogBad l δ η n)) -
        (Model.pathMeasure (rates n) n (2 * n + 1)).real
          ((realThresholdEarlyTriple l δ n ⁻¹' B) \
            realThresholdJointFluidBad l δ C ε n)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hbad
    apply Eventually.of_forall
    intro n
    let μ := Model.pathMeasure (rates n) n (2 * n + 1)
    let A : Set (Model.FinitePath (2 * n + 1)) :=
      (realThresholdEarlyTriple l δ n ⁻¹' B) \
        realThresholdJointFluidBad l δ C ε n
    let F := realThresholdHeightLogBad l δ η n
    have hset : (realThresholdEarlyTriple l δ n ⁻¹' B) \
        (realThresholdJointFluidBad l δ C ε n ∪ F) = A \ F := by
      ext p
      simp only [A, Set.mem_sdiff, mem_union, mem_preimage]
      tauto
    rw [hset]
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
  have hresult := hzero.add hbase
  simpa only [sub_add_cancel, zero_add] using hresult


end HeightPaper.CountCoupling
