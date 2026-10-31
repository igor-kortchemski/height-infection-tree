module

public import HeightPaper.Probability.ConditionalOutgrowthProfile
public import HeightPaper.Analysis.OutgrowthScaleChoice
public import HeightPaper.Probability.EpidemicLaplace
public import HeightPaper.Probability.OutgrowthPressure
public import HeightPaper.Probability.SourceSurvival
public import HeightPaper.Model.OutgrowthBins
public import HeightPaper.Model.DepthMeshHeight

/-!
# Conditional height of one epidemic outgrowth profile bin

This instantiates the geometric upper and lower comparisons with actual
epidemic profile and pressure estimates. The conditioning event here is
activity at the cutoff; the source's non-strict survival convention differs
only by an event of vanishing probability.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal Classical

namespace HeightPaper.Model

noncomputable def sourceActiveBinRoots (l x y : ℝ) (n : ℕ)
    (s : State) : Finset ℕ :=
  activeBinRoots s (growthFactor l * Real.exp x * Real.log n)
    (growthFactor l * Real.exp y * Real.log n)

/-- Activity at any fixed interior source cutoff has the surviving mass. -/
theorem sourceCutoff_active_probability_tendsto
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦
      (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
        {s | s.active.Nonempty}) atTop (𝓝 (1 - 1 / l)) := by
  have hT : (1 - δ) * fluidExtinctionTime l ∈
      Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [fluidExtinctionTime_pos hl, hδ.1]
  have hext := evolve_extinction_tendsto_reciprocal rates (sourceCutoff l δ) hl
    hT hrates (tendsto_floor_fraction hT.1.le)
  simp_rw [evolve_active_probability_eq]
  exact tendsto_const_nhds.sub hext

/-- For every sufficiently late cutoff, almost every active cutoff tree has
uniformly small conditional deviation of its selected fresh-outgrowth height
from the manuscript's finite-bin coefficient. -/
theorem eventually_sourceActiveBinOutgrowth_goodStates
    (rates : ℕ → ℝ≥0) {l x y ε : ℝ} (hl : 1 < l)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (hxy : x < y)
    (hε : 0 < ε)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      let μ : ℕ → PMF State := fun n ↦ evolve (rates n) n (sourceCutoff l δ n)
      let K : ℕ → ℕ := fun n ↦ 2 * n + 1 - sourceCutoff l δ n
      let A : ℕ → Set State := fun _ ↦ {s | s.active.Nonempty}
      let E := outgrowthHeightDeviationEvent (sourceActiveBinRoots l x y)
        (profileExponent l x / outgrowthRate l) ε
      Tendsto (continuationGoodThreshold μ rates K A E) atTop (𝓝 0) ∧
      Tendsto (fun n ↦
        (μ n).toMeasure.real (continuationGoodStates μ rates K A E n) /
        (μ n).toMeasure.real (sourceSurvivalEvent l δ n)) atTop (𝓝 1) ∧
      ∀ n, ∀ s ∈ continuationGoodStates μ rates K A E n,
        (continuationLaw (rates n) s (K n)).toMeasure.real (E n s) ≤
          continuationGoodThreshold μ rates K A E n := by
  let f := profileExponent l x
  let c := f / outgrowthRate l
  have hf : 0 < f := profileExponent_pos hl hx.1.le hx.2
  obtain ⟨mU, mL, hmU, hmU1, hmL0, hmL, hscaleU, hscaleL⟩ :=
    exists_outgrowth_comparison_means hl hε (f := f)
  have hmU0 : 0 < mU := (offspringMean_pos hl).trans hmU
  let pU := Branching.successParameter mU hmU0.le
  let pL := Branching.successParameter mL hmL0.le
  have hpU := successParameter_subcritical hmU0 hmU1
  have hpL := successParameter_subcritical hmL0 (hmL.trans (offspringMean_lt_one hl))
  have hpU0 : 0 < (pU : ℝ) := (by norm_num : (0 : ℝ) < 1 / 2).trans hpU.1
  have hpL0 : 0 < (pL : ℝ) := (by norm_num : (0 : ℝ) < 1 / 2).trans hpL.1
  have heqU : Branching.geometricMean pU = mU :=
    Branching.geometricMean_successParameter mU hmU0.le
  have heqL : Branching.geometricMean pL = mL :=
    Branching.geometricMean_successParameter mL hmL0.le
  obtain ⟨L, _, hL, hbarrierTerminal⟩ :=
    exists_terminal_outgrowth_lower_pressure_threshold rates hl hpL0 hpL.2
      (by rw [heqL]; exact hmL) hrates
  obtain ⟨δ₀, hδ₀, hpressureU⟩ :=
    eventually_cutoff_recovery_lower_concentration rates hl hpU0
      (by rw [heqU]; exact hmU) hrates
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ
  have hδ1 : δ ∈ Ioo (0 : ℝ) 1 :=
    ⟨hδ.1, hδ.2.trans (hδ₀.2.trans (by norm_num))⟩
  let μ : ℕ → PMF State := fun n ↦ evolve (rates n) n (sourceCutoff l δ n)
  let K : ℕ → ℕ := fun n ↦ 2 * n + 1 - sourceCutoff l δ n
  let A : ℕ → Set State := fun _ ↦ {s | s.active.Nonempty}
  let E := outgrowthHeightDeviationEvent (sourceActiveBinRoots l x y) c ε
  have hprofile : ∀ a > (0 : ℝ), Tendsto (fun n ↦
      (μ n).toMeasure.real {s | s ∈ A n ∧
        a ≤ |Real.log (selectedRootCount s
          (sourceActiveBinRoots l x y n s)) / Real.log n - f|})
        atTop (𝓝 0) := by
    intro a ha
    simpa only [μ, A, f, sourceActiveBinRoots, selectedRootCount_activeBinRoots,
      Set.mem_ofPred_eq] using
      activeBinCount_log_convergence_of_laplace rates (sourceCutoff l δ)
        hl hx hxy
        (fun t ht ↦ sourceCutoff_activeWeight_log_concentration
          rates hl hδ1 ht hrates) a ha
  have hK : ∀ᶠ n in atTop, ∀ s ∈ (μ n).support,
      s ∈ A n → potential s ≤ K n := by
    apply Eventually.of_forall
    intro n s hs ha
    exact evolve_active_potential_le_remaining hs ha
  have hpressure : Tendsto (fun n ↦ (μ n).toMeasure.real
      {s | s ∈ A n ∧
        1 - (infectionProbability (rates n) s.susceptible : ℝ) < (pU : ℝ)})
        atTop (𝓝 0) := by
    simpa only [μ, A, Set.mem_ofPred_eq] using hpressureU δ hδ
  have hbarrier : Tendsto (fun n ↦
      (continuationSampleLaw (μ n) (rates n) (K n)).toMeasure.real
        {s | s.cutoff ∈ A n ∧ s.final.susceptible < L n}) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hbarrierTerminal
    intro n
    calc
      _ ≤ (continuationSampleLaw (μ n) (rates n) (K n)).toMeasure.real
            {s | s.final.susceptible < L n} :=
          measureReal_mono (fun _ h ↦ h.2) (measure_ne_top _ _)
      _ = _ := by
        change (continuationSampleLaw _ _ _).toMeasure.real
          {s | s.final ∈ {s : State | s.susceptible < L n}} = _
        rw [continuationSampleLaw_final_event, ← evolve_add_continuation,
          Nat.add_sub_of_le (sourceCutoff_le_steps hl hδ1 n)]
  have hA : Tendsto (fun n ↦ (μ n).toMeasure.real (A n))
      atTop (𝓝 (1 - 1 / l)) := by
    simpa only [μ, A] using sourceCutoff_active_probability_tendsto
      rates hl hδ1 hrates
  have hmass : 0 < 1 - 1 / l := by
    have hl0 : 0 < l := by linarith
    have hdiv : 1 / l < 1 := (div_lt_iff₀ hl0).mpr (by linarith)
    linarith
  have hscaleU' : f / (-Real.log (Branching.geometricMean pU)) < c + ε := by
    rw [heqU]
    exact hscaleU
  have hscaleL' : c - ε < f / (-Real.log (Branching.geometricMean pL)) := by
    rw [heqL]
    exact hscaleL
  have hresult := conditionalOutgrowthGoodStates_of_profile μ
    (fun n ↦ evolve_support_finite _ _ _) rates K L
    (sourceActiveBinRoots l x y) A hpU.1 hpU.2 hpL.1 hpL.2
    hf hmass hscaleU' hscaleL' hprofile hK hpressure
    (hL.mono fun _ hn ↦ hn.2) hbarrier hA
  obtain ⟨hθ, hcondA, hpoint⟩ := hresult
  have hS := sourceCutoffState_survival_probability_tendsto
    rates hl hδ1 hrates
  have hAS := hA.div hS hmass.ne'
  have hAS' : Tendsto (fun n ↦
      (μ n).toMeasure.real (A n) /
      (μ n).toMeasure.real (sourceSurvivalEvent l δ n))
      atTop (𝓝 1) := by
    change Tendsto (fun n ↦
      (μ n).toMeasure.real (A n) /
      (μ n).toMeasure.real (sourceSurvivalEvent l δ n))
      atTop (𝓝 ((1 - 1 / l) / (1 - 1 / l))) at hAS
    simpa only [div_self hmass.ne'] using hAS
  have hprod := hcondA.mul hAS'
  have hApos : ∀ᶠ n in atTop, 0 < (μ n).toMeasure.real (A n) :=
    hA.eventually (Ioi_mem_nhds hmass)
  have hcondS : Tendsto (fun n ↦
      (μ n).toMeasure.real (continuationGoodStates μ rates K A E n) /
      (μ n).toMeasure.real (sourceSurvivalEvent l δ n)) atTop (𝓝 1) := by
    simpa only [one_mul] using hprod.congr' (hApos.mono (by
      intro n hn
      change ((μ n).toMeasure.real (continuationGoodStates μ rates K A E n) /
          (μ n).toMeasure.real (A n)) *
        ((μ n).toMeasure.real (A n) /
          (μ n).toMeasure.real (sourceSurvivalEvent l δ n)) = _
      field_simp [hn.ne']))
  exact ⟨hθ, hcondS, hpoint⟩

/-- Good finite-bin cutoff trees are restricted to the actual support, as in
the source's conditional tree law. -/
noncomputable def sourceActiveBinGoodCutoffStates
    (rates : ℕ → ℝ≥0) (l δ x y ε : ℝ) (n : ℕ) : Set State :=
  let μ : ℕ → PMF State := fun k ↦ evolve (rates k) k (sourceCutoff l δ k)
  let K : ℕ → ℕ := fun k ↦ 2 * k + 1 - sourceCutoff l δ k
  let A : ℕ → Set State := fun _ ↦ {s | s.active.Nonempty}
  let E := outgrowthHeightDeviationEvent (sourceActiveBinRoots l x y)
    (profileExponent l x / outgrowthRate l) ε
  continuationGoodStates μ rates K A E n ∩ (μ n).support

/-- The supported good cutoff trees lie inside exact source survival and have
conditional mass tending to one. Their outgrowth-height deviation probability
is bounded uniformly by a threshold tending to zero. -/
theorem eventually_sourceActiveBinGoodCutoffStates_exact
    (rates : ℕ → ℝ≥0) {l x y ε : ℝ} (hl : 1 < l)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (hxy : x < y)
    (hε : 0 < ε)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      let μ : ℕ → PMF State := fun n ↦ evolve (rates n) n (sourceCutoff l δ n)
      let K : ℕ → ℕ := fun n ↦ 2 * n + 1 - sourceCutoff l δ n
      let A : ℕ → Set State := fun _ ↦ {s | s.active.Nonempty}
      let E := outgrowthHeightDeviationEvent (sourceActiveBinRoots l x y)
        (profileExponent l x / outgrowthRate l) ε
      let θ := continuationGoodThreshold μ rates K A E
      let G := sourceActiveBinGoodCutoffStates rates l δ x y ε
      Tendsto θ atTop (𝓝 0) ∧
      Tendsto (fun n ↦
        (μ n).toMeasure.real (G n) /
        (μ n).toMeasure.real (sourceSurvivalEvent l δ n)) atTop (𝓝 1) ∧
      (∀ n, G n ⊆ sourceSurvivalEvent l δ n) ∧
      ∀ n, ∀ s ∈ G n,
        (continuationLaw (rates n) s (K n)).toMeasure.real (E n s) ≤ θ n := by
  obtain ⟨δ₀, hδ₀, hbase⟩ :=
    eventually_sourceActiveBinOutgrowth_goodStates rates hl hx hxy hε hrates
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ
  obtain ⟨hθ, hcond, hpoint⟩ := hbase δ hδ
  let μ : ℕ → PMF State := fun n ↦ evolve (rates n) n (sourceCutoff l δ n)
  let K : ℕ → ℕ := fun n ↦ 2 * n + 1 - sourceCutoff l δ n
  let A : ℕ → Set State := fun _ ↦ {s | s.active.Nonempty}
  let E := outgrowthHeightDeviationEvent (sourceActiveBinRoots l x y)
    (profileExponent l x / outgrowthRate l) ε
  let G := sourceActiveBinGoodCutoffStates rates l δ x y ε
  have hmass (n : ℕ) :
      (μ n).toMeasure.real (G n) =
        (μ n).toMeasure.real
          (continuationGoodStates μ rates K A E n) := by
    apply measureReal_congr
    apply FinitePMF.ae_of_forall_mem_support
    intro s hs
    exact propext ⟨fun h ↦ h.1, fun h ↦ ⟨h, hs⟩⟩
  have hcond' : Tendsto (fun n ↦
      (μ n).toMeasure.real (G n) /
      (μ n).toMeasure.real (sourceSurvivalEvent l δ n)) atTop (𝓝 1) := by
    simpa only [hmass] using hcond
  have hsub (n : ℕ) : G n ⊆ sourceSurvivalEvent l δ n := by
    intro s hs
    have hg : s ∈ continuationGoodStates μ rates K A E n := hs.1
    have hsupp : s ∈ (evolve (rates n) n (sourceCutoff l δ n)).support := hs.2
    exact evolve_active_mem_sourceSurvivalEvent (rates n) n l δ hsupp hg.1
  have hpoint' : ∀ n, ∀ s ∈ G n,
      (continuationLaw (rates n) s (K n)).toMeasure.real (E n s) ≤
        continuationGoodThreshold μ rates K A E n := by
    intro n s hs
    exact hpoint n s hs.1
  exact ⟨hθ, hcond', hsub, hpoint'⟩

end HeightPaper.Model
