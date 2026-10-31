module

public import HeightPaper.Probability.SourceConditionalOutgrowth
public import HeightPaper.Model.LowProfile

/-!
# Source conditional outgrowth theorem for any profile-selected roots

The finite-bin, infinite-tail, and low-bin instances share the same
geometric comparison and conditional good-state extraction. Only their
root-count profile inputs differ.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal Classical

namespace HeightPaper.Model

noncomputable def sourceOutgrowthGoodCutoffStates
    (rates : ℕ → ℝ≥0) (l δ f ε : ℝ)
    (roots : ℕ → State → Finset ℕ) (n : ℕ) : Set State :=
  let μ : ℕ → PMF State := fun k ↦ evolve (rates k) k (sourceCutoff l δ k)
  let K : ℕ → ℕ := fun k ↦ 2 * k + 1 - sourceCutoff l δ k
  let A : ℕ → Set State := fun _ ↦ {s | s.active.Nonempty}
  let E := outgrowthHeightDeviationEvent roots (f / outgrowthRate l) ε
  continuationGoodStates μ rates K A E n ∩ (μ n).support

def sourceOutgrowthConditionalConclusion
    (rates : ℕ → ℝ≥0) (l f ε : ℝ)
    (roots : ℕ → State → Finset ℕ) : Prop :=
  ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
    let μ : ℕ → PMF State := fun n ↦ evolve (rates n) n (sourceCutoff l δ n)
    let K : ℕ → ℕ := fun n ↦ 2 * n + 1 - sourceCutoff l δ n
    let A : ℕ → Set State := fun _ ↦ {s | s.active.Nonempty}
    let E := outgrowthHeightDeviationEvent roots (f / outgrowthRate l) ε
    let θ := continuationGoodThreshold μ rates K A E
    let G := sourceOutgrowthGoodCutoffStates rates l δ f ε roots
    Tendsto θ atTop (𝓝 0) ∧
    Tendsto (fun n ↦
      (μ n).toMeasure.real (G n) /
      (μ n).toMeasure.real (sourceSurvivalEvent l δ n)) atTop (𝓝 1) ∧
    (∀ n, G n ⊆ sourceSurvivalEvent l δ n) ∧
    ∀ n, ∀ s ∈ G n,
      (continuationLaw (rates n) s (K n)).toMeasure.real (E n s) ≤ θ n

def sourceOutgrowthConditionalProbabilityStatement
    (rates : ℕ → ℝ≥0) (l f ε : ℝ)
    (roots : ℕ → State → Finset ℕ) : Prop :=
  ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
    ∀ a > (0 : ℝ),
    let μ : ℕ → PMF State := fun n ↦ evolve (rates n) n (sourceCutoff l δ n)
    let K : ℕ → ℕ := fun n ↦ 2 * n + 1 - sourceCutoff l δ n
    let E := outgrowthHeightDeviationEvent roots (f / outgrowthRate l) ε
    Tendsto (fun n ↦ (μ n).toMeasure.real
      {s | s ∈ sourceSurvivalEvent l δ n ∧
        a ≤ (continuationLaw (rates n) s (K n)).toMeasure.real (E n s)})
      atTop (𝓝 0)

/-- The actual source conditional conclusion from a profile law for the
selected roots, with no abstract pressure or barrier assumptions remaining. -/
theorem eventually_sourceOutgrowthGoodCutoffStates_of_profile
    (rates : ℕ → ℝ≥0) {l f ε : ℝ} (hl : 1 < l)
    (hf : 0 < f) (hε : 0 < ε)
    (roots : ℕ → State → Finset ℕ)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hprofile : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ a > (0 : ℝ),
      Tendsto (fun n ↦
        (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
          {s | s.active.Nonempty ∧
            a ≤ |Real.log (selectedRootCount s (roots n s)) / Real.log n - f|})
        atTop (𝓝 0)) :
    sourceOutgrowthConditionalConclusion rates l f ε roots := by
  unfold sourceOutgrowthConditionalConclusion
  let c := f / outgrowthRate l
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
  let E := outgrowthHeightDeviationEvent roots c ε
  let G := sourceOutgrowthGoodCutoffStates rates l δ f ε roots
  have hprofile' : ∀ a > (0 : ℝ), Tendsto (fun n ↦
      (μ n).toMeasure.real {s | s ∈ A n ∧
        a ≤ |Real.log (selectedRootCount s (roots n s)) / Real.log n - f|})
        atTop (𝓝 0) := by
    simpa only [μ, A, Set.mem_ofPred_eq] using hprofile δ hδ1
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
    (fun n ↦ evolve_support_finite _ _ _) rates K L roots A
    hpU.1 hpU.2 hpL.1 hpL.2 hf hmass hscaleU' hscaleL'
    hprofile' hK hpressure (hL.mono fun _ hn ↦ hn.2) hbarrier hA
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
  have hmeasureG (n : ℕ) :
      (μ n).toMeasure.real (G n) =
        (μ n).toMeasure.real
          (continuationGoodStates μ rates K A E n) := by
    apply measureReal_congr
    apply FinitePMF.ae_of_forall_mem_support
    intro s hs
    exact propext ⟨fun h ↦ h.1, fun h ↦ ⟨h, hs⟩⟩
  have hcondG : Tendsto (fun n ↦
      (μ n).toMeasure.real (G n) /
      (μ n).toMeasure.real (sourceSurvivalEvent l δ n)) atTop (𝓝 1) := by
    simpa only [hmeasureG] using hcondS
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
  exact ⟨hθ, hcondG, hsub, hpoint'⟩

/-- The finite-upper-endpoint clause in the common conditional formulation. -/
theorem eventually_sourceActiveBinOutgrowth_goodStates_general
    (rates : ℕ → ℝ≥0) {l x y ε : ℝ} (hl : 1 < l)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (hxy : x < y)
    (hε : 0 < ε)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    sourceOutgrowthConditionalConclusion rates l
      (profileExponent l x) ε (sourceActiveBinRoots l x y) := by
  apply eventually_sourceOutgrowthGoodCutoffStates_of_profile rates hl
    (profileExponent_pos hl hx.1.le hx.2) hε
    (sourceActiveBinRoots l x y) hrates
  intro δ hδ a ha
  simpa only [sourceActiveBinRoots, selectedRootCount_activeBinRoots,
    Set.mem_ofPred_eq] using
    activeBinCount_log_convergence_of_laplace rates (sourceCutoff l δ)
      hl hx hxy
      (fun t ht ↦ sourceCutoff_activeWeight_log_concentration
        rates hl hδ ht hrates) a ha

noncomputable def sourceActiveTailRoots (l x : ℝ) (n : ℕ)
    (s : State) : Finset ℕ :=
  activeTailRoots s (growthFactor l * Real.exp x * Real.log n)

/-- The infinite-upper-endpoint clause of the paper's dangling-tree lemma,
with the exact non-strict source survival conditioning. -/
theorem eventually_sourceActiveTailOutgrowth_goodStates
    (rates : ℕ → ℝ≥0) {l x ε : ℝ} (hl : 1 < l)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (hε : 0 < ε)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    sourceOutgrowthConditionalConclusion rates l
      (profileExponent l x) ε (sourceActiveTailRoots l x) := by
  apply eventually_sourceOutgrowthGoodCutoffStates_of_profile rates hl
    (profileExponent_pos hl hx.1.le hx.2) hε
    (sourceActiveTailRoots l x) hrates
  intro δ hδ a ha
  simpa only [sourceActiveTailRoots, selectedRootCount_activeTailRoots,
    Set.mem_ofPred_eq] using
    activeTailCount_log_convergence_of_laplace rates (sourceCutoff l δ)
      hl hx
      (fun t ht ↦ sourceCutoff_activeWeight_log_concentration
        rates hl hδ ht hrates) a ha

noncomputable def sourceActiveLowRoots (l x : ℝ) (n : ℕ)
    (s : State) : Finset ℕ :=
  activeLowBinRoots s (growthFactor l * Real.exp x * Real.log n)

/-- The low-depth clause of the paper's dangling-tree lemma, with its
coefficient one and exact non-strict source survival conditioning. -/
theorem eventually_sourceActiveLowOutgrowth_goodStates
    (rates : ℕ → ℝ≥0) {l x ε : ℝ} (hl : 1 < l)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (hε : 0 < ε)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    sourceOutgrowthConditionalConclusion rates l 1 ε
      (sourceActiveLowRoots l x) := by
  apply eventually_sourceOutgrowthGoodCutoffStates_of_profile rates hl
    (by norm_num) hε (sourceActiveLowRoots l x) hrates
  intro δ hδ a ha
  have hT : (1 - δ) * fluidExtinctionTime l ∈
      Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [fluidExtinctionTime_pos hl, hδ.1]
  simpa only [sourceActiveLowRoots, selectedRootCount_activeLowBinRoots,
    Set.mem_ofPred_eq] using
    activeLowBinCount_log_convergence_of_laplace rates (sourceCutoff l δ)
      hl hT hx hrates (tendsto_floor_fraction hT.1.le)
      (fun t ht ↦ sourceCutoff_activeWeight_log_concentration
        rates hl hδ ht hrates) a ha

/-- All three dangling-tree height clauses, for a finite positive-depth bin,
the infinite tail, and the low-depth bin, on the actual cutoff-state law. -/
theorem source_dangling_all_conditional
    (rates : ℕ → ℝ≥0) {l x y ε : ℝ} (hl : 1 < l)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (hxy : x < y)
    (hε : 0 < ε)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    sourceOutgrowthConditionalConclusion rates l
        (profileExponent l x) ε (sourceActiveBinRoots l x y) ∧
      sourceOutgrowthConditionalConclusion rates l
        (profileExponent l x) ε (sourceActiveTailRoots l x) ∧
      sourceOutgrowthConditionalConclusion rates l 1 ε
        (sourceActiveLowRoots l x) := by
  exact ⟨eventually_sourceActiveBinOutgrowth_goodStates_general
    rates hl hx hxy hε hrates,
    eventually_sourceActiveTailOutgrowth_goodStates rates hl hx hε hrates,
    eventually_sourceActiveLowOutgrowth_goodStates rates hl hx hε hrates⟩

/-- The supported good-state formulation implies the exact conditional
convergence-in-probability tail event used in `lem:dangling`. -/
theorem sourceOutgrowthConditionalConclusion_probability
    (rates : ℕ → ℝ≥0) {l f ε : ℝ} (hl : 1 < l)
    (roots : ℕ → State → Finset ℕ)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hgood : sourceOutgrowthConditionalConclusion rates l f ε roots) :
    sourceOutgrowthConditionalProbabilityStatement rates l f ε roots := by
  unfold sourceOutgrowthConditionalProbabilityStatement
  obtain ⟨δ₀, hδ₀, h⟩ := hgood
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ a ha
  obtain ⟨hθ, hratio, hGS, hpoint⟩ := h δ hδ
  have hδ1 : δ ∈ Ioo (0 : ℝ) 1 :=
    ⟨hδ.1, hδ.2.trans (hδ₀.2.trans (by norm_num))⟩
  let μ : ℕ → PMF State := fun n ↦ evolve (rates n) n (sourceCutoff l δ n)
  let K : ℕ → ℕ := fun n ↦ 2 * n + 1 - sourceCutoff l δ n
  let A : ℕ → Set State := fun _ ↦ {s | s.active.Nonempty}
  let E := outgrowthHeightDeviationEvent roots (f / outgrowthRate l) ε
  let G := sourceOutgrowthGoodCutoffStates rates l δ f ε roots
  let S : ℕ → Set State := sourceSurvivalEvent l δ
  have hS : Tendsto (fun n ↦ (μ n).toMeasure.real (S n))
      atTop (𝓝 (1 - 1 / l)) := by
    simpa only [μ, S] using
      sourceCutoffState_survival_probability_tendsto rates hl hδ1 hrates
  have hpos : 0 < 1 - 1 / l := by
    have hl0 : 0 < l := by linarith
    have hdiv : 1 / l < 1 := (div_lt_iff₀ hl0).mpr (by linarith)
    linarith
  have hG : Tendsto (fun n ↦ (μ n).toMeasure.real (G n))
      atTop (𝓝 (1 - 1 / l)) := by
    have hprod := hratio.mul hS
    simpa only [one_mul] using hprod.congr' (hS.eventually (Ioi_mem_nhds hpos) |>.mono (by
      intro n hn
      change ((μ n).toMeasure.real (G n) / (μ n).toMeasure.real (S n)) *
          (μ n).toMeasure.real (S n) = (μ n).toMeasure.real (G n)
      field_simp [hn.ne']))
  have hmiss : Tendsto (fun n ↦ (μ n).toMeasure.real (S n \ G n))
      atTop (𝓝 0) := by
    have hdiff := hS.sub hG
    simpa only [sub_self] using hdiff.congr' (Eventually.of_forall (by
      intro n
      have hsd := measureReal_sdiff (μ := (μ n).toMeasure)
        (hGS n) (show MeasurableSet (G n) from trivial)
        (measure_ne_top _ _)
      linarith))
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hmiss
  filter_upwards [hθ.eventually (Iio_mem_nhds ha)] with n hn
  apply measureReal_mono (μ := (μ n).toMeasure) ?_ (measure_ne_top _ _)
  intro s hs
  refine ⟨hs.1, ?_⟩
  intro hg
  have hh := hpoint n s hg
  linarith [hs.2]

/-- The three displayed convergence-in-probability assertions of
`lem:dangling`, with finite and infinite upper endpoints and the low bin. -/
theorem source_dangling_all_probability
    (rates : ℕ → ℝ≥0) {l x y ε : ℝ} (hl : 1 < l)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (hxy : x < y)
    (hε : 0 < ε)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    sourceOutgrowthConditionalProbabilityStatement rates l
        (profileExponent l x) ε (sourceActiveBinRoots l x y) ∧
      sourceOutgrowthConditionalProbabilityStatement rates l
        (profileExponent l x) ε (sourceActiveTailRoots l x) ∧
      sourceOutgrowthConditionalProbabilityStatement rates l 1 ε
        (sourceActiveLowRoots l x) := by
  obtain ⟨hbin, htail, hlow⟩ :=
    source_dangling_all_conditional rates hl hx hxy hε hrates
  exact ⟨sourceOutgrowthConditionalConclusion_probability rates hl
      (sourceActiveBinRoots l x y) hrates hbin,
    sourceOutgrowthConditionalConclusion_probability rates hl
      (sourceActiveTailRoots l x) hrates htail,
    sourceOutgrowthConditionalConclusion_probability rates hl
      (sourceActiveLowRoots l x) hrates hlow⟩

end HeightPaper.Model
