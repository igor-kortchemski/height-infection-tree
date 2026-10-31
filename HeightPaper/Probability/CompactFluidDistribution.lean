module

public import HeightPaper.Probability.EarlyHeightJointLaw
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Compact-time weak convergence of both fluid trajectories

The type `CompactFluidPath T` carries the topology of uniform convergence on
`[0,T]`. It permits the actual floor-time epidemic paths, which are step
functions, as well as their continuous limits.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal UniformConvergence Classical

namespace HeightPaper.CountCoupling

abbrev CompactFluidPath (T : ℝ) := UniformOnFun ℝ ℝ {Icc (0 : ℝ) T}

noncomputable instance (T : ℝ) : MeasurableSpace (CompactFluidPath T) := borel _

/-- A pair of paths, with its Borel σ-algebra for the joint uniform topology. -/
structure CompactFluidPair (C T : ℝ) where
  infectious : CompactFluidPath C
  susceptible : CompactFluidPath T

noncomputable instance (C T : ℝ) : PseudoEMetricSpace (CompactFluidPair C T) :=
  PseudoEMetricSpace.induced (fun x ↦ (x.infectious, x.susceptible)) inferInstance

noncomputable instance (C T : ℝ) : MeasurableSpace (CompactFluidPair C T) := borel _

instance (C T : ℝ) : BorelSpace (CompactFluidPair C T) := ⟨rfl⟩

private theorem CompactFluidPair.edist_eq {C T : ℝ}
    (x y : CompactFluidPair C T) :
    edist x y = max (edist x.infectious y.infectious)
      (edist x.susceptible y.susceptible) := rfl

private theorem compactFluidPath_edist_le {T ε : ℝ} (_hε : 0 ≤ ε)
    {f g : ℝ → ℝ} (h : ∀ t ∈ Icc (0 : ℝ) T, |f t - g t| ≤ ε) :
    edist (UniformOnFun.ofFun {Icc (0 : ℝ) T} f)
      (UniformOnFun.ofFun {Icc (0 : ℝ) T} g) ≤ ENNReal.ofReal ε := by
  rw [UniformOnFun.edist_le]
  intro t ht
  simp only [sUnion_singleton, UniformOnFun.toFun_ofFun] at ht ⊢
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal (h t ht)

/-- The two floor-time paths, regarded as random functions with the topology
of uniform convergence on their respective fixed compact intervals. -/
noncomputable def compactFluidPaths (l C : ℝ) (n : ℕ)
    (p : Model.FinitePath (2 * n + 1)) :
    CompactFluidPair C (fluidExtinctionTime l) :=
  ⟨UniformOnFun.ofFun {Icc (0 : ℝ) C}
      (fun t ↦ (Model.infectious (p.eval ⌊t * n⌋₊) : ℝ) / n),
   UniformOnFun.ofFun {Icc (0 : ℝ) (fluidExtinctionTime l)}
      (fun t ↦ (p.eval ⌊t * n⌋₊).susceptible / (n : ℝ))⟩

/-- The two deterministic fluid branches, selected by the local survival
event on the common birth and parent uniform space. -/
noncomputable def localCompactFluidPaths (l C : ℝ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) :
    CompactFluidPair C (fluidExtinctionTime l) :=
  ⟨UniformOnFun.ofFun {Icc (0 : ℝ) C}
      (fun t ↦ if q.1 ∈ localSurvival l then fluidInfectious l t else 0),
   UniformOnFun.ofFun {Icc (0 : ℝ) (fluidExtinctionTime l)}
      (fun t ↦ if q.1 ∈ localSurvival l then fluidSusceptible l t else 1)⟩

private theorem measurable_localCompactFluidPaths (l C : ℝ) :
    Measurable (localCompactFluidPaths l C) := by
  have hS : MeasurableSet {q : (ℕ → ℝ) × (ℕ → ℝ) | q.1 ∈ localSurvival l} :=
    (measurableSet_localSurvival l).preimage measurable_fst
  have hEq : localCompactFluidPaths l C =
      fun q ↦ if q.1 ∈ localSurvival l then
        ⟨UniformOnFun.ofFun {Icc (0 : ℝ) C} (fluidInfectious l),
         UniformOnFun.ofFun {Icc (0 : ℝ) (fluidExtinctionTime l)}
           (fluidSusceptible l)⟩
      else
        ⟨UniformOnFun.ofFun {Icc (0 : ℝ) C} (fun _ ↦ 0),
         UniformOnFun.ofFun {Icc (0 : ℝ) (fluidExtinctionTime l)}
           (fun _ ↦ 1)⟩ := by
    funext q
    by_cases hq : q.1 ∈ localSurvival l <;>
      simp [localCompactFluidPaths, hq]
  rw [hEq]
  exact Measurable.ite hS measurable_const measurable_const

private theorem compactFluidPaths_edist_le_of_not_bad (a l C ε : ℝ)
    (hε : 0 ≤ ε) (n : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ))
    (hnot : q ∉ localJointFluidBad a l C ε n) :
    edist
      (compactFluidPaths l C n (coupledTreeHistory a n (2 * n + 1) q))
      (localCompactFluidPaths l C q) ≤ ENNReal.ofReal ε := by
  have hi (t : ℝ) (ht : t ∈ Icc (0 : ℝ) C) :
      |(Model.infectious ((coupledTreeHistory a n (2 * n + 1) q).eval
          ⌊t * n⌋₊) : ℝ) / n -
        (if q.1 ∈ localSurvival l then fluidInfectious l t else 0)| ≤ ε := by
    by_contra hh
    exact hnot (Or.inl ⟨t, ht, le_of_lt (lt_of_not_ge hh)⟩)
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (fluidExtinctionTime l)) :
      |((coupledTreeHistory a n (2 * n + 1) q).eval
          ⌊t * n⌋₊).susceptible / (n : ℝ) -
        (if q.1 ∈ localSurvival l then fluidSusceptible l t else 1)| ≤ ε := by
    by_contra hh
    exact hnot (Or.inr ⟨t, ht, le_of_lt (lt_of_not_ge hh)⟩)
  have hI := compactFluidPath_edist_le hε hi
  have hS := compactFluidPath_edist_le hε hs
  simpa only [compactFluidPaths, localCompactFluidPaths,
    CompactFluidPair.edist_eq, max_le_iff] using And.intro hI hS

/-- On the common birth and parent uniform space, both full trajectories
converge jointly in measure for the two compact time intervals. -/
theorem coupled_compactFluidPaths_tendstoInMeasure
    (rates : ℕ → ℝ≥0) {l δ C : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    TendstoInMeasure birthParentLaw
      (fun n q ↦ compactFluidPaths l C n
        (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q))
      atTop (localCompactFluidPaths l C) := by
  apply tendstoInMeasure_of_ne_top
  intro ε hε hεtop
  let r : ℝ := ε.toReal
  have hr : 0 < r := ENNReal.toReal_pos hε.ne' hεtop
  have hsmall : 0 < r / 2 := half_pos hr
  have hbad := coupled_local_joint_fluid_compact_time_concentration
    rates hl hδ hC hrates hsmall
  have hbadE : Tendsto (fun n ↦ birthParentLaw
      (localJointFluidBad ((rates n : ℝ) * n) l C (r / 2) n))
      atTop (𝓝 0) := by
    apply (ENNReal.tendsto_toReal_zero_iff (fun n ↦ measure_ne_top _ _)).mp
    simpa only [Measure.real] using hbad
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbadE
  · intro n
    exact bot_le
  · intro n
    apply measure_mono
    intro q hq
    by_contra hnot
    have hle := compactFluidPaths_edist_le_of_not_bad
      ((rates n : ℝ) * n) l C (r / 2) hsmall.le n q hnot
    have hlt : ENNReal.ofReal (r / 2) < ε := by
      rw [← ENNReal.ofReal_toReal hεtop]
      exact (ENNReal.ofReal_lt_ofReal_iff hr).2 (half_lt_self hr)
    exact (not_le.mpr (hle.trans_lt hlt)) hq

theorem coupled_compactFluidPaths_tendstoInDistribution
    (rates : ℕ → ℝ≥0) {l δ C : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    TendstoInDistribution
      (fun n q ↦ compactFluidPaths l C n
        (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q))
      atTop (localCompactFluidPaths l C)
      (fun _ ↦ birthParentLaw) birthParentLaw := by
  apply (coupled_compactFluidPaths_tendstoInMeasure
    rates hl hδ hC hrates).tendstoInDistribution
  intro n
  exact ((Model.FinitePath.measurable (compactFluidPaths l C n)).comp
    (measurable_coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1))).aemeasurable

/-- Genuine joint weak convergence of both floor-time fluid trajectories,
uniformly on the specified compact time intervals, under the original finite
epidemic path law. The susceptible interval reaches the fluid extinction time;
the infectious interval may be any compact `[0,C]`. -/
theorem compactFluidPaths_tendstoInDistribution
    (rates : ℕ → ℝ≥0) {l δ C : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    TendstoInDistribution (fun n ↦ compactFluidPaths l C n) atTop
      (localCompactFluidPaths l C)
      (fun n ↦ Model.pathMeasure (rates n) n (2 * n + 1)) birthParentLaw := by
  have hcommon := coupled_compactFluidPaths_tendstoInDistribution
    rates hl hδ hC hrates
  refine ⟨fun n ↦ (Model.FinitePath.measurable (compactFluidPaths l C n)).aemeasurable,
    (measurable_localCompactFluidPaths l C).aemeasurable, ?_⟩
  have hmap (n : ℕ) (hn : 0 < n) :
      birthParentLaw.map (fun q ↦ compactFluidPaths l C n
        (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q)) =
      (Model.pathMeasure (rates n) n (2 * n + 1)).map
        (compactFluidPaths l C n) := by
    let a : ℝ≥0 := rates n * n
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
    have hrate : a / n = rates n := by
      dsimp [a]
      field_simp [hn0]
    have hLaw := coupledTreeHistory_law a n (2 * n + 1)
    rw [hrate] at hLaw
    have hmap' : birthParentLaw.map
        (compactFluidPaths l C n ∘ coupledTreeHistory a n (2 * n + 1)) =
        (Model.pathMeasure (rates n) n (2 * n + 1)).map
          (compactFluidPaths l C n) := by
      rw [← Measure.map_map (Model.FinitePath.measurable _)
        (measurable_coupledTreeHistory a n (2 * n + 1)), hLaw]
    simpa only [Function.comp_def, a, NNReal.coe_mul, NNReal.coe_natCast] using hmap'
  have heq :
      (fun n ↦ (⟨birthParentLaw.map (fun q ↦ compactFluidPaths l C n
        (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q)), inferInstance⟩ :
          ProbabilityMeasure (CompactFluidPair C (fluidExtinctionTime l)))) =ᶠ[atTop]
      (fun n ↦ (⟨(Model.pathMeasure (rates n) n (2 * n + 1)).map
        (compactFluidPaths l C n), inferInstance⟩ :
          ProbabilityMeasure (CompactFluidPair C (fluidExtinctionTime l)))) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact Subtype.ext (hmap n hn)
  exact hcommon.tendsto.congr' heq

def earlyPairToTriple (z : ℕ × ℕ) : (ℕ × Bool) × ℕ :=
  ((z.1, decide (z.1 = 0)), z.2)

theorem realThresholdEarlyTriple_earlyTerminalPairAt_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      {p | realThresholdEarlyTriple l δ n p ≠
        earlyPairToTriple (earlyTerminalPairAt (Model.sourceCutoff l δ n) p)})
      atTop (𝓝 0) := by
  let T := (1 - δ) * fluidExtinctionTime l
  have hT : 0 ≤ T :=
    (mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)).le
  have hflag := realThreshold_earlyTerminalPairAt_zero_disagreement_tendsto_zero
    rates hl hδ hrates
  have hheight := strictEarlyHeight_earlyTerminalPairAt_snd_disagreement_tendsto_zero
    rates hl hδ hrates
  have hsum := hflag.add hheight
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  let H := Model.sourceCutoff l δ n
  let μ := Model.pathMeasure (rates n) n (2 * n + 1)
  let D : Set (Model.FinitePath (2 * n + 1)) :=
    {p | realThresholdEarlyTriple l δ n p ≠
      earlyPairToTriple (earlyTerminalPairAt H p)}
  let Dflag : Set (Model.FinitePath (2 * n + 1)) :=
    {p | ¬ (T * n ≤ ((2 * p.last.vertices - 1 : ℕ) : ℝ) ↔
      (earlyTerminalPairAt H p).1 = 0)}
  let Dheight : Set (Model.FinitePath (2 * n + 1)) :=
    {p | strictEarlyHeight l δ n p ≠ (earlyTerminalPairAt H p).2}
  have hsub : D ≤ᵐ[μ] Dflag ∪ Dheight := by
    filter_upwards [Model.ae_supportedPath (rates n) n (2 * n + 1)] with p hp
    intro hdiff
    by_cases hf : T * n ≤ ((2 * p.last.vertices - 1 : ℕ) : ℝ) ↔
        (earlyTerminalPairAt H p).1 = 0
    · by_cases hh : strictEarlyHeight l δ n p =
          (earlyTerminalPairAt H p).2
      · have hfirst := earlyTerminalPairAt_fst_eq_realThreshold
          (rate := rates n) (n := n) (N := 2 * n + 1)
          hT le_rfl (Model.sourceCutoff_le_steps hl hδ n) hp
        have heq : realThresholdEarlyTriple l δ n p =
            earlyPairToTriple (earlyTerminalPairAt H p) := by
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
        exact (hdiff heq).elim
      · exact Or.inr hh
    · exact Or.inl hf
  have hbound : μ.real D ≤ μ.real (Dflag ∪ Dheight) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact (hbound.trans (measureReal_union_le Dflag Dheight))

private theorem coupled_fullPath_event_probability_tendsto_zero
    (rates : ℕ → ℝ≥0)
    (A : (n : ℕ) → Set (Model.FinitePath (2 * n + 1)))
    (hA : ∀ n, MeasurableSet (A n))
    (hzero : Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real (A n))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ birthParentLaw.real
      ((coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1)) ⁻¹' A n))
      atTop (𝓝 0) := by
  have heq : (fun n ↦ birthParentLaw.real
      ((coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1)) ⁻¹' A n)) =ᶠ[atTop]
      (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real (A n)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    let a : ℝ≥0 := rates n * n
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
    have hrate : a / n = rates n := by
      dsimp [a]
      field_simp [hn0]
    have hLaw := coupledTreeHistory_law a n (2 * n + 1)
    rw [hrate] at hLaw
    have hreal := congrArg
      (fun μ : Measure (Model.FinitePath (2 * n + 1)) ↦ μ.real (A n)) hLaw
    change ENNReal.toReal ((birthParentLaw.map
      (coupledTreeHistory a n (2 * n + 1))) (A n)) =
        ENNReal.toReal ((Model.pathMeasure (rates n) n (2 * n + 1)) (A n))
      at hreal
    rw [Measure.map_apply (measurable_coupledTreeHistory a n (2 * n + 1))
      (hA n)] at hreal
    simpa only [Measure.real, a, NNReal.coe_mul, NNReal.coe_natCast] using hreal
  exact hzero.congr' heq.symm

/-- The paper's entire unscaled early triple agrees asymptotically with its
local counterpart on the canonical common-uniform coupling. -/
theorem coupled_realThresholdEarlyTriple_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ birthParentLaw.real {q |
      realThresholdEarlyTriple l δ n
        (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q) ≠
          localEarlyTriple l q}) atTop (𝓝 0) := by
  let A : (n : ℕ) → Set (Model.FinitePath (2 * n + 1)) :=
    fun n ↦ {p | realThresholdEarlyTriple l δ n p ≠
      earlyPairToTriple (earlyTerminalPairAt (Model.sourceCutoff l δ n) p)}
  have hA := coupled_fullPath_event_probability_tendsto_zero rates A
    (fun n ↦ (Set.to_countable (A n)).measurableSet)
    (realThresholdEarlyTriple_earlyTerminalPairAt_disagreement_tendsto_zero
      rates hl hδ hrates)
  let T := (1 - δ) * fluidExtinctionTime l
  have hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  have hB := finiteEarly_joint_disagreement_tendsto_zero rates hl hT hrates
  have hsum := hA.add hB
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  let a := (rates n : ℝ) * n
  let H := Model.sourceCutoff l δ n
  let P : (ℕ → ℝ) × (ℕ → ℝ) → Model.FinitePath (2 * n + 1) :=
    coupledTreeHistory a n (2 * n + 1)
  let B : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | finiteEarlyExtinctionTime a n H q.1 ≠ localEarlyExtinctionTime l q.1 ∨
      finiteEarlyHeight a n H q ≠ localEarlyHeight l q}
  have hsub : {q | realThresholdEarlyTriple l δ n (P q) ≠ localEarlyTriple l q} ⊆
      (P ⁻¹' A n) ∪ B := by
    intro q hq
    by_contra hnot
    have hnotA : q ∉ P ⁻¹' A n := fun ha ↦ hnot (Or.inl ha)
    have hnotB : q ∉ B := fun hb ↦ hnot (Or.inr hb)
    have hsource : realThresholdEarlyTriple l δ n (P q) =
        earlyPairToTriple (earlyTerminalPairAt H (P q)) := by
      exact of_not_not hnotA
    have htime : finiteEarlyExtinctionTime a n H q.1 =
        localEarlyExtinctionTime l q.1 := by
      by_contra hne
      exact hnotB (Or.inl hne)
    have hheight : finiteEarlyHeight a n H q = localEarlyHeight l q := by
      by_contra hne
      exact hnotB (Or.inr hne)
    have hpair := finiteEarly_pair_eq_terminalPathAt a n H (2 * n + 1)
      (Model.sourceCutoff_le_steps hl hδ n) q
    have hlocal : earlyPairToTriple
        (localEarlyExtinctionTime l q.1, localEarlyHeight l q) =
        localEarlyTriple l q := by
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · exact Bool.decide_congr (localEarlyExtinctionTime_eq_zero_iff l q.1)
      · rfl
    apply hq
    calc
      realThresholdEarlyTriple l δ n (P q) =
          earlyPairToTriple (earlyTerminalPairAt H (P q)) := hsource
      _ = earlyPairToTriple (finiteEarlyExtinctionTime a n H q.1,
            finiteEarlyHeight a n H q) := by rw [hpair]
      _ = earlyPairToTriple (localEarlyExtinctionTime l q.1,
            localEarlyHeight l q) := by rw [htime, hheight]
      _ = localEarlyTriple l q := hlocal
  have hbound := (measureReal_mono (μ := birthParentLaw) hsub
    (measure_ne_top _ _)).trans
    (measureReal_union_le (μ := birthParentLaw) (P ⁻¹' A n) B)
  simpa only [a, H, P, B, A, T, Model.sourceCutoff] using hbound

/-- The logarithmic cutoff height is close in probability, on the common
coupling, to the branch value selected by local survival. -/
theorem coupled_heightLog_local_bad_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ ε : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hε : 0 < ε) :
    Tendsto (fun n ↦ birthParentLaw.real {q |
      ε ≤ |(Model.height ((coupledTreeHistory ((rates n : ℝ) * n) n
          (2 * n + 1) q).eval (Model.sourceCutoff l δ n)) : ℝ) /
          Real.log n -
        (if q.1 ∈ localSurvival l then
          growthFactor l * Real.exp (profileRoot l) else 0)|})
      atTop (𝓝 0) := by
  let A : (n : ℕ) → Set (Model.FinitePath (2 * n + 1)) :=
    sourceHeightLogBad l δ ε
  have hA := coupled_fullPath_event_probability_tendsto_zero rates A
    (fun n ↦ (Set.to_countable (A n)).measurableSet)
    (sourceHeightLogBad_probability_tendsto_zero rates hl hδ hrates hε)
  have hdis := sourceSurvivalEvent_localSurvival_disagreement_tendsto_zero
    rates hl hδ hrates
  have hsum := hA.add hdis
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  let P : (ℕ → ℝ) × (ℕ → ℝ) → Model.FinitePath (2 * n + 1) :=
    coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1)
  let D : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | ¬ ((P q).last ∈ Model.sourceSurvivalEvent l δ n ↔
      q.1 ∈ localSurvival l)}
  have hsub : {q | ε ≤ |(Model.height ((P q).eval
        (Model.sourceCutoff l δ n)) : ℝ) / Real.log n -
        (if q.1 ∈ localSurvival l then
          growthFactor l * Real.exp (profileRoot l) else 0)|} ⊆
      (P ⁻¹' A n) ∪ D := by
    intro q hq
    by_contra hnot
    have hnotA : q ∉ P ⁻¹' A n := fun ha ↦ hnot (Or.inl ha)
    have hiff : (P q).last ∈ Model.sourceSurvivalEvent l δ n ↔
        q.1 ∈ localSurvival l := of_not_not (fun hd ↦ hnot (Or.inr hd))
    have hbranch :
        (if (P q).last ∈ Model.sourceSurvivalEvent l δ n then
          growthFactor l * Real.exp (profileRoot l) else 0) =
        (if q.1 ∈ localSurvival l then
          growthFactor l * Real.exp (profileRoot l) else 0) := by
      by_cases hs : q.1 ∈ localSurvival l
      · simp [hs, hiff.mpr hs]
      · have hnosrc : (P q).last ∉ Model.sourceSurvivalEvent l δ n :=
          fun hp ↦ hs (hiff.mp hp)
        simp [hs, hnosrc]
    change ¬ ε ≤ |(Model.height ((P q).eval
      (Model.sourceCutoff l δ n)) : ℝ) / Real.log n -
      (if (P q).last ∈ Model.sourceSurvivalEvent l δ n then
        growthFactor l * Real.exp (profileRoot l) else 0)| at hnotA
    rw [hbranch] at hnotA
    exact hnotA hq
  have hbound := (measureReal_mono (μ := birthParentLaw) hsub
    (measure_ne_top _ _)).trans
    (measureReal_union_le (μ := birthParentLaw) (P ⁻¹' A n) D)
  simpa only [P, D, A, NNReal.coe_mul, NNReal.coe_natCast] using hbound

/-- The complete list of source coordinates at a fixed compact time horizon:
the early time, survival indicator, early height, normalized cutoff height,
and both fluid trajectories. -/
structure CompactFluidJoint (l C : ℝ) where
  early : (ℕ × Bool) × ℕ
  heightLog : ℝ
  fluid : CompactFluidPair C (fluidExtinctionTime l)

def earlyMetricCode (z : (ℕ × Bool) × ℕ) : (ℕ × ℕ) × ℕ :=
  ((z.1.1, if z.1.2 then 1 else 0), z.2)

noncomputable instance (l C : ℝ) : PseudoEMetricSpace (CompactFluidJoint l C) :=
  PseudoEMetricSpace.induced
    (fun x ↦ ((earlyMetricCode x.early, x.heightLog), x.fluid)) inferInstance

noncomputable instance (l C : ℝ) : MeasurableSpace (CompactFluidJoint l C) := borel _

instance (l C : ℝ) : BorelSpace (CompactFluidJoint l C) := ⟨rfl⟩

private theorem CompactFluidJoint.edist_eq {l C : ℝ}
    (x y : CompactFluidJoint l C) :
    edist x y = max (max (edist (earlyMetricCode x.early)
      (earlyMetricCode y.early))
      (edist x.heightLog y.heightLog)) (edist x.fluid y.fluid) := by
  change edist ((earlyMetricCode x.early, x.heightLog), x.fluid)
      ((earlyMetricCode y.early, y.heightLog), y.fluid) = _
  simp only [Prod.edist_eq]

noncomputable def sourceCompactFluidJoint (l δ C : ℝ) (n : ℕ)
    (p : Model.FinitePath (2 * n + 1)) : CompactFluidJoint l C where
  early := realThresholdEarlyTriple l δ n p
  heightLog := (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
    Real.log n
  fluid := compactFluidPaths l C n p

noncomputable def localCompactFluidJoint (l C : ℝ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) : CompactFluidJoint l C where
  early := localEarlyTriple l q
  heightLog := if q.1 ∈ localSurvival l then
    growthFactor l * Real.exp (profileRoot l) else 0
  fluid := localCompactFluidPaths l C q

private theorem compactFluidJoint_edist_le_of_good (a l δ C ε : ℝ)
    (hε : 0 ≤ ε) (n : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ))
    (hEarly : realThresholdEarlyTriple l δ n
      (coupledTreeHistory a n (2 * n + 1) q) = localEarlyTriple l q)
    (hHeight : |(Model.height ((coupledTreeHistory a n (2 * n + 1) q).eval
      (Model.sourceCutoff l δ n)) : ℝ) / Real.log n -
      (if q.1 ∈ localSurvival l then
        growthFactor l * Real.exp (profileRoot l) else 0)| ≤ ε)
    (hFluid : q ∉ localJointFluidBad a l C ε n) :
    edist
      (sourceCompactFluidJoint l δ C n
        (coupledTreeHistory a n (2 * n + 1) q))
      (localCompactFluidJoint l C q) ≤ ENNReal.ofReal ε := by
  have hf := compactFluidPaths_edist_le_of_not_bad a l C ε hε n q hFluid
  have hh : edist
      ((sourceCompactFluidJoint l δ C n
        (coupledTreeHistory a n (2 * n + 1) q)).heightLog)
      ((localCompactFluidJoint l C q).heightLog) ≤ ENNReal.ofReal ε := by
    change edist
      ((Model.height ((coupledTreeHistory a n (2 * n + 1) q).eval
        (Model.sourceCutoff l δ n)) : ℝ) / Real.log n)
      (if q.1 ∈ localSurvival l then
        growthFactor l * Real.exp (profileRoot l) else 0) ≤ ENNReal.ofReal ε
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal hHeight
  have he : edist
      (earlyMetricCode ((sourceCompactFluidJoint l δ C n
        (coupledTreeHistory a n (2 * n + 1) q)).early))
      (earlyMetricCode ((localCompactFluidJoint l C q).early)) = 0 := by
    simp only [sourceCompactFluidJoint, localCompactFluidJoint, hEarly, edist_self]
  have hf' : edist
      ((sourceCompactFluidJoint l δ C n
        (coupledTreeHistory a n (2 * n + 1) q)).fluid)
      ((localCompactFluidJoint l C q).fluid) ≤ ENNReal.ofReal ε := by
    change edist (compactFluidPaths l C n
      (coupledTreeHistory a n (2 * n + 1) q))
      (localCompactFluidPaths l C q) ≤ ENNReal.ofReal ε
    exact hf
  rw [CompactFluidJoint.edist_eq, he]
  simpa only [zero_le, max_eq_right, max_le_iff] using And.intro hh hf'

private theorem tendsto_measure_of_real_zero
    (A : ℕ → Set ((ℕ → ℝ) × (ℕ → ℝ)))
    (h : Tendsto (fun n ↦ birthParentLaw.real (A n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ birthParentLaw (A n)) atTop (𝓝 0) := by
  apply (ENNReal.tendsto_toReal_zero_iff (fun n ↦ measure_ne_top _ _)).mp
  simpa only [Measure.real] using h

/-- All source coordinates, including the two entire compact-time paths,
converge jointly in measure on the common coupling. -/
theorem coupled_sourceCompactFluidJoint_tendstoInMeasure
    (rates : ℕ → ℝ≥0) {l δ C : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    TendstoInMeasure birthParentLaw
      (fun n q ↦ sourceCompactFluidJoint l δ C n
        (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q))
      atTop (localCompactFluidJoint l C) := by
  apply tendstoInMeasure_of_ne_top
  intro ε hε hεtop
  let r : ℝ := ε.toReal
  have hr : 0 < r := ENNReal.toReal_pos hε.ne' hεtop
  have hsmall : 0 < r / 2 := half_pos hr
  let A : ℕ → Set ((ℕ → ℝ) × (ℕ → ℝ)) := fun n ↦ {q |
    realThresholdEarlyTriple l δ n
      (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q) ≠
        localEarlyTriple l q}
  let B : ℕ → Set ((ℕ → ℝ) × (ℕ → ℝ)) := fun n ↦ {q |
    r / 2 ≤ |(Model.height ((coupledTreeHistory ((rates n : ℝ) * n) n
      (2 * n + 1) q).eval (Model.sourceCutoff l δ n)) : ℝ) /
      Real.log n -
      (if q.1 ∈ localSurvival l then
        growthFactor l * Real.exp (profileRoot l) else 0)|}
  let D : ℕ → Set ((ℕ → ℝ) × (ℕ → ℝ)) := fun n ↦
    localJointFluidBad ((rates n : ℝ) * n) l C (r / 2) n
  have hA : Tendsto (fun n ↦ birthParentLaw (A n)) atTop (𝓝 0) :=
    tendsto_measure_of_real_zero A
      (coupled_realThresholdEarlyTriple_disagreement_tendsto_zero
        rates hl hδ hrates)
  have hB : Tendsto (fun n ↦ birthParentLaw (B n)) atTop (𝓝 0) :=
    tendsto_measure_of_real_zero B
      (coupled_heightLog_local_bad_tendsto_zero
        rates hl hδ hrates hsmall)
  have hD : Tendsto (fun n ↦ birthParentLaw (D n)) atTop (𝓝 0) :=
    tendsto_measure_of_real_zero D
      (coupled_local_joint_fluid_compact_time_concentration
        rates hl hδ hC hrates hsmall)
  have hsum : Tendsto (fun n ↦
      birthParentLaw (A n) +
        (birthParentLaw (B n) + birthParentLaw (D n)))
      atTop (𝓝 0) := by
    simpa only [add_zero, zero_add] using hA.add (hB.add hD)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
  · intro n
    exact bot_le
  · intro n
    have hsub : {q | ε ≤ edist
        (sourceCompactFluidJoint l δ C n
          (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q))
        (localCompactFluidJoint l C q)} ⊆ A n ∪ (B n ∪ D n) := by
      intro q hq
      by_contra hnot
      have hnotA : q ∉ A n := fun ha ↦ hnot (Or.inl ha)
      have hnotB : q ∉ B n := fun hb ↦ hnot (Or.inr (Or.inl hb))
      have hnotD : q ∉ D n := fun hd ↦ hnot (Or.inr (Or.inr hd))
      have hearly : realThresholdEarlyTriple l δ n
          (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q) =
            localEarlyTriple l q := of_not_not hnotA
      have hheight : |(Model.height ((coupledTreeHistory
          ((rates n : ℝ) * n) n (2 * n + 1) q).eval
          (Model.sourceCutoff l δ n)) : ℝ) / Real.log n -
          (if q.1 ∈ localSurvival l then
            growthFactor l * Real.exp (profileRoot l) else 0)| ≤ r / 2 :=
        (lt_of_not_ge hnotB).le
      have hle := compactFluidJoint_edist_le_of_good
        ((rates n : ℝ) * n) l δ C (r / 2) hsmall.le n q
          hearly hheight hnotD
      have hlt : ENNReal.ofReal (r / 2) < ε := by
        rw [← ENNReal.ofReal_toReal hεtop]
        exact (ENNReal.ofReal_lt_ofReal_iff hr).2 (half_lt_self hr)
      exact (not_le.mpr (hle.trans_lt hlt)) hq
    calc
      birthParentLaw {q | ε ≤ edist
          (sourceCompactFluidJoint l δ C n
            (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q))
          (localCompactFluidJoint l C q)}
          ≤ birthParentLaw (A n ∪ (B n ∪ D n)) := measure_mono hsub
      _ ≤ birthParentLaw (A n) + birthParentLaw (B n ∪ D n) :=
        measure_union_le _ _
      _ ≤ birthParentLaw (A n) +
          (birthParentLaw (B n) + birthParentLaw (D n)) :=
        add_le_add le_rfl (measure_union_le _ _)

theorem coupled_sourceCompactFluidJoint_tendstoInDistribution
    (rates : ℕ → ℝ≥0) {l δ C : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    TendstoInDistribution
      (fun n q ↦ sourceCompactFluidJoint l δ C n
        (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q))
      atTop (localCompactFluidJoint l C)
      (fun _ ↦ birthParentLaw) birthParentLaw := by
  apply (coupled_sourceCompactFluidJoint_tendstoInMeasure
    rates hl hδ hC hrates).tendstoInDistribution
  intro n
  exact ((Model.FinitePath.measurable (sourceCompactFluidJoint l δ C n)).comp
    (measurable_coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1))).aemeasurable

/-- The full source functional limit: the early time, survival flag, early
height, logarithmic cutoff height, and both trajectories converge jointly in
distribution under the actual epidemic law. The conclusion holds for every
finite infectious time horizon `C`; the susceptible horizon is `t_λ`. -/
theorem sourceCompactFluidJoint_tendstoInDistribution
    (rates : ℕ → ℝ≥0) {l δ C : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    TendstoInDistribution
      (fun n ↦ sourceCompactFluidJoint l δ C n) atTop
      (localCompactFluidJoint l C)
      (fun n ↦ Model.pathMeasure (rates n) n (2 * n + 1)) birthParentLaw := by
  have hcommon := coupled_sourceCompactFluidJoint_tendstoInDistribution
    rates hl hδ hC hrates
  refine ⟨fun n ↦ (Model.FinitePath.measurable
      (sourceCompactFluidJoint l δ C n)).aemeasurable,
    hcommon.aemeasurable_limit, ?_⟩
  have hmap (n : ℕ) (hn : 0 < n) :
      birthParentLaw.map (fun q ↦ sourceCompactFluidJoint l δ C n
        (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q)) =
      (Model.pathMeasure (rates n) n (2 * n + 1)).map
        (sourceCompactFluidJoint l δ C n) := by
    let a : ℝ≥0 := rates n * n
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
    have hrate : a / n = rates n := by
      dsimp [a]
      field_simp [hn0]
    have hLaw := coupledTreeHistory_law a n (2 * n + 1)
    rw [hrate] at hLaw
    have hmap' : birthParentLaw.map
        (sourceCompactFluidJoint l δ C n ∘ coupledTreeHistory a n (2 * n + 1)) =
        (Model.pathMeasure (rates n) n (2 * n + 1)).map
          (sourceCompactFluidJoint l δ C n) := by
      rw [← Measure.map_map (Model.FinitePath.measurable _)
        (measurable_coupledTreeHistory a n (2 * n + 1)), hLaw]
    simpa only [Function.comp_def, a, NNReal.coe_mul, NNReal.coe_natCast] using hmap'
  have heq :
      (fun n ↦ (⟨birthParentLaw.map (fun q ↦ sourceCompactFluidJoint l δ C n
        (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q)), inferInstance⟩ :
          ProbabilityMeasure (CompactFluidJoint l C))) =ᶠ[atTop]
      (fun n ↦ (⟨(Model.pathMeasure (rates n) n (2 * n + 1)).map
        (sourceCompactFluidJoint l δ C n), inferInstance⟩ :
          ProbabilityMeasure (CompactFluidJoint l C))) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact Subtype.ext (hmap n hn)
  exact hcommon.tendsto.congr' heq


end HeightPaper.CountCoupling
