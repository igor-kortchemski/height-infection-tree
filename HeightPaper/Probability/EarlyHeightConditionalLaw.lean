module

public import HeightPaper.Probability.EarlyHeightJointLaw
public import HeightPaper.Probability.EarlyLocalTreeKernel

/-!
# Conditional early-height distribution

The joint early-variable limit and the exact local Bienaymé height law yield
the paper's conditional unscaled early-height distribution.  The first theorem
uses the real threshold written in the TeX statement; the second transfers to
the exact source survival event.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal symmDiff Classical

namespace HeightPaper.CountCoupling

/-- The unnormalized early-extinction height CDF has exactly the local
extinction mass times the subcritical geometric-generation CDF as its limit. -/
theorem realThreshold_earlyHeight_extinction_cdf_tendsto
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (h : ℕ) :
    Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
      {p | (realThresholdEarlyPair l δ n p).2 = false ∧
        strictEarlyHeight l δ n p < h}) atTop
      (𝓝 ((1 / l) * Branching.extinctionProbability
        (Branching.successParameter (1 / l) (by positivity)) h)) := by
  let B : Set ((ℕ × Bool) × ℕ) := {x | x.1.2 = false ∧ x.2 < h}
  have hlim := realThresholdEarlyTriple_event_probability_tendsto
    rates hl hδ hrates B
  have hlocal : (localEarlyTriple l ⁻¹' B) =
      {q : (ℕ → ℝ) × (ℕ → ℝ) |
        q.1 ∉ localSurvival l ∧ localEarlyHeight l q < h} := by
    ext q
    simp [B, localEarlyTriple, localEarlyTimeSurvivalPair]
  rw [hlocal] at hlim
  have hmass := birthParentLaw_localExtinction_probability_eq hl
  have hcdf := localEarlyHeight_conditional_cdf_eq_subcritical hl h
  rw [hmass] at hcdf
  have hl0 : 0 < 1 / l := one_div_pos.mpr (by linarith)
  have hident : birthParentLaw.real
      {q : (ℕ → ℝ) × (ℕ → ℝ) |
        q.1 ∉ localSurvival l ∧ localEarlyHeight l q < h} =
      (1 / l) * Branching.extinctionProbability
        (Branching.successParameter (1 / l) (by positivity)) h := by
    apply (div_eq_iff hl0.ne').mp at hcdf
    simpa only [mul_comm] using hcdf
  rw [hident] at hlim
  have hset (n : ℕ) : (realThresholdEarlyTriple l δ n ⁻¹' B) =
      {p | (realThresholdEarlyPair l δ n p).2 = false ∧
        strictEarlyHeight l δ n p < h} := by
    ext p
    rfl
  simpa only [hset] using hlim

/-- Conditioning the TeX real-threshold branch on early extinction gives the
subcritical geometric Bienaymé height law at every integer height threshold. -/
theorem realThreshold_earlyHeight_conditional_cdf_tendsto
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (h : ℕ) :
    Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | (realThresholdEarlyPair l δ n p).2 = false ∧
          strictEarlyHeight l δ n p < h} /
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | (realThresholdEarlyPair l δ n p).2 = false}) atTop
      (𝓝 (Branching.extinctionProbability
        (Branching.successParameter (1 / l) (by positivity)) h)) := by
  have hnum := realThreshold_earlyHeight_extinction_cdf_tendsto
    rates hl hδ hrates h
  let B : Set (ℕ × Bool) := {x | x.2 = false}
  have hden := realThresholdEarlyPair_event_probability_tendsto
    rates hl hδ hrates B
  have hlocal : (localEarlyTimeSurvivalPair l ⁻¹' B) =
      {q : (ℕ → ℝ) × (ℕ → ℝ) | q.1 ∉ localSurvival l} := by
    ext q
    simp [B, localEarlyTimeSurvivalPair]
  rw [hlocal, birthParentLaw_localExtinction_probability_eq hl] at hden
  have hpos : 0 < 1 / l := one_div_pos.mpr (by linarith)
  have hquot := hnum.div hden hpos.ne'
  have hcancel :
      (1 / l * Branching.extinctionProbability
        (Branching.successParameter (1 / l) (by positivity)) h) /
          (1 / l) =
        Branching.extinctionProbability
          (Branching.successParameter (1 / l) (by positivity)) h := by
    field_simp
  rw [hcancel] at hquot
  have hset (n : ℕ) : (realThresholdEarlyPair l δ n ⁻¹' B) =
      {p | (realThresholdEarlyPair l δ n p).2 = false} := by
    ext p
    rfl
  simp only [hset] at hquot
  apply hquot.congr'
  filter_upwards [] with n
  rfl

/-- Restricting any path event to early extinction changes its probability by
at most the already controlled source/real-threshold boundary event. -/
theorem sourceExtinction_realThreshold_restricted_difference_le
    (rate : ℝ≥0) (l δ : ℝ) (n : ℕ)
    (P : Set (Model.FinitePath (2 * n + 1))) :
    |(Model.pathMeasure rate n (2 * n + 1)).real
        {p | p.last ∉ Model.sourceSurvivalEvent l δ n ∧ p ∈ P} -
      (Model.pathMeasure rate n (2 * n + 1)).real
        {p | (realThresholdEarlyPair l δ n p).2 = false ∧ p ∈ P}| ≤
      (Model.pathMeasure rate n (2 * n + 1)).real
        {p | ¬ (p.last ∈ Model.sourceSurvivalEvent l δ n ↔
          (1 - δ) * fluidExtinctionTime l * n ≤
            ((2 * p.last.vertices - 1 : ℕ) : ℝ))} := by
  let μ := Model.pathMeasure rate n (2 * n + 1)
  let A : Set (Model.FinitePath (2 * n + 1)) :=
    {p | p.last ∉ Model.sourceSurvivalEvent l δ n ∧ p ∈ P}
  let C : Set (Model.FinitePath (2 * n + 1)) :=
    {p | (realThresholdEarlyPair l δ n p).2 = false ∧ p ∈ P}
  let D : Set (Model.FinitePath (2 * n + 1)) :=
    {p | ¬ (p.last ∈ Model.sourceSurvivalEvent l δ n ↔
      (1 - δ) * fluidExtinctionTime l * n ≤
        ((2 * p.last.vertices - 1 : ℕ) : ℝ))}
  have hsub : A ∆ C ⊆ D := by
    intro p hp
    by_contra hd
    have hiff : p.last ∈ Model.sourceSurvivalEvent l δ n ↔
        (1 - δ) * fluidExtinctionTime l * n ≤
          ((2 * p.last.vertices - 1 : ℕ) : ℝ) := not_not.mp hd
    simp only [A, C, Set.mem_symmDiff, Set.mem_ofPred_eq] at hp
    dsimp only [realThresholdEarlyPair] at hp
    by_cases hs : p.last ∈ Model.sourceSurvivalEvent l δ n <;>
      by_cases ht : (1 - δ) * fluidExtinctionTime l * n ≤
        ((2 * p.last.vertices - 1 : ℕ) : ℝ) <;>
      simp_all
  exact (abs_measureReal_sub_le_measureReal_symmDiff
    (μ := μ) (show MeasurableSet A from trivial).nullMeasurableSet
      (show MeasurableSet C from trivial).nullMeasurableSet).trans
    (measureReal_mono hsub (measure_ne_top _ _))

/-- The same transfer holds in the limit for any sequence of path events. -/
theorem sourceExtinction_restricted_probability_tendsto_of_realThreshold
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (P : ∀ n, Set (Model.FinitePath (2 * n + 1))) (a : ℝ)
    (hreal : Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | (realThresholdEarlyPair l δ n p).2 = false ∧ p ∈ P n}) atTop (𝓝 a)) :
    Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | p.last ∉ Model.sourceSurvivalEvent l δ n ∧ p ∈ P n}) atTop (𝓝 a) := by
  have hbad := sourceSurvivalEvent_realThreshold_disagreement_tendsto_zero
    rates hl hδ hrates
  have habs : Tendsto (fun n ↦
      |(Model.pathMeasure (rates n) n (2 * n + 1)).real
          {p | p.last ∉ Model.sourceSurvivalEvent l δ n ∧ p ∈ P n} -
        (Model.pathMeasure (rates n) n (2 * n + 1)).real
          {p | (realThresholdEarlyPair l δ n p).2 = false ∧ p ∈ P n}|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hbad
    apply Eventually.of_forall
    intro n
    exact sourceExtinction_realThreshold_restricted_difference_le
      (rates n) l δ n (P n)
  have hzero := (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  have hresult := hzero.add hreal
  simpa only [sub_add_cancel, zero_add] using hresult

/-- The genuine early-extinction branch of the finite epidemic has the exact
subcritical Bienaymé height CDF after conditioning, for every allowed rate
sequence and each fixed source cutoff. -/
theorem sourceExtinction_earlyHeight_conditional_cdf_tendsto
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (h : ℕ) :
    Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | p.last ∉ Model.sourceSurvivalEvent l δ n ∧
          strictEarlyHeight l δ n p < h} /
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | p.last ∉ Model.sourceSurvivalEvent l δ n}) atTop
      (𝓝 (Branching.extinctionProbability
        (Branching.successParameter (1 / l) (by positivity)) h)) := by
  let P : ∀ n, Set (Model.FinitePath (2 * n + 1)) :=
    fun n ↦ {p | strictEarlyHeight l δ n p < h}
  let Q : ∀ n, Set (Model.FinitePath (2 * n + 1)) := fun _ ↦ Set.univ
  have hrealnum := realThreshold_earlyHeight_extinction_cdf_tendsto
    rates hl hδ hrates h
  have hnum := sourceExtinction_restricted_probability_tendsto_of_realThreshold
    rates hl hδ hrates P _ (by simpa only [P, Set.mem_ofPred_eq] using hrealnum)
  let B : Set (ℕ × Bool) := {x | x.2 = false}
  have hrealden := realThresholdEarlyPair_event_probability_tendsto
    rates hl hδ hrates B
  have hlocal : (localEarlyTimeSurvivalPair l ⁻¹' B) =
      {q : (ℕ → ℝ) × (ℕ → ℝ) | q.1 ∉ localSurvival l} := by
    ext q
    simp [B, localEarlyTimeSurvivalPair]
  rw [hlocal, birthParentLaw_localExtinction_probability_eq hl] at hrealden
  have hset (n : ℕ) : (realThresholdEarlyPair l δ n ⁻¹' B) =
      {p | (realThresholdEarlyPair l δ n p).2 = false} := by
    ext p
    rfl
  simp only [hset] at hrealden
  have hden := sourceExtinction_restricted_probability_tendsto_of_realThreshold
    rates hl hδ hrates Q (1 / l) (by simpa only [Q, Set.mem_univ, and_true]
      using hrealden)
  have hpos : 0 < 1 / l := one_div_pos.mpr (by linarith)
  have hquot := hnum.div hden hpos.ne'
  have hcancel :
      (1 / l * Branching.extinctionProbability
        (Branching.successParameter (1 / l) (by positivity)) h) /
          (1 / l) =
        Branching.extinctionProbability
          (Branching.successParameter (1 / l) (by positivity)) h := by
    field_simp
  rw [hcancel] at hquot
  simp only [P, Q, Set.mem_ofPred_eq, Set.mem_univ, and_true] at hquot
  apply hquot.congr'
  filter_upwards [] with n
  rfl

/-- The two unscaled early coordinates have a joint conditional law on the
genuine source early-extinction event, for every subset of the countable pair
space. The denominator has the proved limiting mass `1 / l`. -/
theorem sourceExtinction_earlyPair_conditional_setwise_tendsto
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (B : Set (ℕ × ℕ)) :
    Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | p.last ∉ Model.sourceSurvivalEvent l δ n ∧
          ((realThresholdEarlyPair l δ n p).1,
            strictEarlyHeight l δ n p) ∈ B} /
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | p.last ∉ Model.sourceSurvivalEvent l δ n}) atTop
      (𝓝 (birthParentLaw.real
        {q | q.1 ∉ localSurvival l ∧
          (localEarlyExtinctionTime l q.1, localEarlyHeight l q) ∈ B} /
        (1 / l))) := by
  let P : ∀ n, Set (Model.FinitePath (2 * n + 1)) :=
    fun n ↦ {p | ((realThresholdEarlyPair l δ n p).1,
      strictEarlyHeight l δ n p) ∈ B}
  let C : Set ((ℕ × Bool) × ℕ) :=
    {x | x.1.2 = false ∧ (x.1.1, x.2) ∈ B}
  have hreal := realThresholdEarlyTriple_event_probability_tendsto
    rates hl hδ hrates C
  have hlocal : (localEarlyTriple l ⁻¹' C) =
      {q : (ℕ → ℝ) × (ℕ → ℝ) | q.1 ∉ localSurvival l ∧
        (localEarlyExtinctionTime l q.1, localEarlyHeight l q) ∈ B} := by
    ext q
    simp [C, localEarlyTriple, localEarlyTimeSurvivalPair]
  rw [hlocal] at hreal
  have hset (n : ℕ) : (realThresholdEarlyTriple l δ n ⁻¹' C) =
      {p | (realThresholdEarlyPair l δ n p).2 = false ∧ p ∈ P n} := by
    ext p
    rfl
  simp only [hset] at hreal
  have hnum := sourceExtinction_restricted_probability_tendsto_of_realThreshold
    rates hl hδ hrates P _ hreal
  let Q : ∀ n, Set (Model.FinitePath (2 * n + 1)) := fun _ ↦ Set.univ
  let D : Set (ℕ × Bool) := {x | x.2 = false}
  have hrealden := realThresholdEarlyPair_event_probability_tendsto
    rates hl hδ hrates D
  have hdenlocal : (localEarlyTimeSurvivalPair l ⁻¹' D) =
      {q : (ℕ → ℝ) × (ℕ → ℝ) | q.1 ∉ localSurvival l} := by
    ext q
    simp [D, localEarlyTimeSurvivalPair]
  rw [hdenlocal, birthParentLaw_localExtinction_probability_eq hl] at hrealden
  have hdenset (n : ℕ) : (realThresholdEarlyPair l δ n ⁻¹' D) =
      {p | (realThresholdEarlyPair l δ n p).2 = false} := by
    ext p
    rfl
  simp only [hdenset] at hrealden
  have hden := sourceExtinction_restricted_probability_tendsto_of_realThreshold
    rates hl hδ hrates Q (1 / l) (by simpa only [Q, Set.mem_univ, and_true]
      using hrealden)
  have hpos : 0 < 1 / l := one_div_pos.mpr (by linarith)
  have hquot := hnum.div hden hpos.ne'
  simp only [P, Q, Set.mem_ofPred_eq, Set.mem_univ, and_true] at hquot
  apply hquot.congr'
  filter_upwards [] with n
  rfl

end HeightPaper.CountCoupling
