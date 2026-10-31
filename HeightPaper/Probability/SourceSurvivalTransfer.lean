module

public import HeightPaper.Model.RandomOutgrowth
public import HeightPaper.Probability.LateCutoffActivity

/-!
# From active-cutoff continuation bounds to source survival

The continuation sample has the exact terminal epidemic marginal. Activity at
the cutoff implies source survival; the difference between these two events
is the already controlled one-step cutoff discrepancy. Consequently any
vanishing continuation bound on active cutoff states transfers to the exact
survival event in the source theorem.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

theorem mem_support_continuationSampleLaw_iff (μ : PMF State) (rate : ℝ≥0) (K : ℕ)
    (x : ContinuationSample) : x ∈ (continuationSampleLaw μ rate K).support ↔
      x.cutoff ∈ μ.support ∧ x.final ∈ (continuationLaw rate x.cutoff K).support := by
  constructor
  · intro hx
    obtain ⟨s, hs, hmap⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    obtain ⟨t, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
    subst x
    exact ⟨hs, ht⟩
  · intro hx
    apply (PMF.mem_support_bind_iff _ _ _).mpr
    refine ⟨x.cutoff, hx.1, ?_⟩
    apply (PMF.mem_support_map_iff _ _ _).mpr
    exact ⟨x.final, hx.2, by cases x; rfl⟩

/-- Continuing an epidemic never decreases its genuine event count. -/
theorem continuationLaw_eventCount_mono (rate : ℝ≥0) (s₀ : State) {K : ℕ} {s : State}
    (hs : s ∈ (continuationLaw rate s₀ K).support) : eventCount s₀ ≤ eventCount s := by
  induction K generalizing s with
  | zero =>
      have he : s = s₀ := by simpa using hs
      rw [he]
  | succ K ih =>
      obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
      exact (ih ht).trans (eventCount_step_mono hs)

/-- An active cutoff has performed every event up to that cutoff, hence any
subsequent state satisfies the source event-count survival criterion. -/
theorem sourceSurvival_of_continuation_cutoff_active (rate : ℝ≥0) (n K : ℕ) (l δ : ℝ)
    {x : ContinuationSample}
    (hx : x ∈ (continuationSampleLaw (evolve rate n (sourceCutoff l δ n)) rate K).support)
    (ha : x.cutoff.active.Nonempty) : x.final ∈ sourceSurvivalEvent l δ n := by
  obtain ⟨hc, hf⟩ := (mem_support_continuationSampleLaw_iff _ _ _ x).mp hx
  have hcut := evolve_eventCount_eq_of_active hc ha
  have hmono := continuationLaw_eventCount_mono rate x.cutoff hf
  have hbound : eventCount x.final ≤ 2 * x.final.vertices - 1 := by
    unfold eventCount
    omega
  change sourceCutoff l δ n ≤ 2 * x.final.vertices - 1
  omega

private theorem cutoff_event_probability (μ : PMF State) (rate : ℝ≥0) (K : ℕ)
    (A : Set State) :
    (continuationSampleLaw μ rate K).toMeasure.real {x | x.cutoff ∈ A} = μ.toMeasure.real A := by
  have he := congrArg (fun q : PMF State ↦ q.toMeasure.real A)
    (continuationSampleLaw_map_cutoff μ rate K)
  rw [← PMF.toMeasure_map _ _ (ContinuationSample.measurable _)] at he
  exact (congrArg ENNReal.toReal (Measure.map_apply (ContinuationSample.measurable _)
    (show MeasurableSet A from trivial))).symm.trans he

/-- The final coordinate at the deterministic terminal horizon has precisely
the original terminal-state distribution. -/
theorem continuationSampleLaw_terminal_event (rate : ℝ≥0) (n j : ℕ)
    (hj : j ≤ 2 * n + 1) (B : Set State) :
    (continuationSampleLaw (evolve rate n j) rate (2 * n + 1 - j)).toMeasure.real
      {x | x.final ∈ B} = (terminalStateMeasure rate n).real B := by
  rw [continuationSampleLaw_final_event, ← evolve_add_continuation,
    Nat.add_sub_of_le hj]
  rfl

/-- Finite probability transfer, retaining the exact one-step discrepancy
between source survival and activity at the cutoff. -/
theorem sourceSurvival_event_le_continuation_active {l δ : ℝ}
    (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1) (rate : ℝ≥0) (n : ℕ)
    (hcut : 0 < sourceCutoff l δ n) (B : Set State) :
    (terminalStateMeasure rate n).real {s | s ∈ sourceSurvivalEvent l δ n ∧ s ∈ B} ≤
      (continuationSampleLaw (evolve rate n (sourceCutoff l δ n)) rate
        (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
        {x | x.cutoff.active.Nonempty ∧ x.final ∈ B} +
      (pathMeasure rate n (2 * n + 1)).real
        {p | p.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
          ¬(p.eval (sourceCutoff l δ n)).active.Nonempty} := by
  let μ := (continuationSampleLaw (evolve rate n (sourceCutoff l δ n)) rate
    (2 * n + 1 - sourceCutoff l δ n)).toMeasure
  have hcutle := sourceCutoff_le_steps hl hδ n
  have hactive : μ.real {x | x.final ∈ sourceSurvivalEvent l δ n ∧ x.cutoff.active.Nonempty} =
      (evolve rate n (sourceCutoff l δ n)).toMeasure.real {s | s.active.Nonempty} := by
    rw [← cutoff_event_probability (evolve rate n (sourceCutoff l δ n)) rate
      (2 * n + 1 - sourceCutoff l δ n) {s | s.active.Nonempty}]
    apply measureReal_congr
    have hsup : ∀ᵐ x ∂μ, x ∈ (continuationSampleLaw
        (evolve rate n (sourceCutoff l δ n)) rate (2 * n + 1 - sourceCutoff l δ n)).support := by
      apply (ae_iff_prob_eq_one (ContinuationSample.measurable _)).mpr
      exact (PMF.toMeasure_apply_eq_one_iff _ (by trivial)).mpr (fun _ h ↦ h)
    filter_upwards [hsup] with x hx
    exact propext ⟨fun h ↦ h.2, fun h ↦
      ⟨sourceSurvival_of_continuation_cutoff_active rate n _ l δ hx h, h⟩⟩
  have herror : μ.real {x | x.final ∈ sourceSurvivalEvent l δ n ∧ ¬x.cutoff.active.Nonempty} =
      (pathMeasure rate n (2 * n + 1)).real
        {p | p.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
          ¬(p.eval (sourceCutoff l δ n)).active.Nonempty} := by
    have hh := measureReal_inter_add_sdiff₀ (μ := μ)
      (s := {x | x.final ∈ sourceSurvivalEvent l δ n})
      (t := {x | x.cutoff.active.Nonempty})
      (show MeasurableSet {x : ContinuationSample | x.cutoff.active.Nonempty} from trivial).nullMeasurableSet
    change μ.real {x | x.final ∈ sourceSurvivalEvent l δ n ∧ x.cutoff.active.Nonempty} +
      μ.real {x | x.final ∈ sourceSurvivalEvent l δ n ∧ ¬x.cutoff.active.Nonempty} =
      μ.real {x | x.final ∈ sourceSurvivalEvent l δ n} at hh
    rw [hactive] at hh
    have hfinal := continuationSampleLaw_terminal_event rate n (sourceCutoff l δ n) hcutle
      (sourceSurvivalEvent l δ n)
    change μ.real {x | x.final ∈ sourceSurvivalEvent l δ n} = _ at hfinal
    rw [hfinal] at hh
    rw [sourceSurvival_cutoff_inactive_probability_eq hl hδ rate n hcut]
    linarith only [hh]
  rw [← continuationSampleLaw_terminal_event rate n (sourceCutoff l δ n) hcutle]
  change μ.real {x | x.final ∈ {s | s ∈ sourceSurvivalEvent l δ n ∧ s ∈ B}} ≤ _
  rw [← herror]
  apply le_trans _ (measureReal_union_le _ _)
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro x hx
  by_cases ha : x.cutoff.active.Nonempty
  · exact Or.inl ⟨ha, hx.2⟩
  · exact Or.inr ⟨hx.1, ha⟩

/-- Any vanishing bound on an arbitrary terminal event under active-cutoff
continuation transfers to the source survival event. -/
theorem sourceSurvival_event_tendsto_zero_of_continuation_active
    (rates : ℕ → ℝ≥0) (B : ℕ → Set State) {l δ : ℝ}
    (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hbad : Tendsto (fun n ↦
      (continuationSampleLaw (evolve (rates n) n (sourceCutoff l δ n)) (rates n)
        (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
        {x | x.cutoff.active.Nonempty ∧ x.final ∈ B n}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (terminalStateMeasure (rates n) n).real
      {s | s ∈ sourceSurvivalEvent l δ n ∧ s ∈ B n}) atTop (𝓝 0) := by
  have hh := hbad.add (sourceSurvival_cutoff_inactive_tendsto_zero rates hl hδ hrates)
  simp only [add_zero] at hh
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hh
  filter_upwards [sourceCutoff_pos_eventually hl hδ] with n hn
  exact sourceSurvival_event_le_continuation_active hl hδ (rates n) n hn (B n)

end HeightPaper.Model
