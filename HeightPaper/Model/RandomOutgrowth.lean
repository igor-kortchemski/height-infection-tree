module

public import HeightPaper.Model.OutgrowthHeightLimit
public import HeightPaper.Probability.EpidemicMoments

/-!
# Averaging actual outgrowth bounds over a random cutoff state

The joint law retains the cutoff state and its continued epidemic state.
Bounds may be restricted to a cutoff event, such as survival. Their errors
are the exceptional cutoff-state probability and one terminal barrier probability.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

/-- A cutoff state together with a state obtained by continuing its epidemic. -/
structure ContinuationSample where
  cutoff : State
  final : State

namespace ContinuationSample

instance : MeasurableSpace ContinuationSample := ⊤
instance : MeasurableSingletonClass ContinuationSample where
  measurableSet_singleton _ := trivial

theorem measurable {α : Type*} [MeasurableSpace α]
    (f : ContinuationSample → α) : Measurable f := fun _ _ ↦ trivial

end ContinuationSample

/-- Joint cutoff/final law, using the actual continuation kernel. -/
def continuationSampleLaw (μ : PMF State) (rate : ℝ≥0) (K : ℕ) : PMF ContinuationSample :=
  μ.bind fun s ↦ (continuationLaw rate s K).map (fun t ↦ ⟨s, t⟩)

theorem continuationSampleLaw_support_finite (μ : PMF State) (hμ : μ.support.Finite)
    (rate : ℝ≥0) (K : ℕ) : (continuationSampleLaw μ rate K).support.Finite :=
  FinitePMF.finite_support_bind _ _ hμ fun s _ ↦
    FinitePMF.finite_support_map _ (continuationLaw_support_finite rate s K) _

theorem continuationSampleLaw_map_cutoff (μ : PMF State) (rate : ℝ≥0) (K : ℕ) :
    (continuationSampleLaw μ rate K).map ContinuationSample.cutoff = μ := by
  simp only [continuationSampleLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (μ.bind fun s ↦ (continuationLaw rate s K).map (Function.const State s)) = μ
  simp only [PMF.map_const, PMF.bind_pure]

theorem continuationSampleLaw_map_final (μ : PMF State) (rate : ℝ≥0) (K : ℕ) :
    (continuationSampleLaw μ rate K).map ContinuationSample.final =
      μ.bind (fun s ↦ continuationLaw rate s K) := by
  simp only [continuationSampleLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (μ.bind fun s ↦ (continuationLaw rate s K).map id) = _
  simp only [PMF.map_id]

theorem continuationSampleLaw_evolve_map_final (rate : ℝ≥0) (n j K : ℕ) :
    (continuationSampleLaw (evolve rate n j) rate K).map ContinuationSample.final =
      evolve rate n (j + K) := by
  rw [continuationSampleLaw_map_final, evolve_add_continuation]

theorem continuationSampleLaw_integral (μ : PMF State) (hμ : μ.support.Finite)
    (rate : ℝ≥0) (K : ℕ) (f : ContinuationSample → ℝ) :
    (∫ x, f x ∂(continuationSampleLaw μ rate K).toMeasure) =
      ∫ s, (∫ t, f ⟨s, t⟩ ∂(continuationLaw rate s K).toMeasure) ∂μ.toMeasure := by
  rw [continuationSampleLaw, FinitePMF.integral_bind_of_finite_support _ _
    (measurable_state _) hμ
    (fun s _ ↦ FinitePMF.finite_support_map _ (continuationLaw_support_finite rate s K) _) f]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [← PMF.toMeasure_map _ _ (measurable_state _),
    integral_map_of_stronglyMeasurable (measurable_state _) (ContinuationSample.measurable f).stronglyMeasurable]

/-- Exact averaging of a cutoff-dependent event. -/
theorem continuationSampleLaw_event (μ : PMF State) (hμ : μ.support.Finite)
    (rate : ℝ≥0) (K : ℕ) (E : Set ContinuationSample) :
    (continuationSampleLaw μ rate K).toMeasure.real E =
      ∫ s, (continuationLaw rate s K).toMeasure.real {t | (⟨s, t⟩ : ContinuationSample) ∈ E}
        ∂μ.toMeasure := by
  rw [← integral_indicator_one (show MeasurableSet E from trivial),
    continuationSampleLaw_integral μ hμ rate K]
  apply integral_congr_ae
  filter_upwards [] with s
  change (∫ t, ({t | (⟨s, t⟩ : ContinuationSample) ∈ E} : Set State).indicator 1 t
    ∂(continuationLaw rate s K).toMeasure) = _
  exact integral_indicator_one (by trivial)

/-- A terminal-only event has exactly the continued marginal probability. -/
theorem continuationSampleLaw_final_event (μ : PMF State) (rate : ℝ≥0) (K : ℕ)
    (E : Set State) :
    (continuationSampleLaw μ rate K).toMeasure.real {x | x.final ∈ E} =
      (μ.bind (fun s ↦ continuationLaw rate s K)).toMeasure.real E := by
  rw [← continuationSampleLaw_map_final μ rate K,
    ← PMF.toMeasure_map _ _ (ContinuationSample.measurable _)]
  exact (congrArg ENNReal.toReal (Measure.map_apply (ContinuationSample.measurable _)
    (show MeasurableSet E from trivial))).symm

theorem continuationSampleLaw_restricted_event (μ : PMF State) (hμ : μ.support.Finite)
    (rate : ℝ≥0) (K : ℕ) (A : Set State) (E : State → Set State) :
    (continuationSampleLaw μ rate K).toMeasure.real
      {x | x.cutoff ∈ A ∧ x.final ∈ E x.cutoff} =
      ∫ s, A.indicator (fun s ↦ (continuationLaw rate s K).toMeasure.real (E s)) s
        ∂μ.toMeasure := by
  classical
  rw [continuationSampleLaw_event μ hμ]
  apply integral_congr_ae
  filter_upwards [] with s
  by_cases hs : s ∈ A <;> simp [hs]

/-- Uniform estimates on good cutoff states can be averaged, while retaining
a restriction to any cutoff event `A`. The additional conditional error `B`
is averaged exactly. -/
theorem continuationSampleLaw_restricted_bound
    (μ : PMF State) (hμ : μ.support.Finite) (rate : ℝ≥0) (K : ℕ)
    (A G : Set State) (E : State → Set State) (B : State → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hB : ∀ s, 0 ≤ B s)
    (hgood : ∀ s ∈ μ.support, s ∈ A → s ∈ G →
      (continuationLaw rate s K).toMeasure.real (E s) ≤ C + B s) :
    (continuationSampleLaw μ rate K).toMeasure.real {x | x.cutoff ∈ A ∧ x.final ∈ E x.cutoff} ≤
      C + μ.toMeasure.real (A \ G) + ∫ s, A.indicator B s ∂μ.toMeasure := by
  classical
  rw [continuationSampleLaw_event μ hμ]
  have hpoint : ∀ᵐ s ∂μ.toMeasure,
      (continuationLaw rate s K).toMeasure.real {t | s ∈ A ∧ t ∈ E s} ≤
        (C + (A \ G).indicator 1 s) + A.indicator B s := by
    apply FinitePMF.ae_of_forall_mem_support
    intro s hs
    by_cases hA : s ∈ A
    · simp only [hA, true_and, Set.ofPred_mem_eq, Set.indicator_of_mem hA]
      by_cases hG : s ∈ G
      · simpa only [Set.indicator_apply, Set.mem_sdiff, hA, hG, not_true_eq_false,
          and_false, ↓reduceIte, add_zero] using hgood s hs hA hG
      · have hprob : (continuationLaw rate s K).toMeasure.real (E s) ≤ 1 := measureReal_le_one
        simp only [Set.indicator_apply, Set.mem_sdiff, hA, hG, not_false_eq_true,
          and_self, ↓reduceIte, Pi.one_apply]
        linarith [hB s]
    · simp only [hA, false_and, Set.ofPred_false, measureReal_empty,
        Set.indicator_apply, Set.mem_sdiff, false_and, ↓reduceIte, add_zero]
      exact hC
  have hi (f : State → ℝ) : Integrable f μ.toMeasure :=
    FinitePMF.integrable_of_finite_support μ hμ f
  have hb := integral_mono_ae (hi _) (hi _) hpoint
  rw [integral_add (hi _) (hi _), integral_add (integrable_const _) (hi _),
    integral_const, probReal_univ, one_smul, integral_indicator_one (by trivial)] at hb
  exact hb

/-- A random-cutoff upper height-tail bound with one exceptional-cutoff error. -/
theorem randomOutgrowth_upper_bound (μ : PMF State) (hμ : μ.support.Finite)
    (rate : ℝ≥0) (K : ℕ) (roots : State → Finset ℕ) (A G : Set State)
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {h : ℕ} (hh : 0 < h) {M : ℝ} (hM : 0 ≤ M)
    (hgood : ∀ s ∈ μ.support, s ∈ A → s ∈ G →
      potential s ≤ K ∧ (p : ℝ) ≤ 1 - (infectionProbability rate s.susceptible : ℝ) ∧
        (selectedRootCount s (roots s) : ℝ) ≤ M) :
    (continuationSampleLaw μ rate K).toMeasure.real {x | x.cutoff ∈ A ∧
      ¬belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos (roots x.cutoff) h x.final} ≤
        M * Branching.geometricMean p ^ h + μ.toMeasure.real (A \ G) := by
  have hm : 0 ≤ Branching.geometricMean p := (Branching.geometricMean_pos
    (by linarith : 0 < (p : ℝ)) hp1).le
  have hb := continuationSampleLaw_restricted_bound μ hμ rate K A G
    (fun s ↦ {t | ¬belowFreshHeight s.vertices s.tree.size_pos (roots s) h t}) (fun _ ↦ 0)
    (mul_nonneg hM (pow_nonneg hm h)) (fun _ ↦ le_rfl) ?_
  · have hz : A.indicator (fun _ : State ↦ (0 : ℝ)) = fun _ ↦ 0 := by
      funext s
      simp [Set.indicator]
    simpa only [hz, integral_zero, add_zero, Set.mem_ofPred_eq] using hb
  · intro s hs hA hG
    obtain ⟨hK, hpr, hN⟩ := hgood s hs hA hG
    have ht := continuation_freshHeight_tail_le_geometric hp hp1 rate s (roots s) hh hpr hK
    exact ht.trans (by simpa only [selectedRootCount, add_zero] using
      mul_le_mul_of_nonneg_right hN (pow_nonneg hm h))

/-- A random-cutoff lower height-tail bound with an exceptional-cutoff error
and the actual terminal susceptible-barrier probability. -/
theorem randomOutgrowth_lower_bound (μ : PMF State) (hμ : μ.support.Finite)
    (rate : ℝ≥0) (K : ℕ) (roots : State → Finset ℕ) (A G : Set State)
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {h : ℕ} (hh : 0 < h) (L : ℕ) {M : ℝ}
    (hpr : 1 - (infectionProbability rate L : ℝ) ≤ (p : ℝ))
    (hgood : ∀ s ∈ μ.support, s ∈ A → s ∈ G →
      potential s ≤ K ∧ M ≤ (selectedRootCount s (roots s) : ℝ)) :
    (continuationSampleLaw μ rate K).toMeasure.real {x | x.cutoff ∈ A ∧
      belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos (roots x.cutoff) h x.final} ≤
        Real.exp (-M * ((1 - Branching.geometricMean p) * Branching.geometricMean p ^ h)) +
          μ.toMeasure.real (A \ G) +
          (continuationSampleLaw μ rate K).toMeasure.real
            {x | x.cutoff ∈ A ∧ x.final.susceptible < L} := by
  have hm : 0 ≤ Branching.geometricMean p := (Branching.geometricMean_pos
    (by linarith : 0 < (p : ℝ)) hp1).le
  have hm1 := Branching.geometricMean_lt_one hp
  rw [show {x : ContinuationSample | x.cutoff ∈ A ∧ x.final.susceptible < L} =
      {x : ContinuationSample | x.cutoff ∈ A ∧ x.final ∈ ({s | s.susceptible < L} : Set State)} by rfl,
    continuationSampleLaw_restricted_event μ hμ rate K A (fun _ ↦ {s | s.susceptible < L})]
  apply continuationSampleLaw_restricted_bound μ hμ rate K A G
    (fun s ↦ {t | belowFreshHeight s.vertices s.tree.size_pos (roots s) h t})
    (fun s ↦ (continuationLaw rate s K).toMeasure.real {t | t.susceptible < L})
    (Real.exp_nonneg _) (fun _ ↦ measureReal_nonneg)
  intro s hs hA hG
  obtain ⟨hK, hN⟩ := hgood s hs hA hG
  apply (continuation_freshHeight_cdf_le_geometric_exp hp hp1 rate s (roots s) hh L hpr hK).trans
  apply add_le_add _ le_rfl
  apply Real.exp_le_exp.mpr
  change -(selectedRootCount s (roots s) : ℝ) * _ ≤ _
  exact mul_le_mul_of_nonneg_right (neg_le_neg hN)
    (mul_nonneg (sub_nonneg.mpr hm1.le) (pow_nonneg hm h))

end HeightPaper.Model
