module

public import HeightPaper.Model.OutgrowthSampleGeometry
public import HeightPaper.Model.RandomOutgrowthLimits

/-! # Full-height event bounds from a finite mesh of fresh outgrowths -/

public section

open MeasureTheory
open scoped NNReal BigOperators

namespace HeightPaper.Model

theorem continuationSampleLaw_cutoff_event (μ : PMF State) (rate : ℝ≥0) (K : ℕ)
    (E : Set State) :
    (continuationSampleLaw μ rate K).toMeasure.real {x | x.cutoff ∈ E} = μ.toMeasure.real E := by
  calc
    _ = ((continuationSampleLaw μ rate K).map ContinuationSample.cutoff).toMeasure.real E := by
      rw [← PMF.toMeasure_map _ _ (ContinuationSample.measurable _)]
      exact (congrArg ENNReal.toReal (Measure.map_apply (ContinuationSample.measurable _)
        (show MeasurableSet E from trivial))).symm
    _ = _ := by rw [continuationSampleLaw_map_cutoff]

/-- A full-height upper failure on the cutoff event is covered by the
exceptional cutoff states and finitely many fresh-height upper failures. -/
theorem fullHeight_upper_mesh_bound (rate : ℝ≥0) (n j K T : ℕ)
    {ι : Type*} (bins : Finset ι) (roots : ι → State → Finset ℕ) (D H : ι → ℕ)
    (A G : Set State) (hH : ∀ b ∈ bins, 0 < H b)
    (hmesh : ∀ b ∈ bins, D b + H b ≤ T)
    (hgood : ∀ s ∈ (evolve rate n j).support, s ∈ A → s ∈ G →
      height s ≤ T ∧
      (∀ b ∈ bins, roots b s ⊆ activeLabels s) ∧
      (∀ v ∈ s.active, ∃ b ∈ bins, v.val ∈ roots b s) ∧
      (∀ b ∈ bins, ∀ v : Fin s.vertices, v.val ∈ roots b s → s.tree.depth v ≤ D b)) :
    (continuationSampleLaw (evolve rate n j) rate K).toMeasure.real
      {x | x.cutoff ∈ A ∧ T < height x.final} ≤
      (evolve rate n j).toMeasure.real (A \ G) +
        ∑ b ∈ bins, (continuationSampleLaw (evolve rate n j) rate K).toMeasure.real
          {x | x.cutoff ∈ A ∧ ¬belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos
            (roots b x.cutoff) (H b) x.final} := by
  classical
  let μ := continuationSampleLaw (evolve rate n j) rate K
  let E : ι → Set ContinuationSample := fun b ↦ {x | x.cutoff ∈ A ∧
    ¬belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos (roots b x.cutoff) (H b) x.final}
  have hcover : μ.toMeasure.real {x | x.cutoff ∈ A ∧ T < height x.final} ≤
      μ.toMeasure.real ({x | x.cutoff ∈ A \ G} ∪ ⋃ b ∈ bins, E b) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply PMF.toMeasure_mono _ (show MeasurableSet {x : ContinuationSample |
      x.cutoff ∈ A ∧ T < height x.final} from trivial)
    intro x hx
    have hxA := hx.1.1
    have hxT := hx.1.2
    by_cases hxG : x.cutoff ∈ G
    · have hcut : x.cutoff ∈ (evolve rate n j).support := by
        rw [← continuationSampleLaw_map_cutoff (evolve rate n j) rate K]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨x, hx.2, rfl⟩
      obtain ⟨hpre, hroots, hbins, hdepth⟩ := hgood x.cutoff hcut hxA hxG
      by_cases hfail : ∃ b ∈ bins, ¬belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos
          (roots b x.cutoff) (H b) x.final
      · obtain ⟨b, hb, hbfail⟩ := hfail
        exact Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hxA, hbfail⟩⟩)
      · have hfresh : ∀ b ∈ bins,
            selectedFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos (roots b x.cutoff) x.final ≤ H b := by
          intro b hb
          have hgoodb : belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos
              (roots b x.cutoff) (H b) x.final := by
            by_contra hf
            exact hfail ⟨b, hb, hf⟩
          exact ((belowFreshHeight_iff_selectedFreshHeight_lt _ _ _ (hH b hb) _).mp hgoodb).le
        have hh := continuationSample_height_le_max_bins hx.2 bins (fun b ↦ roots b x.cutoff)
          D H hroots hbins hdepth hfresh
        have hs : bins.sup (fun b ↦ D b + H b) ≤ T := Finset.sup_le hmesh
        exact False.elim ((not_lt_of_ge (hh.trans (max_le hpre hs))) hxT)
    · exact Or.inl ⟨hxA, hxG⟩
  calc
    _ ≤ μ.toMeasure.real {x | x.cutoff ∈ A \ G} + μ.toMeasure.real (⋃ b ∈ bins, E b) :=
      hcover.trans (measureReal_union_le _ _)
    _ ≤ _ := by
      rw [continuationSampleLaw_cutoff_event]
      exact add_le_add le_rfl (measureReal_biUnion_finset_le bins E)

/-- A full-height lower failure is covered by an exceptional cutoff state or
the lower fresh-height failure in any one nonempty selected depth bin. -/
theorem fullHeight_lower_bin_bound (rate : ℝ≥0) (n j K d h : ℕ)
    (roots : State → Finset ℕ) (A G : Set State) (hh : 0 < h)
    (hgood : ∀ s ∈ (evolve rate n j).support, s ∈ A → s ∈ G →
      roots s ⊆ activeLabels s ∧ 0 < selectedRootCount s (roots s) ∧
        ∀ v : Fin s.vertices, v.val ∈ roots s → d ≤ s.tree.depth v) :
    (continuationSampleLaw (evolve rate n j) rate K).toMeasure.real
      {x | x.cutoff ∈ A ∧ height x.final < d + h} ≤
      (evolve rate n j).toMeasure.real (A \ G) +
        (continuationSampleLaw (evolve rate n j) rate K).toMeasure.real
          {x | x.cutoff ∈ A ∧ belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos
            (roots x.cutoff) h x.final} := by
  let μ := continuationSampleLaw (evolve rate n j) rate K
  have hcover : μ.toMeasure.real {x | x.cutoff ∈ A ∧ height x.final < d + h} ≤
      μ.toMeasure.real ({x | x.cutoff ∈ A \ G} ∪ {x | x.cutoff ∈ A ∧
        belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos (roots x.cutoff) h x.final}) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply PMF.toMeasure_mono _ (show MeasurableSet {x : ContinuationSample |
      x.cutoff ∈ A ∧ height x.final < d + h} from trivial)
    intro x hx
    by_cases hxG : x.cutoff ∈ G
    · have hcut : x.cutoff ∈ (evolve rate n j).support := by
        rw [← continuationSampleLaw_map_cutoff (evolve rate n j) rate K]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨x, hx.2, rfl⟩
      obtain ⟨hroots, hN, hdepth⟩ := hgood x.cutoff hcut hx.1.1 hxG
      apply Or.inr
      refine ⟨hx.1.1, ?_⟩
      rw [belowFreshHeight_iff_selectedFreshHeight_lt _ _ _ hh]
      have hb := continuationSample_depth_add_fresh_le hx.2 (roots x.cutoff) d hroots hN hdepth
      have ht := hx.1.2
      omega
    · exact Or.inl ⟨hx.1.1, hxG⟩
  have hb := hcover.trans (measureReal_union_le _ _)
  rwa [continuationSampleLaw_cutoff_event] at hb

end HeightPaper.Model
