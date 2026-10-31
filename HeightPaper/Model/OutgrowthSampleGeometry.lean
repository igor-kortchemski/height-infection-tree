module

public import HeightPaper.Model.OutgrowthSamplePath
public import HeightPaper.Model.OutgrowthBins

/-! # Full-tree geometry on the actual random-cutoff sample law -/

public section

open scoped NNReal

namespace HeightPaper.Model

theorem continuationSample_vertices_le {rate : ℝ≥0} {n j K : ℕ} {x : ContinuationSample}
    (hx : x ∈ (continuationSampleLaw (evolve rate n j) rate K).support) :
    x.cutoff.vertices ≤ x.final.vertices := by
  obtain ⟨p, hp, hcut, hfin⟩ := continuationSampleLaw_evolve_support_path rate n j K x hx
  have hv := (hp.cutoffInvariant (Nat.le_add_right j K) le_rfl).1
  simpa only [hcut, FinitePath.eval_last, hfin] using hv

/-- An active cutoff root in the final tree has precisely its original depth. -/
theorem continuationSample_old_depth {rate : ℝ≥0} {n j K : ℕ} {x : ContinuationSample}
    (hx : x ∈ (continuationSampleLaw (evolve rate n j) rate K).support)
    (r : Fin x.final.vertices) (hr : r.val ∈ activeLabels x.cutoff) :
    ∃ v : Fin x.cutoff.vertices, v ∈ x.cutoff.active ∧ v.val = r.val ∧
      x.final.tree.depth r = x.cutoff.tree.depth v := by
  rcases x with ⟨s, t⟩
  obtain ⟨p, hp, hcut, hfin⟩ := continuationSampleLaw_evolve_support_path rate n j K ⟨s, t⟩ hx
  simp only at hcut hfin
  subst s
  subst t
  obtain ⟨v, hv, hval⟩ := Finset.mem_image.mp hr
  refine ⟨v, hv, hval, ?_⟩
  have hd := hp.old_depth_preserved (Nat.le_add_right j K) le_rfl v
  have heq : Fin.castLE (hp.cutoffInvariant (Nat.le_add_right j K) le_rfl).1 v =
      Fin.cast (congrArg State.vertices (FinitePath.eval_last p).symm) r := Fin.ext hval
  rw [heq] at hd
  have hcast {s t : State} (he : s = t) (r : Fin t.vertices) :
      s.tree.depth (Fin.cast (congrArg State.vertices he.symm) r) = t.tree.depth r := by
    subst t
    rfl
  exact (hcast (FinitePath.eval_last p) r).symm.trans hd

/-- A finite cover of active cutoff roots and binwise outgrowth bounds give
the actual final-height upper bound on every supported continuation sample. -/
theorem continuationSample_height_le_max_bins {rate : ℝ≥0} {n j K : ℕ} {x : ContinuationSample}
    (hx : x ∈ (continuationSampleLaw (evolve rate n j) rate K).support)
    {ι : Type*} (bins : Finset ι) (roots : ι → Finset ℕ) (D H : ι → ℕ)
    (hroots : ∀ b ∈ bins, roots b ⊆ activeLabels x.cutoff)
    (hcover : ∀ v ∈ x.cutoff.active, ∃ b ∈ bins, v.val ∈ roots b)
    (hdepth : ∀ b ∈ bins, ∀ v : Fin x.cutoff.vertices,
      v.val ∈ roots b → x.cutoff.tree.depth v ≤ D b)
    (hfresh : ∀ b ∈ bins,
      selectedFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos (roots b) x.final ≤ H b) :
    height x.final ≤ max (height x.cutoff) (bins.sup (fun b ↦ D b + H b)) := by
  rcases x with ⟨s, t⟩
  obtain ⟨p, hp, hcut, hfin⟩ := continuationSampleLaw_evolve_support_path rate n j K ⟨s, t⟩ hx
  simp only at hcut hfin
  subst s
  subst t
  have hb := hp.height_le_max_bins (Nat.le_add_right j K) le_rfl bins roots D H
    (fun r hr ↦ ?_) (fun b hb r hr ↦ ?_) (fun b hb ↦ ?_)
  · simpa only [FinitePath.eval_last] using hb
  · obtain ⟨v, hv, hval⟩ := Finset.mem_image.mp hr
    obtain ⟨b, hb, hroot⟩ := hcover v hv
    exact ⟨b, hb, hval ▸ hroot⟩
  · have hactive := hroots b hb hr
    obtain ⟨v, hv, hval⟩ := Finset.mem_image.mp hactive
    have hd := hp.old_depth_preserved (Nat.le_add_right j K) le_rfl v
    have heq : Fin.castLE (hp.cutoffInvariant (Nat.le_add_right j K) le_rfl).1 v = r := Fin.ext hval
    rw [heq] at hd
    rw [hd]
    exact hdepth b hb v (hval.symm ▸ hr)
  · simpa only [FinitePath.eval_last] using hfresh b hb

/-- A positive selected root count and a lower cutoff-depth bound give the
matching final-height lower bound on the actual joint law. -/
theorem continuationSample_depth_add_fresh_le {rate : ℝ≥0} {n j K : ℕ} {x : ContinuationSample}
    (hx : x ∈ (continuationSampleLaw (evolve rate n j) rate K).support)
    (roots : Finset ℕ) (d : ℕ) (hroots : roots ⊆ activeLabels x.cutoff)
    (hN : 0 < selectedRootCount x.cutoff roots)
    (hdepth : ∀ v : Fin x.cutoff.vertices, v.val ∈ roots → d ≤ x.cutoff.tree.depth v) :
    d + selectedFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos roots x.final ≤ height x.final := by
  classical
  apply depth_add_selectedFreshHeight_le x.final x.cutoff.vertices x.cutoff.tree.size_pos roots d
  · obtain ⟨v, hv⟩ := Finset.card_pos.mp hN
    exact ⟨Fin.castLE (continuationSample_vertices_le hx) v, (Finset.mem_filter.mp hv).2⟩
  · intro r hr
    obtain ⟨v, _, hval, _⟩ := continuationSample_old_depth hx r (hroots hr)
    rw [← hval]
    exact v.isLt
  · intro r hr
    obtain ⟨v, _, hval, hd⟩ := continuationSample_old_depth hx r (hroots hr)
    rw [hd]
    exact hdepth v (hval.symm ▸ hr)

end HeightPaper.Model
