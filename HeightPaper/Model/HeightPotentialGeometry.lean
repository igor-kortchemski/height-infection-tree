module

public import HeightPaper.Model.HeightPotential

/-! # Geometric meaning of the height-CDF potential's event -/

public section

namespace HeightPaper.Model

/-- The potential's vertexwise condition is exactly the conjunction of
the usual fresh-outgrowth height bounds for the selected root labels. -/
theorem belowFreshHeight_iff_outgrowthHeight_lt (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) {h : ℕ} (hh : 0 < h) (s : State) :
    belowFreshHeight cutoff hcutoff roots h s ↔
      ∀ r : Fin s.vertices, r.val ∈ roots →
        Tree.outgrowthHeight s.tree cutoff hcutoff r < h := by
  constructor
  · intro hg r hr
    rw [Tree.outgrowthHeight, Finset.sup_lt_iff hh]
    intro v hv
    apply hg v
    change (Tree.attachmentRoot s.tree cutoff hcutoff v).val ∈ roots
    rw [(Tree.mem_outgrowthVertices s.tree cutoff hcutoff r v).mp hv]
    exact hr
  · intro hg v hv
    exact (Tree.freshDepth_le_outgrowthHeight s.tree cutoff hcutoff v).trans_lt
      (hg _ hv)

/-- Equivalently, the maximum of the selected fresh-outgrowth heights is
strictly below the level. The positive-level hypothesis handles an empty selection. -/
theorem belowFreshHeight_iff_sup_outgrowthHeight_lt (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) {h : ℕ} (hh : 0 < h) (s : State) :
    belowFreshHeight cutoff hcutoff roots h s ↔
      (Finset.univ.filter (fun r : Fin s.vertices ↦ r.val ∈ roots)).sup
        (Tree.outgrowthHeight s.tree cutoff hcutoff) < h := by
  classical
  rw [Finset.sup_lt_iff hh, belowFreshHeight_iff_outgrowthHeight_lt cutoff hcutoff roots hh s]
  simp

end HeightPaper.Model
