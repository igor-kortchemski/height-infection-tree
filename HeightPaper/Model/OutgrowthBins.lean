module

public import HeightPaper.Model.OutgrowthHeightLimit
public import HeightPaper.Model.WeakProfile

/-! # Active profile bins as fresh-outgrowth root selections -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace HeightPaper.Model

def activeBinRoots (s : State) (a b : ℝ) : Finset ℕ := by
  classical
  exact (s.active.filter fun v ↦ a ≤ (s.tree.depth v : ℝ) ∧ (s.tree.depth v : ℝ) ≤ b).image Fin.val

def activeTailRoots (s : State) (a : ℝ) : Finset ℕ := by
  classical
  exact (s.active.filter fun v ↦ a ≤ (s.tree.depth v : ℝ)).image Fin.val

@[simp] theorem mem_activeBinRoots (s : State) (a b : ℝ) (v : Fin s.vertices) :
    v.val ∈ activeBinRoots s a b ↔
      v ∈ s.active ∧ a ≤ (s.tree.depth v : ℝ) ∧ (s.tree.depth v : ℝ) ≤ b := by
  classical
  constructor
  · rintro hv
    obtain ⟨w, hw, hval⟩ := Finset.mem_image.mp hv
    have heq : w = v := Fin.ext hval
    subst w
    exact Finset.mem_filter.mp hw
  · intro hv
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr hv, rfl⟩

@[simp] theorem mem_activeTailRoots (s : State) (a : ℝ) (v : Fin s.vertices) :
    v.val ∈ activeTailRoots s a ↔ v ∈ s.active ∧ a ≤ (s.tree.depth v : ℝ) := by
  classical
  constructor
  · rintro hv
    obtain ⟨w, hw, hval⟩ := Finset.mem_image.mp hv
    have heq : w = v := Fin.ext hval
    subst w
    exact Finset.mem_filter.mp hw
  · intro hv
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr hv, rfl⟩

@[simp] theorem selectedRootCount_activeBinRoots (s : State) (a b : ℝ) :
    selectedRootCount s (activeBinRoots s a b) = activeBinCount s a b := by
  classical
  unfold selectedRootCount activeBinCount
  congr 1
  ext v
  simp only [Finset.mem_filter, mem_activeBinRoots]
  tauto

@[simp] theorem selectedRootCount_activeTailRoots (s : State) (a : ℝ) :
    selectedRootCount s (activeTailRoots s a) = activeTailCount s a := by
  classical
  unfold selectedRootCount activeTailCount
  congr 1
  ext v
  simp only [Finset.mem_filter, mem_activeTailRoots]
  tauto

theorem activeBinRoots_subset_activeLabels (s : State) (a b : ℝ) :
    activeBinRoots s a b ⊆ activeLabels s := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
  exact Finset.mem_image.mpr ⟨v, (Finset.mem_filter.mp hv).1, rfl⟩

/-- Selected bin roots keep their cutoff depths throughout the future path. -/
theorem SupportedPath.depth_mem_activeBinRoots {rate : ℝ≥0} {n steps : ℕ}
    {path : ℕ → State} (hp : SupportedPath rate n steps path) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ steps) (a b : ℝ) (r : Fin (path j).vertices)
    (hr : r.val ∈ activeBinRoots (path i) a b) :
    a ≤ ((path j).tree.depth r : ℝ) ∧ ((path j).tree.depth r : ℝ) ≤ b := by
  obtain ⟨v, hv, hval⟩ := Finset.mem_image.mp hr
  have heq : Fin.castLE (hp.cutoffInvariant hij hj).1 v = r := Fin.ext hval
  have hdepth := hp.old_depth_preserved hij hj v
  rw [heq] at hdepth
  rw [hdepth]
  exact (Finset.mem_filter.mp hv).2

/-- A finite cover of the infectious cutoff roots turns per-bin fresh-height
bounds into a bound for the full final infection-tree height. -/
theorem SupportedPath.height_le_max_bins {rate : ℝ≥0} {n steps : ℕ}
    {path : ℕ → State} (hp : SupportedPath rate n steps path) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ steps) {ι : Type*} (bins : Finset ι)
    (roots : ι → Finset ℕ) (D H : ι → ℕ)
    (hcover : ∀ r : Fin (path j).vertices, r.val ∈ activeLabels (path i) →
      ∃ b ∈ bins, r.val ∈ roots b)
    (hdepth : ∀ b ∈ bins, ∀ r : Fin (path j).vertices,
      r.val ∈ roots b → (path j).tree.depth r ≤ D b)
    (hfresh : ∀ b ∈ bins,
      selectedFreshHeight (path i).vertices (path i).tree.size_pos (roots b) (path j) ≤ H b) :
    height (path j) ≤ max (height (path i)) (bins.sup (fun b ↦ D b + H b)) := by
  classical
  rw [hp.height_eq_max_active_outgrowths hij hj]
  apply max_le_max_left
  apply Finset.sup_le
  intro r hr
  obtain ⟨b, hb, hroot⟩ := hcover r (Finset.mem_filter.mp hr).2
  have hf : Tree.outgrowthHeight (path j).tree (path i).vertices (path i).tree.size_pos r ≤
      selectedFreshHeight (path i).vertices (path i).tree.size_pos (roots b) (path j) :=
    Finset.le_sup (s := Finset.univ.filter (fun r : Fin (path j).vertices ↦ r.val ∈ roots b))
      (f := Tree.outgrowthHeight (path j).tree (path i).vertices (path i).tree.size_pos)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hroot⟩)
  exact (Nat.add_le_add (hdepth b hb r hroot) (hf.trans (hfresh b hb))).trans
    (Finset.le_sup (s := bins) (f := fun b ↦ D b + H b) hb)

/-- A nonempty root selection with a common lower depth bound yields the
matching lower bound for total height. -/
theorem depth_add_selectedFreshHeight_le (s : State) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (d : ℕ)
    (hne : ∃ r : Fin s.vertices, r.val ∈ roots)
    (hold : ∀ r : Fin s.vertices, r.val ∈ roots → r.val < cutoff)
    (hdepth : ∀ r : Fin s.vertices, r.val ∈ roots → d ≤ s.tree.depth r) :
    d + selectedFreshHeight cutoff hcutoff roots s ≤ height s := by
  classical
  have hsel : (Finset.univ.filter (fun r : Fin s.vertices ↦ r.val ∈ roots)).Nonempty := by
    obtain ⟨r, hr⟩ := hne
    exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩⟩
  obtain ⟨r, hr, hmax⟩ := Finset.exists_mem_eq_sup _ hsel
    (Tree.outgrowthHeight s.tree cutoff hcutoff)
  have hroot := (Finset.mem_filter.mp hr).2
  change d + (Finset.univ.filter (fun r : Fin s.vertices ↦ r.val ∈ roots)).sup _ ≤ s.tree.height
  rw [hmax, Tree.height_eq_sup_outgrowth s.tree cutoff hcutoff]
  apply (Nat.add_le_add_right (hdepth r hroot) _).trans
  exact Finset.le_sup
    (s := Finset.univ.filter fun r : Fin s.vertices ↦ r.val < cutoff)
    (f := fun r ↦ s.tree.depth r + Tree.outgrowthHeight s.tree cutoff hcutoff r)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hold r hroot⟩)

end HeightPaper.Model
