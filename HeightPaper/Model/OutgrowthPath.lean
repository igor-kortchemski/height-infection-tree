module

public import HeightPaper.Model.Outgrowth
public import HeightPaper.Model.Paths

/-!
# Fresh outgrowths are attached to vertices active at the cutoff

This connects the purely genealogical partition with supported epidemic paths.
An old frozen vertex has only its singleton component: full descendant trees
are never used as outgrowths.
-/

@[expose] public section
open scoped NNReal ENNReal

namespace HeightPaper.Model

/-- Infection-order labels of the currently infectious vertices. -/
def activeLabels (s : State) : Finset ℕ := s.active.image Fin.val

@[simp] theorem mem_activeLabels (s : State) (v : Fin s.vertices) :
    v.val ∈ activeLabels s ↔ v ∈ s.active := by
  simp [activeLabels, Fin.val_injective.eq_iff]

/-- The two cutoff invariants: old active vertices were active at the cutoff,
and every fresh vertex is rooted at a vertex active at that cutoff. -/
def CutoffInvariant (cutoff : ℕ) (hcutoff : 0 < cutoff) (roots : Finset ℕ)
    (s : State) : Prop :=
  cutoff ≤ s.vertices ∧
  (∀ v ∈ s.active, v.val < cutoff → v.val ∈ roots) ∧
  (∀ v : Fin s.vertices, cutoff ≤ v.val →
    (Tree.attachmentRoot s.tree cutoff hcutoff v).val ∈ roots)

 theorem cutoffInvariant_initial (s : State) :
    CutoffInvariant s.vertices s.tree.size_pos (activeLabels s) s := by
  refine ⟨le_rfl, ?_, ?_⟩
  · intro v hv _
    exact (mem_activeLabels s v).mpr hv
  · intro v hv
    have := v.isLt
    omega

/-- Recovery cannot create an active old label or any new descendant. -/
theorem CutoffInvariant.recover {cutoff : ℕ} {hcutoff : 0 < cutoff} {roots : Finset ℕ}
    {s : State} (h : CutoffInvariant cutoff hcutoff roots s) (p : Fin s.vertices) :
    CutoffInvariant cutoff hcutoff roots (recover s p) := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro v hv hvold
  exact h.2.1 v (Finset.mem_of_mem_erase hv) hvold

/-- A fresh infection is in its infector's fresh component. If the infector
is old, it is an old active vertex; otherwise the induction invariant applies. -/
theorem CutoffInvariant.infect {cutoff : ℕ} {hcutoff : 0 < cutoff} {roots : Finset ℕ}
    {s : State} (h : CutoffInvariant cutoff hcutoff roots s) (p : Fin s.vertices)
    (hp : p ∈ s.active) :
    CutoffInvariant cutoff hcutoff roots (infect s p) := by
  have hsize : cutoff ≤ s.vertices := h.1
  refine ⟨by change cutoff ≤ s.vertices + 1; omega, ?_, ?_⟩
  · intro v hv hvold
    change v ∈ insert (Fin.last s.vertices) (s.active.map Fin.castSuccEmb) at hv
    rcases Finset.mem_insert.mp hv with heq | hmap
    · have hvval : v.val = s.vertices := congrArg Fin.val heq
      omega
    · obtain ⟨u, hu, huval⟩ := Finset.mem_map.mp hmap
      subst v
      exact h.2.1 u hu hvold
  · intro v hvfresh
    change (Tree.attachmentRoot (.attach s.tree p) cutoff hcutoff v).val ∈ roots
    by_cases hvold : v.val < s.vertices
    · let u : Fin s.vertices := ⟨v.val, hvold⟩
      have heq : v = u.castSucc := Fin.ext rfl
      rw [heq, Tree.attachmentRoot_attach_old]
      exact h.2.2 u hvfresh
    · have heq : v = Fin.last s.vertices := Fin.ext (by
        change v.val = s.vertices
        have hvlt : v.val < s.vertices + 1 := v.isLt
        omega)
      rw [heq, Tree.attachmentRoot_attach_new s.tree p cutoff hcutoff h.1]
      by_cases hpold : p.val < cutoff
      · rw [Tree.attachmentRoot_of_old s.tree cutoff hcutoff p hpold]
        exact h.2.1 p hp hpold
      · exact h.2.2 p (Nat.le_of_not_gt hpold)

/-- Both invariants are preserved by every supported SIR transition. -/
theorem CutoffInvariant.step {rate : ℝ≥0} {cutoff : ℕ} {hcutoff : 0 < cutoff}
    {roots : Finset ℕ} {s t : State} (h : CutoffInvariant cutoff hcutoff roots s)
    (ht : t ∈ (step rate s).support) : CutoffInvariant cutoff hcutoff roots t := by
  rcases step_support_cases ht with ⟨_, rfl⟩ | ⟨p, hp, hrec | ⟨_, hinf⟩⟩
  · exact h
  · rw [hrec]
    exact h.recover p
  · rw [hinf]
    exact h.infect p hp

/-- Starting at any cutoff time on a supported path gives both invariants
at every later time. -/
theorem SupportedPath.cutoffInvariant {rate : ℝ≥0} {n steps : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n steps path) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps) :
    CutoffInvariant (path i).vertices (path i).tree.size_pos (activeLabels (path i)) (path j) := by
  induction j, hij using Nat.le_induction with
  | base => exact cutoffInvariant_initial _
  | succ j hij ih => exact (ih (by omega)).step (hp.2 j (by omega))

/-- Every fresh vertex's attachment root was active at the cutoff. -/
theorem SupportedPath.fresh_root_was_active {rate : ℝ≥0} {n steps : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n steps path) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps)
    (v : Fin (path j).vertices) (hv : (path i).vertices ≤ v.val) :
    (Tree.attachmentRoot (path j).tree (path i).vertices (path i).tree.size_pos v).val ∈
      activeLabels (path i) :=
  (hp.cutoffInvariant hij hj).2.2 v hv

/-- An old vertex that was already frozen at the cutoff has no fresh
outgrowth beyond itself. -/
theorem SupportedPath.outgrowth_frozen_eq_singleton {rate : ℝ≥0} {n steps : ℕ}
    {path : ℕ → State} (hp : SupportedPath rate n steps path) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ steps) (r : Fin (path j).vertices)
    (hrold : r.val < (path i).vertices) (hrfrozen : r.val ∉ activeLabels (path i)) :
    Tree.outgrowthVertices (path j).tree (path i).vertices (path i).tree.size_pos r = {r} := by
  ext v
  constructor
  · intro hv
    have hroot := (Tree.mem_outgrowthVertices _ _ _ r v).mp hv
    by_cases hvold : v.val < (path i).vertices
    · rw [Tree.attachmentRoot_of_old _ _ _ v hvold] at hroot
      exact Finset.mem_singleton.mpr hroot
    · have hwas := hp.fresh_root_was_active hij hj v (Nat.le_of_not_gt hvold)
      rw [hroot] at hwas
      exact False.elim (hrfrozen hwas)
  · intro hv
    have heq := Finset.mem_singleton.mp hv
    subst v
    exact Tree.root_mem_outgrowth _ _ _ r hrold

/-- Frozen old vertices contribute zero additional height in the decomposition. -/
theorem SupportedPath.outgrowthHeight_frozen {rate : ℝ≥0} {n steps : ℕ}
    {path : ℕ → State} (hp : SupportedPath rate n steps path) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ steps) (r : Fin (path j).vertices)
    (hrold : r.val < (path i).vertices) (hrfrozen : r.val ∉ activeLabels (path i)) :
    Tree.outgrowthHeight (path j).tree (path i).vertices (path i).tree.size_pos r = 0 := by
  unfold Tree.outgrowthHeight
  rw [hp.outgrowth_frozen_eq_singleton hij hj r hrold hrfrozen]
  simp [Tree.freshDepth_of_old _ _ _ r hrold]

/-- Infection-order labels already present remain available at the next step. -/
theorem vertices_step_mono {rate : ℝ≥0} {s t : State}
    (ht : t ∈ (step rate s).support) : s.vertices ≤ t.vertices := by
  rcases step_support_cases ht with ⟨_, rfl⟩ | ⟨p, _, hrec | ⟨_, hinf⟩⟩
  · exact le_rfl
  · rw [hrec]
    exact le_rfl
  · rw [hinf]
    exact Nat.le_succ _

/-- Existing vertices keep their depth during infection and recovery. -/
theorem depth_step_preserved {rate : ℝ≥0} {s t : State}
    (ht : t ∈ (step rate s).support) (v : Fin s.vertices) :
    t.tree.depth (Fin.castLE (vertices_step_mono ht) v) = s.tree.depth v := by
  rcases step_support_cases ht with ⟨_, heq⟩ | ⟨p, _, hrec | ⟨_, hinf⟩⟩
  · subst t
    rfl
  · subst t
    rfl
  · subst t
    exact Tree.depth_attach_old s.tree p v

/-- The old-root depth used in the final-tree decomposition is exactly its
depth at the cutoff, not a new or reweighted quantity. -/
theorem SupportedPath.old_depth_preserved {rate : ℝ≥0} {n steps : ℕ}
    {path : ℕ → State} (hp : SupportedPath rate n steps path) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ steps) (v : Fin (path i).vertices) :
    (path j).tree.depth (Fin.castLE (hp.cutoffInvariant hij hj).1 v) = (path i).tree.depth v := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
      have hjle : j ≤ steps := by omega
      exact (depth_step_preserved (hp.2 j (by omega))
        (Fin.castLE (hp.cutoffInvariant hij hjle).1 v)).trans (ih hjle)

 theorem SupportedPath.old_depth_le_height {rate : ℝ≥0} {n steps : ℕ}
    {path : ℕ → State} (hp : SupportedPath rate n steps path) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ steps) (r : Fin (path j).vertices)
    (hrold : r.val < (path i).vertices) : (path j).tree.depth r ≤ height (path i) := by
  let v : Fin (path i).vertices := ⟨r.val, hrold⟩
  have hdepth := hp.old_depth_preserved hij hj v
  have heq : Fin.castLE (hp.cutoffInvariant hij hj).1 v = r := Fin.ext rfl
  rw [heq] at hdepth
  rw [hdepth]
  exact Tree.depth_le_height _ _

 theorem SupportedPath.height_mono {rate : ℝ≥0} {n steps : ℕ}
    {path : ℕ → State} (hp : SupportedPath rate n steps path) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ steps) : height (path i) ≤ height (path j) := by
  change Finset.univ.sup (Tree.depth (path i).tree) ≤ _
  apply Finset.sup_le
  intro v _
  rw [← hp.old_depth_preserved hij hj v]
  exact Tree.depth_le_height _ _

/-- The exact decomposition used for the main height theorem: the cutoff tree
itself, and fresh outgrowths rooted only at vertices active at the cutoff. -/
theorem SupportedPath.height_eq_max_active_outgrowths {rate : ℝ≥0} {n steps : ℕ}
    {path : ℕ → State} (hp : SupportedPath rate n steps path) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ steps) :
    height (path j) = max (height (path i))
      ((Finset.univ.filter fun r : Fin (path j).vertices => r.val ∈ activeLabels (path i)).sup
        (fun r => (path j).tree.depth r + Tree.outgrowthHeight (path j).tree
          (path i).vertices (path i).tree.size_pos r)) := by
  have hall := Tree.height_eq_sup_outgrowth (path j).tree
    (path i).vertices (path i).tree.size_pos
  apply le_antisymm
  · change (path j).tree.height ≤ _
    rw [hall]
    apply Finset.sup_le
    intro r hr
    have hrold := (Finset.mem_filter.mp hr).2
    by_cases hractive : r.val ∈ activeLabels (path i)
    · apply (Finset.le_sup (s := Finset.univ.filter
        (fun r : Fin (path j).vertices => r.val ∈ activeLabels (path i)))
        (f := fun r => (path j).tree.depth r + Tree.outgrowthHeight (path j).tree
          (path i).vertices (path i).tree.size_pos r)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hractive⟩)).trans
      exact le_max_right _ _
    · rw [hp.outgrowthHeight_frozen hij hj r hrold hractive, Nat.add_zero]
      exact (hp.old_depth_le_height hij hj r hrold).trans (le_max_left _ _)
  · apply max_le (hp.height_mono hij hj)
    apply Finset.sup_le
    intro r hr
    have hractive := (Finset.mem_filter.mp hr).2
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hractive
    have hrold : r.val < (path i).vertices := by rw [← hv]; exact v.isLt
    change _ ≤ (path j).tree.height
    rw [hall]
    exact Finset.le_sup
      (s := Finset.univ.filter (fun r : Fin (path j).vertices => r.val < (path i).vertices))
      (f := fun r => (path j).tree.depth r + Tree.outgrowthHeight (path j).tree
        (path i).vertices (path i).tree.size_pos r)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hrold⟩)

end HeightPaper.Model
