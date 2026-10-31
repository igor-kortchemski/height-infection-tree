module

public import HeightPaper.Model.InfectionTree
public import Mathlib.Data.Nat.Find
public import Mathlib.Logic.Function.Iterate

/-!
# Disjoint fresh outgrowths at a birth-label cutoff

A vertex is assigned to the first ancestor whose infection-order label is
below the cutoff. This partitions fresh descendants even when two old roots
are themselves ancestor and descendant. Ordinary full descendant sets would
overlap in that situation.
-/

@[expose] public section

namespace HeightPaper.Model.Tree

/-- Patient zero is its own parent. -/
theorem parent_zero {n : ℕ} (t : Tree n) :
    parent t ⟨0, size_pos t⟩ = ⟨0, size_pos t⟩ := by
  induction t with
  | root => rfl
  | attach t p ih =>
      simp only [parent, size_pos t, dite_eq_left]
      exact congrArg Fin.castSucc ih

/-- Depth zero characterizes patient zero. -/
theorem depth_eq_zero_iff {n : ℕ} (t : Tree n) (v : Fin n) :
    depth t v = 0 ↔ v.val = 0 := by
  constructor
  · intro h
    by_contra hv
    have := depth_pos t v hv
    omega
  · intro hv
    have heq : v = ⟨0, size_pos t⟩ := Fin.ext hv
    rw [heq, depth_zero]

/-- Moving to the parent lowers depth by one, with the root fixed. -/
theorem depth_parent_sub {n : ℕ} (t : Tree n) (v : Fin n) :
    depth t (parent t v) = depth t v - 1 := by
  by_cases hv : v.val = 0
  · have heq : v = ⟨0, size_pos t⟩ := Fin.ext hv
    simp [heq, parent_zero, depth_zero]
  · have hd := depth_parent t v hv
    omega

/-- Repeated parent steps calculate the actual ancestral distance. -/
theorem depth_iterate_parent {n : ℕ} (t : Tree n) (v : Fin n) (k : ℕ) :
    depth t ((parent t)^[k] v) = depth t v - k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', depth_parent_sub, ih]
      omega

/-- Every vertex reaches an old vertex, because the root has label zero. -/
theorem exists_old_ancestor {n : ℕ} (t : Tree n) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (v : Fin n) : ∃ k : ℕ, ((parent t)^[k] v).val < cutoff := by
  refine ⟨depth t v, ?_⟩
  have hd : depth t ((parent t)^[depth t v] v) = 0 := by
    simp [depth_iterate_parent]
  rw [(depth_eq_zero_iff t _).mp hd]
  exact hcutoff

/-- Number of fresh edges traversed before first meeting the cutoff tree. -/
noncomputable def freshDepth {n : ℕ} (t : Tree n) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (v : Fin n) : ℕ := Nat.find (exists_old_ancestor t cutoff hcutoff v)

/-- The unique first old ancestor, which is the root of the fresh outgrowth. -/
noncomputable def attachmentRoot {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v : Fin n) : Fin n :=
  (parent t)^[freshDepth t cutoff hcutoff v] v

 theorem attachmentRoot_lt {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v : Fin n) :
    (attachmentRoot t cutoff hcutoff v).val < cutoff :=
  Nat.find_spec (exists_old_ancestor t cutoff hcutoff v)

 theorem freshDepth_minimal {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v : Fin n) {j : ℕ}
    (hj : j < freshDepth t cutoff hcutoff v) :
    cutoff ≤ ((parent t)^[j] v).val := by
  exact Nat.le_of_not_lt (Nat.find_min (exists_old_ancestor t cutoff hcutoff v) hj)

 theorem freshDepth_le_depth {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v : Fin n) : freshDepth t cutoff hcutoff v ≤ depth t v := by
  apply Nat.find_min'
  have hd : depth t ((parent t)^[depth t v] v) = 0 := by simp [depth_iterate_parent]
  rw [(depth_eq_zero_iff t _).mp hd]
  exact hcutoff

/-- Exact decomposition into cutoff-root depth and the fresh descendant depth. -/
theorem depth_eq_root_add_freshDepth {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v : Fin n) :
    depth t v = depth t (attachmentRoot t cutoff hcutoff v) + freshDepth t cutoff hcutoff v := by
  have hle := freshDepth_le_depth t cutoff hcutoff v
  simp only [attachmentRoot, depth_iterate_parent]
  omega

 theorem freshDepth_of_old {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v : Fin n) (hv : v.val < cutoff) :
    freshDepth t cutoff hcutoff v = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.find_min' _ (by simpa using hv)

@[simp] theorem attachmentRoot_of_old {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v : Fin n) (hv : v.val < cutoff) :
    attachmentRoot t cutoff hcutoff v = v := by
  simp [attachmentRoot, freshDepth_of_old t cutoff hcutoff v hv]

/-- The characterization as first old ancestor is unique. -/
theorem attachmentRoot_unique {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v r : Fin n) (k : ℕ)
    (hold : r.val < cutoff) (hroot : (parent t)^[k] v = r)
    (hfresh : ∀ j < k, cutoff ≤ ((parent t)^[j] v).val) :
    attachmentRoot t cutoff hcutoff v = r := by
  have hkle : freshDepth t cutoff hcutoff v ≤ k :=
    Nat.find_min' _ (by rw [hroot]; exact hold)
  have hkge : k ≤ freshDepth t cutoff hcutoff v := by
    by_contra h
    have hlt : freshDepth t cutoff hcutoff v < k := by omega
    have hbad := hfresh _ hlt
    have hgood := attachmentRoot_lt t cutoff hcutoff v
    change ((parent t)^[freshDepth t cutoff hcutoff v] v).val < cutoff at hgood
    omega
  have heq : freshDepth t cutoff hcutoff v = k := by omega
  simpa [attachmentRoot, heq] using hroot

/-- Vertices of one fresh outgrowth, including its old root. -/
noncomputable def outgrowthVertices {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => attachmentRoot t cutoff hcutoff v = r)

@[simp] theorem mem_outgrowthVertices {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (r v : Fin n) :
    v ∈ outgrowthVertices t cutoff hcutoff r ↔ attachmentRoot t cutoff hcutoff v = r := by
  simp [outgrowthVertices]

/-- Distinct cutoff roots give disjoint components, including when the roots
are ancestor and descendant in the cutoff tree itself. -/
theorem outgrowthVertices_disjoint {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) {r s : Fin n} (hrs : r ≠ s) :
    Disjoint (outgrowthVertices t cutoff hcutoff r) (outgrowthVertices t cutoff hcutoff s) := by
  apply Finset.disjoint_left.mpr
  intro v hr hs
  exact hrs ((mem_outgrowthVertices t cutoff hcutoff r v).mp hr |>.symm.trans
    ((mem_outgrowthVertices t cutoff hcutoff s v).mp hs))

/-- Every vertex belongs to exactly one old-rooted outgrowth. -/
theorem existsUnique_outgrowth {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v : Fin n) :
    ∃! r : Fin n, r.val < cutoff ∧ v ∈ outgrowthVertices t cutoff hcutoff r := by
  refine ⟨attachmentRoot t cutoff hcutoff v, ⟨attachmentRoot_lt t cutoff hcutoff v, ?_⟩, ?_⟩
  · simp
  · intro r hr
    exact ((mem_outgrowthVertices t cutoff hcutoff r v).mp hr.2).symm

/-- An alternative first-hit description determines the same fresh depth. -/
theorem freshDepth_eq_of_first_hit {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v : Fin n) (k : ℕ)
    (hold : ((parent t)^[k] v).val < cutoff)
    (hfresh : ∀ j < k, cutoff ≤ ((parent t)^[j] v).val) :
    freshDepth t cutoff hcutoff v = k := by
  apply (Nat.find_eq_iff _).mpr
  exact ⟨hold, fun j hj => Nat.not_lt_of_ge (hfresh j hj)⟩

/-- An edge from a fresh vertex to its parent remains within the same
outgrowth component. Only old-to-old edges are cut. -/
theorem attachmentRoot_parent_of_fresh {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v : Fin n) (hv : cutoff ≤ v.val) :
    attachmentRoot t cutoff hcutoff (parent t v) = attachmentRoot t cutoff hcutoff v := by
  have hdpos : 0 < freshDepth t cutoff hcutoff v := by
    by_contra h
    have hz : freshDepth t cutoff hcutoff v = 0 := by omega
    have hold := attachmentRoot_lt t cutoff hcutoff v
    simp [attachmentRoot, hz] at hold
    omega
  let k := freshDepth t cutoff hcutoff v - 1
  have hk : freshDepth t cutoff hcutoff v = k + 1 := by dsimp [k]; omega
  have hold : ((parent t)^[k] (parent t v)).val < cutoff := by
    have hh := attachmentRoot_lt t cutoff hcutoff v
    simpa only [attachmentRoot, hk, Function.iterate_succ_apply] using hh
  have hfresh (j : ℕ) (hj : j < k) : cutoff ≤ ((parent t)^[j] (parent t v)).val := by
    have hh := freshDepth_minimal t cutoff hcutoff v (j := j + 1) (by omega)
    simpa only [Function.iterate_succ_apply] using hh
  have heq := freshDepth_eq_of_first_hit t cutoff hcutoff (parent t v) k hold hfresh
  simp only [attachmentRoot, heq, hk, Function.iterate_succ_apply]

/-- Height measured within one fresh outgrowth from its old attachment root. -/
noncomputable def outgrowthHeight {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (r : Fin n) : ℕ :=
  (outgrowthVertices t cutoff hcutoff r).sup (freshDepth t cutoff hcutoff)

 theorem root_mem_outgrowth {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (r : Fin n) (hr : r.val < cutoff) :
    r ∈ outgrowthVertices t cutoff hcutoff r := by
  simp [attachmentRoot_of_old t cutoff hcutoff r hr]

 theorem freshDepth_le_outgrowthHeight {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v : Fin n) :
    freshDepth t cutoff hcutoff v ≤
      outgrowthHeight t cutoff hcutoff (attachmentRoot t cutoff hcutoff v) := by
  apply Finset.le_sup
  simp

/-- Deterministic height decomposition over the disjoint fresh outgrowths.
The supremum ranges over old roots, with their original depth plus fresh height. -/
theorem height_eq_sup_outgrowth {n : ℕ} (t : Tree n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) :
    height t = (Finset.univ.filter fun r : Fin n => r.val < cutoff).sup
      (fun r => depth t r + outgrowthHeight t cutoff hcutoff r) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro v _
    calc
      depth t v = depth t (attachmentRoot t cutoff hcutoff v) +
          freshDepth t cutoff hcutoff v := depth_eq_root_add_freshDepth t cutoff hcutoff v
      _ ≤ depth t (attachmentRoot t cutoff hcutoff v) +
          outgrowthHeight t cutoff hcutoff (attachmentRoot t cutoff hcutoff v) :=
        Nat.add_le_add_left (freshDepth_le_outgrowthHeight t cutoff hcutoff v) _
      _ ≤ _ := Finset.le_sup
        (s := Finset.univ.filter (fun r : Fin n => r.val < cutoff))
        (f := fun r => depth t r + outgrowthHeight t cutoff hcutoff r)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, attachmentRoot_lt t cutoff hcutoff v⟩)
  · apply Finset.sup_le
    intro r hr
    have hold : r.val < cutoff := (Finset.mem_filter.mp hr).2
    have hne : (outgrowthVertices t cutoff hcutoff r).Nonempty :=
      ⟨r, root_mem_outgrowth t cutoff hcutoff r hold⟩
    obtain ⟨v, hv, hmax⟩ := Finset.exists_mem_eq_sup
      (outgrowthVertices t cutoff hcutoff r) hne (freshDepth t cutoff hcutoff)
    have hroot := (mem_outgrowthVertices t cutoff hcutoff r v).mp hv
    have hd := depth_eq_root_add_freshDepth t cutoff hcutoff v
    rw [hroot] at hd
    change depth t r + (outgrowthVertices t cutoff hcutoff r).sup _ ≤ height t
    rw [hmax, ← hd]
    exact depth_le_height t v

/-- Attaching a later vertex preserves the parents of all existing vertices. -/
@[simp] theorem parent_attach_old {n : ℕ} (t : Tree n) (p v : Fin n) :
    parent (.attach t p) v.castSucc = (parent t v).castSucc := by
  simp [parent]

 theorem iterate_parent_attach_old {n : ℕ} (t : Tree n) (p v : Fin n) (k : ℕ) :
    (parent (.attach t p))^[k] v.castSucc = ((parent t)^[k] v).castSucc := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, parent_attach_old]

/-- Old vertices retain their fresh-depth assignment when the tree grows. -/
theorem freshDepth_attach_old {n : ℕ} (t : Tree n) (p : Fin n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v : Fin n) :
    freshDepth (.attach t p) cutoff hcutoff v.castSucc = freshDepth t cutoff hcutoff v := by
  apply freshDepth_eq_of_first_hit
  · simp only [iterate_parent_attach_old, Fin.val_castSucc]
    exact attachmentRoot_lt t cutoff hcutoff v
  · intro j hj
    simp only [iterate_parent_attach_old, Fin.val_castSucc]
    exact freshDepth_minimal t cutoff hcutoff v hj

/-- Old vertices retain their attachment root when the tree grows. -/
theorem attachmentRoot_attach_old {n : ℕ} (t : Tree n) (p : Fin n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (v : Fin n) :
    attachmentRoot (.attach t p) cutoff hcutoff v.castSucc =
      (attachmentRoot t cutoff hcutoff v).castSucc := by
  simp only [attachmentRoot, freshDepth_attach_old, iterate_parent_attach_old]

/-- A fresh infection belongs to the outgrowth of its infector. -/
theorem attachmentRoot_attach_new {n : ℕ} (t : Tree n) (p : Fin n) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (hcut : cutoff ≤ n) :
    attachmentRoot (.attach t p) cutoff hcutoff (Fin.last n) =
      (attachmentRoot t cutoff hcutoff p).castSucc := by
  rw [← attachmentRoot_parent_of_fresh (.attach t p) cutoff hcutoff (Fin.last n) hcut]
  simp only [parent, Fin.val_last, lt_self_iff_false]
  exact attachmentRoot_attach_old t p cutoff hcutoff p

end HeightPaper.Model.Tree
