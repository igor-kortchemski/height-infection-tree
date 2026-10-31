module

public import HeightPaper.Model.LowOutgrowthBins

/-! # A finite depth mesh covering every infectious cutoff root -/

@[expose] public section

noncomputable section

namespace HeightPaper.Model

inductive DepthMeshBin (J : ℕ)
  | low
  | middle (i : Fin J)
  | high
  deriving DecidableEq, Fintype

def depthMeshRoots {J : ℕ} (u : Fin (J + 1) → ℝ) (b : DepthMeshBin J) (s : State) : Finset ℕ :=
  match b with
  | .low => activeLowBinRoots s (u 0)
  | .middle i => activeBinRoots s (u i.castSucc) (u i.succ)
  | .high => activeTailRoots s (u (Fin.last J))

def depthMeshUpper {J : ℕ} (u : Fin (J + 1) → ℝ) (pre : ℕ) : DepthMeshBin J → ℕ
  | .low => ⌈u 0⌉₊
  | .middle i => ⌈u i.succ⌉₊
  | .high => pre

def depthMeshLower {J : ℕ} (u : Fin (J + 1) → ℝ) : DepthMeshBin J → ℕ
  | .low => 0
  | .middle i => ⌊u i.castSucc⌋₊
  | .high => ⌊u (Fin.last J)⌋₊

@[simp] theorem selectedRootCount_depthMeshRoots_low {J : ℕ} (u : Fin (J + 1) → ℝ) (s : State) :
    selectedRootCount s (depthMeshRoots u .low s) = activeLowBinCount s (u 0) := by
  simp [depthMeshRoots]

@[simp] theorem selectedRootCount_depthMeshRoots_middle {J : ℕ} (u : Fin (J + 1) → ℝ)
    (i : Fin J) (s : State) :
    selectedRootCount s (depthMeshRoots u (.middle i) s) = activeBinCount s (u i.castSucc) (u i.succ) := by
  simp [depthMeshRoots]

@[simp] theorem selectedRootCount_depthMeshRoots_high {J : ℕ} (u : Fin (J + 1) → ℝ) (s : State) :
    selectedRootCount s (depthMeshRoots u .high s) = activeTailCount s (u (Fin.last J)) := by
  simp [depthMeshRoots]

/-- Adjacent intervals, together with the two end intervals, cover the line.
No ordering assumption on the listed cutpoints is needed for this coverage. -/
theorem depth_cutpoints_cover (J : ℕ) (u : Fin (J + 1) → ℝ) (x : ℝ) :
    x ≤ u 0 ∨ (∃ i : Fin J, u i.castSucc ≤ x ∧ x ≤ u i.succ) ∨ u (Fin.last J) ≤ x := by
  induction J with
  | zero =>
      rcases le_total x (u 0) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  | succ J ih =>
      by_cases hlow : x ≤ u 0
      · exact Or.inl hlow
      · have hfirst : u 0 ≤ x := le_of_not_ge hlow
        rcases ih (fun i ↦ u i.succ) with h | h | h
        · exact Or.inr (Or.inl ⟨0, hfirst, h⟩)
        · obtain ⟨i, hi⟩ := h
          exact Or.inr (Or.inl ⟨i.succ, hi⟩)
        · exact Or.inr (Or.inr h)

theorem depthMeshRoots_cover {J : ℕ} (u : Fin (J + 1) → ℝ) (s : State)
    (v : Fin s.vertices) (hv : v ∈ s.active) :
    ∃ b : DepthMeshBin J, v.val ∈ depthMeshRoots u b s := by
  rcases depth_cutpoints_cover J u (s.tree.depth v) with hlo | hmid | hhi
  · exact ⟨.low, (mem_activeLowBinRoots s (u 0) v).mpr ⟨hv, hlo⟩⟩
  · obtain ⟨i, hi⟩ := hmid
    exact ⟨.middle i, (mem_activeBinRoots s _ _ v).mpr ⟨hv, hi⟩⟩
  · exact ⟨.high, (mem_activeTailRoots s _ v).mpr ⟨hv, hhi⟩⟩

theorem depthMeshRoots_subset_activeLabels {J : ℕ} (u : Fin (J + 1) → ℝ)
    (b : DepthMeshBin J) (s : State) : depthMeshRoots u b s ⊆ activeLabels s := by
  cases b with
  | low => exact activeBinRoots_subset_activeLabels s 0 (u 0)
  | middle i => exact activeBinRoots_subset_activeLabels s _ _
  | high =>
      intro r hr
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_image.mpr ⟨v, (Finset.mem_filter.mp hv).1, rfl⟩

theorem depth_le_depthMeshUpper {J : ℕ} (u : Fin (J + 1) → ℝ) (pre : ℕ)
    (b : DepthMeshBin J) (s : State) (hpre : height s ≤ pre) (v : Fin s.vertices)
    (hv : v.val ∈ depthMeshRoots u b s) : s.tree.depth v ≤ depthMeshUpper u pre b := by
  cases b with
  | low =>
      have hh := ((mem_activeLowBinRoots s _ v).mp hv).2
      exact_mod_cast hh.trans (Nat.le_ceil (u 0))
  | middle i =>
      have hh := ((mem_activeBinRoots s _ _ v).mp hv).2.2
      exact_mod_cast hh.trans (Nat.le_ceil (u i.succ))
  | high => exact (Tree.depth_le_height s.tree v).trans hpre

theorem depthMeshLower_le_depth {J : ℕ} (u : Fin (J + 1) → ℝ) (b : DepthMeshBin J)
    (s : State) (v : Fin s.vertices) (hv : v.val ∈ depthMeshRoots u b s) :
    depthMeshLower u b ≤ s.tree.depth v := by
  cases b with
  | low => exact Nat.zero_le _
  | middle i =>
      have hh := ((mem_activeBinRoots s _ _ v).mp hv).2.1
      simpa only [Nat.floor_natCast, depthMeshLower] using Nat.floor_mono hh
  | high =>
      have hh := ((mem_activeTailRoots s _ v).mp hv).2
      simpa only [Nat.floor_natCast, depthMeshLower] using Nat.floor_mono hh

end HeightPaper.Model
