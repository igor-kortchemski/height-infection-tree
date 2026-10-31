module

public import HeightPaper.Model.OutgrowthBins
public import HeightPaper.Model.LowProfile

/-! # Selecting the low-height active vertices as outgrowth roots -/

@[expose] public section

namespace HeightPaper.Model

noncomputable def activeLowBinRoots (s : State) (b : ℝ) : Finset ℕ :=
  activeBinRoots s 0 b

@[simp] theorem mem_activeLowBinRoots (s : State) (b : ℝ) (v : Fin s.vertices) :
    v.val ∈ activeLowBinRoots s b ↔ v ∈ s.active ∧ (s.tree.depth v : ℝ) ≤ b := by
  simp [activeLowBinRoots, mem_activeBinRoots]

@[simp] theorem selectedRootCount_activeLowBinRoots (s : State) (b : ℝ) :
    selectedRootCount s (activeLowBinRoots s b) = activeLowBinCount s b := by
  rw [activeLowBinRoots, selectedRootCount_activeBinRoots]
  simp [activeBinCount, activeLowBinCount]

end HeightPaper.Model
