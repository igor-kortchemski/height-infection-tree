module

public import HeightPaper.Probability.EarlyBranchLocalLaw
public import HeightPaper.Model.HeightPotential

/-!
# The geometric height potential at the root of the local tree

At cutoff one, the selected outgrowth is the whole infection tree. Thus the
existing active-vertex potential starts at the geometric extinction
probability and, on the extinct branch, ends at the indicator of the local
tree's height being below the prescribed level. This is the deterministic
endpoint for an exact local-height law via the one-step harmonic identity.
-/

@[expose] public section

noncomputable section

namespace HeightPaper.Model

theorem selectedOutgrowth_one (s : State) (v : Fin s.vertices) :
    selectedOutgrowth 1 (by omega) {0} s v := by
  unfold selectedOutgrowth
  have hr := Tree.attachmentRoot_lt s.tree 1 (by omega) v
  have hz : (Tree.attachmentRoot s.tree 1 (by omega) v).val = 0 := by omega
  simp [hz]

theorem freshDepth_one_eq_depth (s : State) (v : Fin s.vertices) :
    Tree.freshDepth s.tree 1 (by omega) v = Tree.depth s.tree v := by
  have hr := Tree.attachmentRoot_lt s.tree 1 (by omega) v
  have hz : (Tree.attachmentRoot s.tree 1 (by omega) v).val = 0 := by omega
  have hroot : Tree.attachmentRoot s.tree 1 (by omega) v =
      ⟨0, Tree.size_pos s.tree⟩ := Fin.ext hz
  have hd := Tree.depth_eq_root_add_freshDepth s.tree 1 (by omega) v
  rw [hroot, Tree.depth_zero] at hd
  omega

theorem belowFreshHeight_one_iff_height_lt (h : ℕ) (s : State) :
    belowFreshHeight 1 (by omega) {0} h s ↔ height s < h := by
  classical
  cases h with
  | zero =>
      have hne : Nonempty (Fin s.vertices) := ⟨⟨0, Tree.size_pos s.tree⟩⟩
      simp [belowFreshHeight, selectedOutgrowth_one]
  | succ h =>
      change (∀ v, selectedOutgrowth 1 (by omega) {0} s v →
        Tree.freshDepth s.tree 1 (by omega) v < h + 1) ↔ s.tree.height < h + 1
      simp only [selectedOutgrowth_one, true_implies, freshDepth_one_eq_depth]
      rw [Tree.height]
      rw [Finset.sup_lt_iff (Nat.succ_pos h)]
      simp

/-- At an absorbed local state, the potential is precisely the height CDF
indicator. -/
theorem freshHeightPotential_one_of_active_empty (p : unitInterval)
    (h : ℕ) (s : State) (hs : s.active = ∅) :
    freshHeightPotential p 1 (by omega) {0} h s =
      if height s < h then 1 else 0 := by
  classical
  simp [freshHeightPotential, belowFreshHeight_one_iff_height_lt, activeHeightProduct, hs]

/-- At patient zero, the potential is the generation-`h` extinction
probability of the corresponding geometric branching law. -/
theorem freshHeightPotential_initial_one (p : unitInterval) (h : ℕ) :
    freshHeightPotential p 1 (by omega) {0} h (initial 0) =
      Branching.extinctionProbability p h := by
  classical
  by_cases hh : 0 < h
  · have hb : belowFreshHeight 1 (by omega) {0} h (initial 0) := by
      rw [belowFreshHeight_one_iff_height_lt]
      simpa [height_initial] using hh
    rw [freshHeightPotential, ite_eq_left hb]
    simp [activeHeightProduct, heightFactor, selectedOutgrowth_one,
      Tree.freshDepth_of_old, initial]
  · have hzero : h = 0 := by omega
    subst h
    simp [freshHeightPotential, belowFreshHeight_one_iff_height_lt,
      height_initial, Branching.extinctionProbability_zero]

/-- On any local-tree state, the root potential is bounded by one common
geometric CDF factor for each active vertex. -/
theorem freshHeightPotential_one_le_pow_active (p : unitInterval)
    (hp : 0 < (p : ℝ)) (h : ℕ) (s : State) :
    freshHeightPotential p 1 (by omega) {0} h s ≤
      (Branching.extinctionProbability p h) ^ s.active.card := by
  classical
  by_cases hb : height s < h
  · have hb' : belowFreshHeight 1 (by omega) {0} h s :=
      (belowFreshHeight_one_iff_height_lt h s).mpr hb
    rw [freshHeightPotential, ite_eq_left hb']
    unfold activeHeightProduct
    calc
      (∏ v ∈ s.active, heightFactor p 1 (by omega) {0} h s v) ≤
          ∏ _v ∈ s.active, Branching.extinctionProbability p h := by
        apply Finset.prod_le_prod₀
        · intro v _
          exact heightFactor_nonneg p 1 (by omega) {0} h s v
        · intro v _
          rw [heightFactor, ite_eq_left (selectedOutgrowth_one s v)]
          exact Branching.extinctionProbability_mono hp (Nat.sub_le h _)
      _ = _ := by simp
  · have hb' : ¬belowFreshHeight 1 (by omega) {0} h s :=
      (belowFreshHeight_one_iff_height_lt h s).not.mpr hb
    rw [freshHeightPotential, ite_eq_right hb']
    exact pow_nonneg (Branching.extinctionProbability_nonneg p h) _

end HeightPaper.Model

namespace HeightPaper.CountCoupling

/-- The root-height potential has zero one-step drift at exactly the local
birth probability `l / (1 + l)` and its complementary recovery probability. -/
theorem localHeightPotential_one_step {l : ℝ} (hl : 0 ≤ l)
    (h : ℕ) (s : Model.State) (v : Fin s.vertices) (hv : v ∈ s.active) :
    birthThreshold l * Model.freshHeightPotential
        (Branching.successParameter l hl) 1 (by omega) {0} h (Model.infect s v) +
      (1 - birthThreshold l) * Model.freshHeightPotential
        (Branching.successParameter l hl) 1 (by omega) {0} h (Model.recover s v) =
      Model.freshHeightPotential
        (Branching.successParameter l hl) 1 (by omega) {0} h s := by
  let p := Branching.successParameter l hl
  have hp : 0 < (p : ℝ) := Branching.successParameter_pos l hl
  have hbirth : birthThreshold l = 1 - (p : ℝ) := by
    dsimp [birthThreshold, p, Branching.successParameter]
    have hd : 1 + l ≠ 0 := by linarith
    field_simp [hd]
    ring
  calc
    birthThreshold l * Model.freshHeightPotential p 1 (by omega) {0} h (Model.infect s v) +
        (1 - birthThreshold l) * Model.freshHeightPotential p 1 (by omega) {0} h
          (Model.recover s v) =
        (p : ℝ) * Model.freshHeightPotential p 1 (by omega) {0} h (Model.recover s v) +
          (1 - (p : ℝ)) * Model.freshHeightPotential p 1 (by omega) {0} h
            (Model.infect s v) := by rw [hbirth]; ring
    _ = Model.freshHeightPotential p 1 (by omega) {0} h s :=
      Model.freshHeightPotential_one_step p hp 1 (by omega) {0} h s v hv
        s.tree.size_pos

/-- The terminal potential on an extinct local path is the indicator of its
explicit early-tree height. -/
theorem localEarlyHeight_potential_terminal_of_extinction (l : ℝ)
    (p : unitInterval) (h : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ))
    (hs : q.1 ∉ localSurvival l) :
    Model.freshHeightPotential p 1 (by omega) {0} h
      (Model.rankState (localBirth l q.1) (Model.initial 0) q.2
        (localEarlyExtinctionTime l q.1)) =
      if localEarlyHeight l q < h then 1 else 0 := by
  rw [Model.freshHeightPotential_one_of_active_empty p h _ (localEarlyTree_absorbed hs)]
  rfl

end HeightPaper.CountCoupling
