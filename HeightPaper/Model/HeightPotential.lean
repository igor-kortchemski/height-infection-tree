module

public import HeightPaper.Model.Outgrowth
public import HeightPaper.Probability.GeometricBranching
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Height-distribution potentials for actual epidemic states

For selected fresh outgrowth roots, the potential is zero after the chosen
height threshold has been reached. Otherwise it is the product of the
remaining geometric extinction probabilities at active vertices. It is bounded
between zero and one and has zero one-step drift at the reference recovery
probability. This provides a route to height-tail bounds without assuming a
branching-process coupling.
-/

@[expose] public section

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace HeightPaper

theorem Branching.extinctionProbability_succ_fixedpoint {p : unitInterval}
    (hp : 0 < (p : ℝ)) (h : ℕ) :
    Branching.extinctionProbability p (h + 1) = (p : ℝ) +
      (1 - (p : ℝ)) * Branching.extinctionProbability p (h + 1) *
        Branching.extinctionProbability p h := by
  have hp0 : p ≠ 0 := by
    intro heq
    have := congrArg Subtype.val heq
    simpa using hp.ne' this
  have hq := Branching.extinctionProbability_le_one p h
  have hd : 0 < 1 - (1 - (p : ℝ)) * Branching.extinctionProbability p h := by
    have := mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr p.property.2)
    nlinarith
  rw [Branching.extinctionProbability_succ hp0]
  field_simp
  ring

namespace Model

theorem Tree.freshDepth_attach_new {n : ℕ} (t : Tree n) (v : Fin n)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hcut : cutoff ≤ n) :
    Tree.freshDepth (.attach t v) cutoff hcutoff (Fin.last n) =
      Tree.freshDepth t cutoff hcutoff v + 1 := by
  have hnew := Tree.depth_eq_root_add_freshDepth (.attach t v) cutoff hcutoff (Fin.last n)
  have hold := Tree.depth_eq_root_add_freshDepth t cutoff hcutoff v
  rw [Tree.depth_attach_new, Tree.attachmentRoot_attach_new t v cutoff hcutoff hcut,
    Tree.depth_attach_old] at hnew
  omega

/-- Root selection is fixed at the cutoff and inherited by every fresh vertex. -/
def selectedOutgrowth (cutoff : ℕ) (hcutoff : 0 < cutoff) (roots : Finset ℕ)
    (s : State) (v : Fin s.vertices) : Prop :=
  (Tree.attachmentRoot s.tree cutoff hcutoff v).val ∈ roots

/-- No vertex of the selected fresh outgrowths has yet reached level `h`. -/
def belowFreshHeight (cutoff : ℕ) (hcutoff : 0 < cutoff) (roots : Finset ℕ)
    (h : ℕ) (s : State) : Prop :=
  ∀ v, selectedOutgrowth cutoff hcutoff roots s v →
    Tree.freshDepth s.tree cutoff hcutoff v < h

/-- The remaining extinction-probability factor for one active vertex. -/
def heightFactor (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) (v : Fin s.vertices) : ℝ := by
  classical
  exact if selectedOutgrowth cutoff hcutoff roots s v then
    Branching.extinctionProbability p (h - Tree.freshDepth s.tree cutoff hcutoff v) else 1

def activeHeightProduct (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) : ℝ :=
  ∏ v ∈ s.active, heightFactor p cutoff hcutoff roots h s v

/-- Bounded CDF potential, retaining past height exceedances after recovery. -/
def freshHeightPotential (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) : ℝ := by
  classical
  exact if belowFreshHeight cutoff hcutoff roots h s then
    activeHeightProduct p cutoff hcutoff roots h s else 0

theorem heightFactor_nonneg (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) (v : Fin s.vertices) :
    0 ≤ heightFactor p cutoff hcutoff roots h s v := by
  unfold heightFactor
  split_ifs
  · exact Branching.extinctionProbability_nonneg _ _
  · exact zero_le_one

theorem heightFactor_le_one (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) (v : Fin s.vertices) :
    heightFactor p cutoff hcutoff roots h s v ≤ 1 := by
  unfold heightFactor
  split_ifs
  · exact Branching.extinctionProbability_le_one _ _
  · exact le_rfl

theorem freshHeightPotential_bounds (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) :
    0 ≤ freshHeightPotential p cutoff hcutoff roots h s ∧
      freshHeightPotential p cutoff hcutoff roots h s ≤ 1 := by
  classical
  unfold freshHeightPotential
  split_ifs
  · exact ⟨Finset.prod_nonneg (fun v _ ↦ heightFactor_nonneg _ _ _ _ _ _ v),
      Finset.prod_le_one₀ (fun v _ ↦ heightFactor_nonneg _ _ _ _ _ _ v)
        (fun v _ ↦ heightFactor_le_one _ _ _ _ _ _ v)⟩
  · exact ⟨le_rfl, zero_le_one⟩

@[simp] theorem heightFactor_recover (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) (v w : Fin s.vertices) :
    heightFactor p cutoff hcutoff roots h (recover s v) w =
      heightFactor p cutoff hcutoff roots h s w := rfl

@[simp] theorem belowFreshHeight_recover (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) (v : Fin s.vertices) :
    belowFreshHeight cutoff hcutoff roots h (recover s v) ↔
      belowFreshHeight cutoff hcutoff roots h s := Iff.rfl

theorem activeHeightProduct_recover_mul (p : unitInterval) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (roots : Finset ℕ) (h : ℕ) {s : State} {v : Fin s.vertices}
    (hv : v ∈ s.active) :
    activeHeightProduct p cutoff hcutoff roots h (recover s v) *
      heightFactor p cutoff hcutoff roots h s v = activeHeightProduct p cutoff hcutoff roots h s := by
  exact Finset.prod_erase_mul s.active (heightFactor p cutoff hcutoff roots h s) hv

@[simp] theorem selectedOutgrowth_infect_old (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (s : State) (v w : Fin s.vertices) :
    selectedOutgrowth cutoff hcutoff roots (infect s v) w.castSucc ↔
      selectedOutgrowth cutoff hcutoff roots s w := by
  simp [selectedOutgrowth, infect, Tree.attachmentRoot_attach_old]

@[simp] theorem heightFactor_infect_old (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) (v w : Fin s.vertices) :
    heightFactor p cutoff hcutoff roots h (infect s v) w.castSucc =
      heightFactor p cutoff hcutoff roots h s w := by
  classical
  by_cases hs : selectedOutgrowth cutoff hcutoff roots s w
  · have hs' := (selectedOutgrowth_infect_old cutoff hcutoff roots s v w).mpr hs
    simp only [heightFactor, ite_eq_left hs', ite_eq_left hs]
    change Branching.extinctionProbability p
      (h - Tree.freshDepth (.attach s.tree v) cutoff hcutoff w.castSucc) = _
    rw [Tree.freshDepth_attach_old]
  · have hs' : ¬selectedOutgrowth cutoff hcutoff roots (infect s v) w.castSucc := by
      simpa using hs
    simp only [heightFactor, ite_eq_right hs', ite_eq_right hs]

theorem activeHeightProduct_infect (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) (v : Fin s.vertices) :
    activeHeightProduct p cutoff hcutoff roots h (infect s v) =
      heightFactor p cutoff hcutoff roots h (infect s v) (Fin.last s.vertices) *
        activeHeightProduct p cutoff hcutoff roots h s := by
  classical
  have hnew : Fin.last s.vertices ∉ s.active.map Fin.castSuccEmb := by
    simp only [Finset.mem_map, not_exists, not_and]
    intro w _ hw
    have hwval := congrArg Fin.val hw
    change w.val = s.vertices at hwval
    have := w.isLt
    omega
  simp only [activeHeightProduct, infect, Finset.prod_insert hnew, Finset.prod_map]
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  exact heightFactor_infect_old p cutoff hcutoff roots h s v w

@[simp] theorem selectedOutgrowth_infect_new (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (s : State) (v : Fin s.vertices) (hcut : cutoff ≤ s.vertices) :
    selectedOutgrowth cutoff hcutoff roots (infect s v) (Fin.last s.vertices) ↔
      selectedOutgrowth cutoff hcutoff roots s v := by
  simp [selectedOutgrowth, infect, Tree.attachmentRoot_attach_new _ _ _ _ hcut]

theorem heightFactor_infect_new (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) (v : Fin s.vertices) (hcut : cutoff ≤ s.vertices) :
    heightFactor p cutoff hcutoff roots h (infect s v) (Fin.last s.vertices) =
      if selectedOutgrowth cutoff hcutoff roots s v then
        Branching.extinctionProbability p (h - (Tree.freshDepth s.tree cutoff hcutoff v + 1))
      else 1 := by
  classical
  by_cases hs : selectedOutgrowth cutoff hcutoff roots s v
  · have hs' := (selectedOutgrowth_infect_new cutoff hcutoff roots s v hcut).mpr hs
    simp only [heightFactor, ite_eq_left hs', ite_eq_left hs]
    change Branching.extinctionProbability p
      (h - Tree.freshDepth (.attach s.tree v) cutoff hcutoff (Fin.last s.vertices)) = _
    rw [Tree.freshDepth_attach_new _ _ _ _ hcut]
  · have hs' : ¬selectedOutgrowth cutoff hcutoff roots (infect s v) (Fin.last s.vertices) := by
      simpa only [selectedOutgrowth_infect_new _ _ _ _ _ hcut] using hs
    simp only [heightFactor, ite_eq_right hs', ite_eq_right hs]

theorem belowFreshHeight_infect_iff (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) (v : Fin s.vertices) (hcut : cutoff ≤ s.vertices) :
    belowFreshHeight cutoff hcutoff roots h (infect s v) ↔
      belowFreshHeight cutoff hcutoff roots h s ∧
        (selectedOutgrowth cutoff hcutoff roots s v →
          Tree.freshDepth s.tree cutoff hcutoff v + 1 < h) := by
  constructor
  · intro hg
    constructor
    · intro w hw
      have hh := hg w.castSucc ((selectedOutgrowth_infect_old cutoff hcutoff roots s v w).mpr hw)
      simpa [infect, Tree.freshDepth_attach_old] using hh
    · intro hv
      have hh := hg (Fin.last s.vertices)
        ((selectedOutgrowth_infect_new cutoff hcutoff roots s v hcut).mpr hv)
      simpa [infect, Tree.freshDepth_attach_new _ _ _ _ hcut] using hh
  · rintro ⟨hg, hnew⟩ w
    refine Fin.lastCases ?_ ?_ w
    · intro hw
      have hs := (selectedOutgrowth_infect_new cutoff hcutoff roots s v hcut).mp hw
      simpa [infect, Tree.freshDepth_attach_new _ _ _ _ hcut] using hnew hs
    · intro u hu
      have hs := (selectedOutgrowth_infect_old cutoff hcutoff roots s v u).mp hu
      simpa [infect, Tree.freshDepth_attach_old] using hg u hs

theorem freshHeightPotential_recover_of_good (p : unitInterval) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (roots : Finset ℕ) (h : ℕ) (s : State) (v : Fin s.vertices)
    (hg : belowFreshHeight cutoff hcutoff roots h s) :
    freshHeightPotential p cutoff hcutoff roots h (recover s v) =
      activeHeightProduct p cutoff hcutoff roots h (recover s v) := by
  simp [freshHeightPotential, hg]

/-- A new violation already has a zero factor, so the ordinary active-product
update remains valid when the first excessive-depth child is created. -/
theorem freshHeightPotential_infect_of_good (p : unitInterval) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (roots : Finset ℕ) (h : ℕ) (s : State) (v : Fin s.vertices)
    (hcut : cutoff ≤ s.vertices) (hg : belowFreshHeight cutoff hcutoff roots h s) :
    freshHeightPotential p cutoff hcutoff roots h (infect s v) =
      heightFactor p cutoff hcutoff roots h (infect s v) (Fin.last s.vertices) *
        activeHeightProduct p cutoff hcutoff roots h s := by
  classical
  by_cases hnew : belowFreshHeight cutoff hcutoff roots h (infect s v)
  · rw [freshHeightPotential, ite_eq_left hnew, activeHeightProduct_infect]
  · rw [freshHeightPotential, ite_eq_right hnew]
    have hbad : ¬(selectedOutgrowth cutoff hcutoff roots s v →
        Tree.freshDepth s.tree cutoff hcutoff v + 1 < h) := by
      intro hf
      exact hnew ((belowFreshHeight_infect_iff cutoff hcutoff roots h s v hcut).mpr ⟨hg, hf⟩)
    push Not at hbad
    have hsub : h - (Tree.freshDepth s.tree cutoff hcutoff v + 1) = 0 := by omega
    rw [heightFactor_infect_new _ _ _ _ _ _ _ hcut, ite_eq_left hbad.1, hsub]
    simp

/-- Once the threshold has been crossed, recovery cannot erase that fact. -/
theorem freshHeightPotential_recover_of_bad (p : unitInterval) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (roots : Finset ℕ) (h : ℕ) (s : State) (v : Fin s.vertices)
    (hg : ¬belowFreshHeight cutoff hcutoff roots h s) :
    freshHeightPotential p cutoff hcutoff roots h (recover s v) = 0 := by
  simp [freshHeightPotential, hg]

theorem freshHeightPotential_infect_of_bad (p : unitInterval) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (roots : Finset ℕ) (h : ℕ) (s : State) (v : Fin s.vertices)
    (hcut : cutoff ≤ s.vertices) (hg : ¬belowFreshHeight cutoff hcutoff roots h s) :
    freshHeightPotential p cutoff hcutoff roots h (infect s v) = 0 := by
  have hnew : ¬belowFreshHeight cutoff hcutoff roots h (infect s v) := by
    intro hh
    exact hg ((belowFreshHeight_infect_iff cutoff hcutoff roots h s v hcut).mp hh).1
  simp [freshHeightPotential, hnew]

/-- At the reference geometric recovery probability, each possible parent draw
has exactly zero potential drift. No stochastic hypothesis is assumed. -/
theorem freshHeightPotential_one_step (p : unitInterval) (hp : 0 < (p : ℝ))
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (roots : Finset ℕ) (h : ℕ)
    (s : State) (v : Fin s.vertices) (hv : v ∈ s.active) (hcut : cutoff ≤ s.vertices) :
    (p : ℝ) * freshHeightPotential p cutoff hcutoff roots h (recover s v) +
      (1 - (p : ℝ)) * freshHeightPotential p cutoff hcutoff roots h (infect s v) =
        freshHeightPotential p cutoff hcutoff roots h s := by
  classical
  by_cases hg : belowFreshHeight cutoff hcutoff roots h s
  · rw [freshHeightPotential_recover_of_good _ _ _ _ _ _ _ hg,
      freshHeightPotential_infect_of_good _ _ _ _ _ _ _ hcut hg,
      freshHeightPotential, ite_eq_left hg]
    have hprod := activeHeightProduct_recover_mul p cutoff hcutoff roots h hv
    by_cases hs : selectedOutgrowth cutoff hcutoff roots s v
    · have hd := hg v hs
      have hidx : h - Tree.freshDepth s.tree cutoff hcutoff v =
          (h - (Tree.freshDepth s.tree cutoff hcutoff v + 1)) + 1 := by omega
      have hparent : heightFactor p cutoff hcutoff roots h s v =
          Branching.extinctionProbability p
            ((h - (Tree.freshDepth s.tree cutoff hcutoff v + 1)) + 1) := by
        simp [heightFactor, hs, hidx]
      have hchild : heightFactor p cutoff hcutoff roots h (infect s v) (Fin.last s.vertices) =
          Branching.extinctionProbability p (h - (Tree.freshDepth s.tree cutoff hcutoff v + 1)) := by
        rw [heightFactor_infect_new _ _ _ _ _ _ _ hcut, ite_eq_left hs]
      rw [hparent] at hprod
      rw [hchild, ← hprod]
      have heq := Branching.extinctionProbability_succ_fixedpoint hp
        (h - (Tree.freshDepth s.tree cutoff hcutoff v + 1))
      have hmul := congrArg
        (fun x : ℝ ↦ x * activeHeightProduct p cutoff hcutoff roots h (recover s v)) heq
      nlinarith only [hmul]
    · have hparent : heightFactor p cutoff hcutoff roots h s v = 1 := by simp [heightFactor, hs]
      have hchild : heightFactor p cutoff hcutoff roots h (infect s v) (Fin.last s.vertices) = 1 := by
        rw [heightFactor_infect_new _ _ _ _ _ _ _ hcut, ite_eq_right hs]
      rw [hparent, mul_one] at hprod
      rw [hchild, one_mul, hprod]
      ring
  · rw [freshHeightPotential_recover_of_bad _ _ _ _ _ _ _ hg,
      freshHeightPotential_infect_of_bad _ _ _ _ _ _ _ hcut hg,
      freshHeightPotential, ite_eq_right hg]
    ring

theorem activeHeightProduct_nonneg (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) : 0 ≤ activeHeightProduct p cutoff hcutoff roots h s :=
  Finset.prod_nonneg (fun v _ ↦ heightFactor_nonneg _ _ _ _ _ _ v)

/-- Recovery always has at least as large a CDF potential as infection. -/
theorem freshHeightPotential_infect_le_recover (p : unitInterval) (cutoff : ℕ)
    (hcutoff : 0 < cutoff) (roots : Finset ℕ) (h : ℕ) (s : State) (v : Fin s.vertices)
    (hv : v ∈ s.active) (hcut : cutoff ≤ s.vertices) :
    freshHeightPotential p cutoff hcutoff roots h (infect s v) ≤
      freshHeightPotential p cutoff hcutoff roots h (recover s v) := by
  classical
  by_cases hg : belowFreshHeight cutoff hcutoff roots h s
  · rw [freshHeightPotential_recover_of_good _ _ _ _ _ _ _ hg,
      freshHeightPotential_infect_of_good _ _ _ _ _ _ _ hcut hg,
      ← activeHeightProduct_recover_mul p cutoff hcutoff roots h hv]
    have hf := mul_le_mul
      (heightFactor_le_one p cutoff hcutoff roots h (infect s v) (Fin.last s.vertices))
      (heightFactor_le_one p cutoff hcutoff roots h s v)
      (heightFactor_nonneg p cutoff hcutoff roots h s v) (show (0 : ℝ) ≤ 1 by norm_num)
    have hm := mul_le_mul_of_nonneg_right hf
      (activeHeightProduct_nonneg p cutoff hcutoff roots h (recover s v))
    nlinarith only [hm]
  · rw [freshHeightPotential_recover_of_bad _ _ _ _ _ _ _ hg,
      freshHeightPotential_infect_of_bad _ _ _ _ _ _ _ hcut hg]

/-- A recovery probability above the reference parameter gives nonnegative
one-step drift, directly on the actual infection/recovery states. -/
theorem freshHeightPotential_subharmonic (p : unitInterval) (hp : 0 < (p : ℝ))
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (roots : Finset ℕ) (h : ℕ)
    (s : State) (v : Fin s.vertices) (hv : v ∈ s.active) (hcut : cutoff ≤ s.vertices)
    {r : ℝ} (hpr : (p : ℝ) ≤ r) :
    freshHeightPotential p cutoff hcutoff roots h s ≤
      r * freshHeightPotential p cutoff hcutoff roots h (recover s v) +
        (1 - r) * freshHeightPotential p cutoff hcutoff roots h (infect s v) := by
  have heq := freshHeightPotential_one_step p hp cutoff hcutoff roots h s v hv hcut
  have hm := freshHeightPotential_infect_le_recover p cutoff hcutoff roots h s v hv hcut
  have hn := mul_nonneg (sub_nonneg.mpr hpr) (sub_nonneg.mpr hm)
  nlinarith only [heq, hn]

/-- A recovery probability below the reference parameter gives nonpositive
one-step drift. -/
theorem freshHeightPotential_superharmonic (p : unitInterval) (hp : 0 < (p : ℝ))
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (roots : Finset ℕ) (h : ℕ)
    (s : State) (v : Fin s.vertices) (hv : v ∈ s.active) (hcut : cutoff ≤ s.vertices)
    {r : ℝ} (hrp : r ≤ (p : ℝ)) :
    r * freshHeightPotential p cutoff hcutoff roots h (recover s v) +
        (1 - r) * freshHeightPotential p cutoff hcutoff roots h (infect s v) ≤
      freshHeightPotential p cutoff hcutoff roots h s := by
  have heq := freshHeightPotential_one_step p hp cutoff hcutoff roots h s v hv hcut
  have hm := freshHeightPotential_infect_le_recover p cutoff hcutoff roots h s v hv hcut
  have hn := mul_nonneg (sub_nonneg.mpr hrp) (sub_nonneg.mpr hm)
  nlinarith only [heq, hn]

/-- At extinction the potential is exactly the height-CDF indicator. -/
theorem freshHeightPotential_terminal (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h : ℕ) (s : State) (hs : s.active = ∅) :
    freshHeightPotential p cutoff hcutoff roots h s =
      if belowFreshHeight cutoff hcutoff roots h s then 1 else 0 := by
  classical
  simp [freshHeightPotential, activeHeightProduct, hs]

/-- At the cutoff every old vertex has fresh depth zero. -/
theorem belowFreshHeight_at_cutoff (roots : Finset ℕ) {h : ℕ} (hh : 0 < h) (s : State) :
    belowFreshHeight s.vertices s.tree.size_pos roots h s := by
  intro v _
  rw [Tree.freshDepth_of_old _ _ _ v v.isLt]
  exact hh

theorem heightFactor_at_cutoff (p : unitInterval) (roots : Finset ℕ) (h : ℕ)
    (s : State) (v : Fin s.vertices) :
    heightFactor p s.vertices s.tree.size_pos roots h s v =
      if v.val ∈ roots then Branching.extinctionProbability p h else 1 := by
  classical
  have hsel : selectedOutgrowth s.vertices s.tree.size_pos roots s v ↔ v.val ∈ roots := by
    simp [selectedOutgrowth]
  by_cases hv : v.val ∈ roots
  · simp only [heightFactor, ite_eq_left (hsel.mpr hv), ite_eq_left hv]
    rw [Tree.freshDepth_of_old _ _ _ v v.isLt, Nat.sub_zero]
  · simp only [heightFactor, ite_eq_right (fun hx ↦ hv (hsel.mp hx)), ite_eq_right hv]

/-- The initial CDF potential is the independent-forest product with one
factor for each selected active cutoff root. -/
theorem freshHeightPotential_at_cutoff (p : unitInterval) (roots : Finset ℕ)
    {h : ℕ} (hh : 0 < h) (s : State) :
    freshHeightPotential p s.vertices s.tree.size_pos roots h s =
      Branching.extinctionProbability p h ^ (s.active.filter (fun v ↦ v.val ∈ roots)).card := by
  classical
  rw [freshHeightPotential, ite_eq_left (belowFreshHeight_at_cutoff roots hh s)]
  unfold activeHeightProduct
  simp_rw [heightFactor_at_cutoff]
  rw [Finset.prod_ite]
  simp

end Model
end HeightPaper
