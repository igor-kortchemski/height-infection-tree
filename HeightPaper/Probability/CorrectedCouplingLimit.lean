module

public import HeightPaper.Probability.CorrectedCouplingComponents

/-!
# Stability of finite genealogies during the corrected coupling

Every birth uses a label fresh for the upper forest.  When the deterministic
sandwich is ordered, this label is fresh for each smaller forest as well.
Consequently vertices are never removed and parent edges of old vertices
never change.  These are the compatibility facts needed to form the limiting
forests from their finite prefixes.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

/-- Inclusion of vertex sets together with agreement of parent pointers on
the older forest.  Active sets are omitted because recovery removes activity. -/
def CouplingGenealogy.TreeLE (a b : CouplingGenealogy) : Prop :=
  a.carrier.vertices ⊆ b.carrier.vertices ∧
    ∀ x ∈ a.carrier.vertices, a.parent x = b.parent x

theorem CouplingGenealogy.treeLE_refl (s : CouplingGenealogy) : s.TreeLE s :=
  ⟨Finset.Subset.rfl, fun _ _ ↦ rfl⟩

theorem CouplingGenealogy.treeLE_trans {a b c : CouplingGenealogy}
    (hab : a.TreeLE b) (hbc : b.TreeLE c) : a.TreeLE c := by
  refine ⟨hab.1.trans hbc.1, ?_⟩
  intro x hx
  exact (hab.2 x hx).trans (hbc.2 x (hab.1 hx))

/-- A step may freeze an active vertex but never removes an existing vertex. -/
theorem CouplingGenealogy.vertices_subset_update
    (s : CouplingGenealogy) (v fresh : ℕ) (birth : Bool) :
    s.carrier.vertices ⊆ (s.update v fresh birth).carrier.vertices := by
  by_cases hv : v ∈ s.carrier.active
  · cases birth <;> simp [CouplingGenealogy.update,
      CouplingCarrier.update, hv]
  · simp [CouplingGenealogy.update, CouplingCarrier.update, hv]

/-- A fresh birth label cannot alter the parent pointer of an old vertex. -/
theorem CouplingGenealogy.parent_update_old
    (s : CouplingGenealogy) (v fresh : ℕ)
    (hfresh : fresh ∉ s.carrier.vertices) (birth : Bool)
    (x : ℕ) (hx : x ∈ s.carrier.vertices) :
    s.parent x = (s.update v fresh birth).parent x := by
  have hne : x ≠ fresh := fun h ↦ hfresh (h ▸ hx)
  by_cases hv : v ∈ s.carrier.active
  · cases birth <;> simp [CouplingGenealogy.update, hv,
      Function.update_of_ne hne]
  · simp [CouplingGenealogy.update, hv]

theorem CouplingGenealogy.treeLE_update
    (s : CouplingGenealogy) (v fresh : ℕ)
    (hfresh : fresh ∉ s.carrier.vertices) (birth : Bool) :
    s.TreeLE (s.update v fresh birth) :=
  ⟨s.vertices_subset_update v fresh birth,
    s.parent_update_old v fresh hfresh birth⟩

def CouplingTriple.TreeLE (s t : CouplingTriple) : Prop :=
  s.lower.TreeLE t.lower ∧ s.middle.TreeLE t.middle ∧
    s.upper.TreeLE t.upper

theorem CouplingTriple.treeLE_trans {a b c : CouplingTriple}
    (hab : a.TreeLE b) (hbc : b.TreeLE c) : a.TreeLE c :=
  ⟨CouplingGenealogy.treeLE_trans hab.1 hbc.1,
    CouplingGenealogy.treeLE_trans hab.2.1 hbc.2.1,
    CouplingGenealogy.treeLE_trans hab.2.2 hbc.2.2⟩

/-- All three forests extend their existing tree edges at each common draw. -/
theorem CouplingTriple.treeLE_step {s : CouplingTriple}
    (hs : s.Ordered) (p q r u : ℝ) (v : ℕ) :
    s.TreeLE (s.step p q r u v) := by
  have hmid : s.upper.fresh ∉ s.middle.carrier.vertices :=
    fun hx ↦ s.upper.fresh_not_mem (hs.2.1.1 hx)
  have hlo : s.upper.fresh ∉ s.lower.carrier.vertices :=
    fun hx ↦ hmid (hs.1.1.1 hx)
  exact ⟨s.lower.treeLE_update v s.upper.fresh hlo _,
    s.middle.treeLE_update v s.upper.fresh hmid _,
    s.upper.treeLE_update v s.upper.fresh s.upper.fresh_not_mem _⟩

/-- Every finite prefix extends the three starting trees if the corrected
active-step bounds hold along that prefix. -/
theorem CouplingTriple.treeLE_run {s : CouplingTriple}
    (hs : s.Ordered) {p q : ℝ} (draws : List CouplingDraw)
    (hgood : s.RunGood p q draws) :
    s.TreeLE (s.run p q draws) := by
  induction draws generalizing s with
  | nil =>
      exact ⟨s.lower.treeLE_refl,
        s.middle.treeLE_refl, s.upper.treeLE_refl⟩
  | cons d ds ih =>
      have hstep := s.treeLE_step hs p q d.recovery d.uniform d.selected
      have horder := s.step_ordered_of_middle_active hs
        (p := p) (q := q) (r := d.recovery) (u := d.uniform)
        hgood.1 d.selected
      have htail := ih (s := s.step p q d.recovery d.uniform d.selected)
        horder hgood.2
      simpa [CouplingTriple.run, List.foldl_cons] using
        CouplingTriple.treeLE_trans hstep htail

theorem CouplingTriple.run_append (s : CouplingTriple)
    (p q : ℝ) (xs ys : List CouplingDraw) :
    s.run p q (xs ++ ys) = (s.run p q xs).run p q ys := by
  simp [CouplingTriple.run, List.foldl_append]

theorem CouplingTriple.runGood_append (s : CouplingTriple)
    (p q : ℝ) (xs ys : List CouplingDraw) :
    s.RunGood p q (xs ++ ys) ↔
      s.RunGood p q xs ∧ (s.run p q xs).RunGood p q ys := by
  induction xs generalizing s with
  | nil => simp [CouplingTriple.RunGood, CouplingTriple.run]
  | cons d ds ih =>
      simp only [List.cons_append, CouplingTriple.RunGood,
        CouplingTriple.run, List.foldl_cons]
      rw [ih]
      tauto

/-- A longer good prefix extends the tree edges of a shorter one. -/
theorem CouplingTriple.treeLE_run_append {s : CouplingTriple}
    (hs : s.Ordered) {p q : ℝ} (xs ys : List CouplingDraw)
    (hgood : s.RunGood p q (xs ++ ys)) :
    (s.run p q xs).TreeLE (s.run p q (xs ++ ys)) := by
  obtain ⟨hx, hy⟩ := (s.runGood_append p q xs ys).mp hgood
  have horder := s.run_ordered_of_good hs xs hx
  have htree := (s.run p q xs).treeLE_run horder ys hy
  simpa only [s.run_append] using htree

/-- The infinite sequence of finite coupled forests driven by common draws. -/
noncomputable def CouplingTriple.trajectory
    (s : CouplingTriple) (p q : ℝ) (d : ℕ → CouplingDraw) :
    ℕ → CouplingTriple
  | 0 => s
  | k + 1 =>
      (s.trajectory p q d k).step p q (d k).recovery
        (d k).uniform (d k).selected

/-- The corrected bounds at every draw while the middle forest is active. -/
def CouplingTriple.TrajectoryGood
    (s : CouplingTriple) (p q : ℝ) (d : ℕ → CouplingDraw) : Prop :=
  ∀ k, (s.trajectory p q d k).middle.carrier.active.Nonempty →
    p ≤ (d k).recovery ∧ (d k).recovery ≤ q

theorem CouplingTriple.trajectory_ordered
    {s : CouplingTriple} (hs : s.Ordered)
    {p q : ℝ} {d : ℕ → CouplingDraw}
    (hgood : s.TrajectoryGood p q d) (k : ℕ) :
    (s.trajectory p q d k).Ordered := by
  induction k with
  | zero => exact hs
  | succ k ih =>
      change ((s.trajectory p q d k).step p q (d k).recovery
        (d k).uniform (d k).selected).Ordered
      exact (s.trajectory p q d k).step_ordered_of_middle_active
        ih (u := (d k).uniform) (hgood k) (d k).selected

theorem CouplingTriple.trajectory_treeLE_step
    {s : CouplingTriple} (hs : s.Ordered)
    {p q : ℝ} {d : ℕ → CouplingDraw}
    (hgood : s.TrajectoryGood p q d) (k : ℕ) :
    (s.trajectory p q d k).TreeLE (s.trajectory p q d (k + 1)) := by
  change (s.trajectory p q d k).TreeLE
    ((s.trajectory p q d k).step p q (d k).recovery
      (d k).uniform (d k).selected)
  exact (s.trajectory p q d k).treeLE_step
    (s.trajectory_ordered hs hgood k) p q
    (d k).recovery (d k).uniform (d k).selected

/-- The finite genealogies form a directed system of rooted trees. -/
theorem CouplingTriple.trajectory_treeLE_of_le
    {s : CouplingTriple} (hs : s.Ordered)
    {p q : ℝ} {d : ℕ → CouplingDraw}
    (hgood : s.TrajectoryGood p q d)
    {k m : ℕ} (hkm : k ≤ m) :
    (s.trajectory p q d k).TreeLE (s.trajectory p q d m) := by
  induction m with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      exact ⟨(s.trajectory p q d 0).lower.treeLE_refl,
        (s.trajectory p q d 0).middle.treeLE_refl,
        (s.trajectory p q d 0).upper.treeLE_refl⟩
  | succ m ih =>
      by_cases hk : k ≤ m
      · exact CouplingTriple.treeLE_trans (ih hk)
          (s.trajectory_treeLE_step hs hgood m)
      · have heq : k = m + 1 := by omega
        subst k
        exact ⟨(s.trajectory p q d (m + 1)).lower.treeLE_refl,
          (s.trajectory p q d (m + 1)).middle.treeLE_refl,
          (s.trajectory p q d (m + 1)).upper.treeLE_refl⟩

theorem CouplingTriple.trajectory_valid
    {s : CouplingTriple} {roots : Finset ℕ}
    (hs : s.Ordered) (hv : s.Valid roots)
    {p q : ℝ} {d : ℕ → CouplingDraw}
    (hgood : s.TrajectoryGood p q d) (k : ℕ) :
    (s.trajectory p q d k).Valid roots := by
  induction k with
  | zero => exact hv
  | succ k ih =>
      change ((s.trajectory p q d k).step p q (d k).recovery
        (d k).uniform (d k).selected).Valid roots
      exact (s.trajectory p q d k).step_valid
        (s.trajectory_ordered hs hgood k) ih p q
        (d k).recovery (d k).uniform (d k).selected

def CouplingTriple.limitLowerComponent
    (s : CouplingTriple) (p q : ℝ) (d : ℕ → CouplingDraw)
    (roots : Finset ℕ) (r : ℕ) : Set ℕ :=
  {x | ∃ k, x ∈ (s.trajectory p q d k).lower.component roots r}

def CouplingTriple.limitMiddleComponent
    (s : CouplingTriple) (p q : ℝ) (d : ℕ → CouplingDraw)
    (roots : Finset ℕ) (r : ℕ) : Set ℕ :=
  {x | ∃ k, x ∈ (s.trajectory p q d k).middle.component roots r}

def CouplingTriple.limitUpperComponent
    (s : CouplingTriple) (p q : ℝ) (d : ℕ → CouplingDraw)
    (roots : Finset ℕ) (r : ℕ) : Set ℕ :=
  {x | ∃ k, x ∈ (s.trajectory p q d k).upper.component roots r}

/-- The corrected active-step event yields componentwise vertex inclusion in
the limiting forests, with no bound needed after middle extinction. -/
theorem CouplingTriple.limit_component_sandwich
    {s : CouplingTriple} {roots : Finset ℕ}
    (hs : s.Ordered) (hv : s.Valid roots)
    {p q : ℝ} {d : ℕ → CouplingDraw}
    (hgood : s.TrajectoryGood p q d) (r : ℕ) :
    s.limitLowerComponent p q d roots r ⊆
      s.limitMiddleComponent p q d roots r ∧
    s.limitMiddleComponent p q d roots r ⊆
      s.limitUpperComponent p q d roots r := by
  constructor
  · rintro x ⟨k, hx⟩
    have ho := s.trajectory_ordered hs hgood k
    have hvalid := s.trajectory_valid hs hv hgood k
    exact ⟨k, CouplingGenealogy.component_subset_of_LE
      ho.1 hvalid.1 r hx⟩
  · rintro x ⟨k, hx⟩
    have ho := s.trajectory_ordered hs hgood k
    have hvalid := s.trajectory_valid hs hv hgood k
    exact ⟨k, CouplingGenealogy.component_subset_of_LE
      ho.2 hvalid.2.1 r hx⟩

def CouplingTriple.limitLowerEdges
    (s : CouplingTriple) (p q : ℝ) (d : ℕ → CouplingDraw)
    (roots : Finset ℕ) (r : ℕ) : Set (ℕ × ℕ) :=
  {e | e.2 ∉ roots ∧ ∃ k,
    e.2 ∈ (s.trajectory p q d k).lower.component roots r ∧
    (s.trajectory p q d k).lower.parent e.2 = e.1}

def CouplingTriple.limitMiddleEdges
    (s : CouplingTriple) (p q : ℝ) (d : ℕ → CouplingDraw)
    (roots : Finset ℕ) (r : ℕ) : Set (ℕ × ℕ) :=
  {e | e.2 ∉ roots ∧ ∃ k,
    e.2 ∈ (s.trajectory p q d k).middle.component roots r ∧
    (s.trajectory p q d k).middle.parent e.2 = e.1}

def CouplingTriple.limitUpperEdges
    (s : CouplingTriple) (p q : ℝ) (d : ℕ → CouplingDraw)
    (roots : Finset ℕ) (r : ℕ) : Set (ℕ × ℕ) :=
  {e | e.2 ∉ roots ∧ ∃ k,
    e.2 ∈ (s.trajectory p q d k).upper.component roots r ∧
    (s.trajectory p q d k).upper.parent e.2 = e.1}

/-- The limiting component inclusion preserves every parent edge. -/
theorem CouplingTriple.limit_edge_sandwich
    {s : CouplingTriple} {roots : Finset ℕ}
    (hs : s.Ordered) (hv : s.Valid roots)
    {p q : ℝ} {d : ℕ → CouplingDraw}
    (hgood : s.TrajectoryGood p q d) (r : ℕ) :
    s.limitLowerEdges p q d roots r ⊆
      s.limitMiddleEdges p q d roots r ∧
    s.limitMiddleEdges p q d roots r ⊆
      s.limitUpperEdges p q d roots r := by
  constructor
  · rintro e ⟨hroot, k, hx, he⟩
    have ho := s.trajectory_ordered hs hgood k
    have hvalid := s.trajectory_valid hs hv hgood k
    have hvertex := (Finset.mem_filter.mp hx).1
    exact ⟨hroot, k, CouplingGenealogy.component_subset_of_LE
      ho.1 hvalid.1 r hx, (ho.1.2 e.2 hvertex).symm.trans he⟩
  · rintro e ⟨hroot, k, hx, he⟩
    have ho := s.trajectory_ordered hs hgood k
    have hvalid := s.trajectory_valid hs hv hgood k
    have hvertex := (Finset.mem_filter.mp hx).1
    exact ⟨hroot, k, CouplingGenealogy.component_subset_of_LE
      ho.2 hvalid.2.1 r hx, (ho.2.2 e.2 hvertex).symm.trans he⟩

end HeightPaper.CountCoupling
