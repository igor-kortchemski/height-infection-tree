module

public import HeightPaper.Probability.CorrectedCouplingGenealogy

/-!
# Componentwise inclusion in the coupled forests

The shared parent-pointer invariant implies that every vertex retained by a
smaller forest stays attached to the same initial root in the larger forest.
This is the componentwise form of the deterministic tree sandwich.
-/

@[expose] public section

namespace HeightPaper.CountCoupling

/-- Follow decreasing parent labels until an initial root is reached.
Outside a valid forest this totalized definition stops at any nondecreasing
parent pointer. -/
def CouplingGenealogy.rootOf (s : CouplingGenealogy)
    (roots : Finset ℕ) (x : ℕ) : ℕ :=
  if x ∈ roots then x
  else if _h : s.parent x < x then s.rootOf roots (s.parent x)
  else x
termination_by x

/-- A component consists of all vertices descending from one initial root. -/
def CouplingGenealogy.component (s : CouplingGenealogy)
    (roots : Finset ℕ) (r : ℕ) : Finset ℕ :=
  s.carrier.vertices.filter (fun x ↦ s.rootOf roots x = r)

/-- Parent agreement on the smaller forest preserves its root labels. -/
theorem CouplingGenealogy.rootOf_eq_of_LE
    {a b : CouplingGenealogy} {roots : Finset ℕ}
    (hab : a.LE b) (ha : a.Valid roots)
    {x : ℕ} (hx : x ∈ a.carrier.vertices) :
    a.rootOf roots x = b.rootOf roots x := by
  induction x using Nat.strong_induction_on generalizing a b with
  | h x ih =>
      by_cases hr : x ∈ roots
      · simp [CouplingGenealogy.rootOf, hr]
      · obtain ⟨hp, hlt⟩ := ha.2 x hx hr
        have heq : a.parent x = b.parent x := hab.2 x hx
        calc
          a.rootOf roots x = a.rootOf roots (a.parent x) := by
            conv_lhs => rw [CouplingGenealogy.rootOf]
            simp only [hr, ↓reduceIte, dite_eq_left hlt]
          _ = b.rootOf roots (a.parent x) := ih (a.parent x) hlt hab ha hp
          _ = b.rootOf roots x := by
            conv_rhs => rw [CouplingGenealogy.rootOf]
            simp only [hr, ↓reduceIte, ← heq, dite_eq_left hlt]

/-- Forest inclusion is componentwise, with each component indexed by the
same initial root. -/
theorem CouplingGenealogy.component_subset_of_LE
    {a b : CouplingGenealogy} {roots : Finset ℕ}
    (hab : a.LE b) (ha : a.Valid roots) (r : ℕ) :
    a.component roots r ⊆ b.component roots r := by
  intro x hx
  have hmem : x ∈ a.carrier.vertices :=
    (Finset.mem_filter.mp hx).1
  have hroot : a.rootOf roots x = r :=
    (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  exact ⟨hab.1.1 hmem,
    (a.rootOf_eq_of_LE hab ha hmem).symm.trans hroot⟩

/-- The corrected deterministic triple has componentwise inclusion after
every finite run satisfying the corrected active-step bounds. -/
theorem CouplingTriple.run_component_sandwich
    {s : CouplingTriple} {roots : Finset ℕ}
    (hs : s.Ordered) (hv : s.Valid roots) {p q : ℝ}
    (draws : List CouplingDraw) (hgood : s.RunGood p q draws)
    (r : ℕ) :
    (s.run p q draws).lower.component roots r ⊆
      (s.run p q draws).middle.component roots r ∧
    (s.run p q draws).middle.component roots r ⊆
      (s.run p q draws).upper.component roots r := by
  have ho := s.run_ordered_of_good hs draws hgood
  have hvalid := s.run_valid_of_good hs hv draws hgood
  exact ⟨CouplingGenealogy.component_subset_of_LE ho.1 hvalid.1 r,
    CouplingGenealogy.component_subset_of_LE ho.2 hvalid.2.1 r⟩

end HeightPaper.CountCoupling
