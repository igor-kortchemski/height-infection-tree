module

public import HeightPaper.Probability.CorrectedCouplingSelection
public import Mathlib.Probability.UniformOn

/-!
# Conditioning a uniform active-vertex draw on a smaller active set

When the smaller active set is contained in the larger one, conditioning one
uniform draw from the larger set on hitting the smaller set gives exactly its
uniform law.  This is the one-trial rejection-sampling identity used in the
corrected coupling.  The stopping-time law of the first accepted draw remains
to be proved.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HeightPaper.CountCoupling

theorem uniformOfFinset_eq_uniformOn (s : Finset ℕ) :
    Measure.uniformOfFinset s = uniformOn (s : Set ℕ) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.uniformOfFinset_apply_singleton]
  have hh := uniformOn_apply_finset (s := s) (t := ({x} : Finset ℕ))
  have hsingleton : ({x} : Set ℕ) = (({x} : Finset ℕ) : Set ℕ) := by ext y; simp
  rw [hsingleton]
  rw [hh]
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx]

/-- Conditional uniformity of a draw that hits a nested active set. -/
theorem uniformOfFinset_cond_subset (A B : Finset ℕ) (hAB : A ⊆ B) :
    (Measure.uniformOfFinset B)[| (A : Set ℕ)] =
      Measure.uniformOfFinset A := by
  rw [uniformOfFinset_eq_uniformOn B, uniformOfFinset_eq_uniformOn A]
  have hABset : (A : Set ℕ) ⊆ (B : Set ℕ) := fun _ hx ↦ hAB hx
  have hinter : (B : Set ℕ) ∩ (A : Set ℕ) = (A : Set ℕ) :=
    Set.inter_eq_right.mpr hABset
  have hfinite : Measure.count (B : Set ℕ) ≠ ∞ :=
    (Measure.count_apply_lt_top.2 B.finite_toSet).ne
  change (Measure.count[| (B : Set ℕ)])[| (A : Set ℕ)] =
    Measure.count[| (A : Set ℕ)]
  rw [cond_cond_eq_cond_inter' B.measurableSet A.measurableSet hfinite,
    hinter]

end HeightPaper.CountCoupling
