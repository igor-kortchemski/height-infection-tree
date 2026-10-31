module

public import HeightPaper.Combinatorics.PlaneTree
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Algebra.BigOperators.Fin

/-!
Adapted from the generic Bienaymé-law utilities in the sibling `freezing1`
project, using the same pinned Lean and Mathlib 4.35.0.

# Independent groups of potential offspring coordinates

Group zero contains the root coordinate and unused addresses; group i+1
contains all addresses below child i+1. The explicit injection retains all
coordinates needed for any finite family of child subtrees. Its pushforward
under an iid field is the actual product of iid fields.
-/

@[expose] public section

namespace HeightPaper.PlaneTree

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

def branchAddress (k : ℕ) (q : Fin (k + 1) × Address) : Address :=
  if q.1 = 0 then match q.2 with
    | [] => []
    | j :: u => (k + 1 + j) :: u
  else q.1.val :: q.2

theorem branchAddress_injective (k : ℕ) : Function.Injective (branchAddress k) := by
  rintro ⟨i, u⟩ ⟨j, v⟩ h
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      cases u <;> cases v <;> simp_all [branchAddress]
    · cases u with
      | nil => simp [branchAddress, hj] at h
      | cons a u =>
          have hh : k + 1 + a = j.val := (List.cons.inj
            (by simpa [branchAddress, hj] using h)).1
          have hJ := j.isLt
          omega
  · by_cases hj : j = 0
    · subst j
      cases v with
      | nil => simp [branchAddress, hi] at h
      | cons b v =>
          have hh : i.val = k + 1 + b := (List.cons.inj
            (by simpa [branchAddress, hi] using h)).1
          have hI := i.isLt
          omega
    · have hh : i.val = j.val ∧ u = v := List.cons.inj
        (by simpa [branchAddress, hi, hj] using h)
      exact Prod.ext (Fin.ext hh.1) hh.2

theorem iid_branch_groups (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) :
    (Measure.infinitePi (fun _ : Address => μ)).map
        (fun f (i : Fin (k + 1)) (u : Address) => f (branchAddress k (i, u))) =
      Measure.pi (fun _ : Fin (k + 1) => Measure.infinitePi (fun _ : Address => μ)) := by
  have hi := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Address => μ) (branchAddress_injective k)
  calc
    _ = ((Measure.infinitePi (fun _ : Address => μ)).map
          (fun f q => f (branchAddress k q))).map
          (MeasurableEquiv.curry (Fin (k + 1)) Address ℕ) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [hi, Measure.infinitePi_map_curry
        (fun (_ : Fin (k + 1)) (_ : Address) => μ), Measure.infinitePi_eq_pi]

end HeightPaper.PlaneTree
