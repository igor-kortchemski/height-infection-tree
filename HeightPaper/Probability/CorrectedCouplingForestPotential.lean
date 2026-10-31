module

public import HeightPaper.Probability.CorrectedCouplingPlaneFreeze
public import HeightPaper.Combinatorics.FinitePlaneShape

/-!
# Completion potentials for all root components at once

The product of the individual completion potentials is harmonic for every
selected vertex, including a proposal outside the current active forest.
Its terminal value is the indicator of the entire ordered forest shape.
-/

@[expose] public section

open scoped BigOperators

namespace HeightPaper.CountCoupling

open PlaneForward
open scoped Classical

noncomputable def forestShape (N : ℕ) (s : CouplingGenealogy) : Fin N → FiniteShape :=
  fun i ↦ toFiniteShape (s.planeComponent (Finset.range N) i.val)

noncomputable def forestCompletionPotential (N : ℕ) (t : Fin N → FiniteShape)
    (a : ℝ) (s : CouplingGenealogy) : ℝ :=
  ∏ i, completionPotential (t i).1 a (s.planeComponent (Finset.range N) i.val)

theorem forestCompletionPotential_nonneg (N : ℕ) (t : Fin N → FiniteShape)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (s : CouplingGenealogy) :
    0 ≤ forestCompletionPotential N t a s :=
  Finset.prod_nonneg (fun _ _ ↦ completionPotential_nonneg _ ha0 ha1 _)

theorem forestCompletionPotential_le_one (N : ℕ) (t : Fin N → FiniteShape)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (s : CouplingGenealogy) :
    forestCompletionPotential N t a s ≤ 1 := by
  unfold forestCompletionPotential
  apply Finset.prod_le_one₀
  · exact fun _ _ ↦ completionPotential_nonneg _ ha0 ha1 _
  · exact fun _ _ ↦ completionPotential_le_one _ ha0 ha1 _

theorem forestCompletionPotential_harmonic (N : ℕ) (t : Fin N → FiniteShape)
    (a : ℝ) (s : CouplingGenealogy) (hs : s.Valid (Finset.range N))
    (v fresh : ℕ) (hgt : ∀ x ∈ s.carrier.vertices, x < fresh) :
    a * forestCompletionPotential N t a (s.update v fresh false) +
      (1 - a) * forestCompletionPotential N t a (s.update v fresh true) =
        forestCompletionPotential N t a s := by
  by_cases hv : v ∈ s.carrier.active
  · have hr : s.rootOf (Finset.range N) v < N := Finset.mem_range.mp
      (s.rootOf_mem_roots hs (s.carrier.active_sub_vertices hv))
    let i : Fin N := ⟨s.rootOf (Finset.range N) v, hr⟩
    let g := s.planeComponent (Finset.range N) i.val
    let z := s.orderedAddress (Finset.range N) v
    let P := ∏ k ∈ Finset.univ.erase i,
      completionPotential (t k).1 a (s.planeComponent (Finset.range N) k.val)
    have hprod (b : Bool) : forestCompletionPotential N t a (s.update v fresh b) =
        completionPotential (t i).1 a (PlaneForward.step g b z) * P := by
      unfold forestCompletionPotential
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      apply congrArg₂ (· * ·)
      · rw [s.planeComponent_update hs v fresh hgt b i.val]
        simp only [hv, and_self, ↓reduceIte, i]
        rfl
      · apply Finset.prod_congr rfl
        intro k hk
        have hki : k ≠ i := (Finset.mem_erase.mp hk).1
        have hrk : s.rootOf (Finset.range N) v ≠ k.val := by
          intro he
          exact hki (Fin.ext he.symm)
        rw [s.planeComponent_update hs v fresh hgt b k.val, ite_eq_right (fun h ↦ hrk h.2)]
    have hbase : forestCompletionPotential N t a s = completionPotential (t i).1 a g * P := by
      exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [hprod false, hprod true, hbase]
    calc
      _ = (a * completionPotential (t i).1 a (PlaneForward.step g false z) +
          (1 - a) * completionPotential (t i).1 a (PlaneForward.step g true z)) * P := by ring
      _ = _ := by rw [completionPotential_step_harmonic
        (s.planeComponent_valid hs (Finset.mem_range.mpr i.isLt)) (t i).2.1]
  · rw [s.update_eq_of_not_active hv false, s.update_eq_of_not_active hv true]
    ring

theorem CouplingGenealogy.planeComponent_initial (roots : Finset ℕ) {root : ℕ} (hr : root ∈ roots) :
    (CouplingGenealogy.initial roots).planeComponent roots root = PlaneForward.initial := by
  have hc : (CouplingGenealogy.initial roots).component roots root = {root} := by
    ext x
    rw [CouplingGenealogy.component, Finset.mem_filter, Finset.mem_singleton]
    change (x ∈ roots ∧ (CouplingGenealogy.initial roots).rootOf roots x = root) ↔ x = root
    constructor
    · rintro ⟨hx, hxroot⟩
      simpa only [CouplingGenealogy.rootOf, hx, ↓reduceIte] using hxroot
    · rintro rfl
      exact ⟨hr, by simp [CouplingGenealogy.rootOf, hr]⟩
  have ha : (CouplingGenealogy.initial roots).carrier.active.filter
      (fun x ↦ (CouplingGenealogy.initial roots).rootOf roots x = root) = {root} := hc
  apply PlaneForward.State.ext_vertices_active
  · change ((CouplingGenealogy.initial roots).component roots root).image _ = {[]}
    rw [hc, Finset.image_singleton, (CouplingGenealogy.initial roots).orderedAddress_root roots hr]
  · change ((CouplingGenealogy.initial roots).carrier.active.filter _).image _ = {[]}
    rw [ha, Finset.image_singleton, (CouplingGenealogy.initial roots).orderedAddress_root roots hr]

theorem forestCompletionPotential_initial (N : ℕ) (t : Fin N → FiniteShape) (a : ℝ) :
    forestCompletionPotential N t a (CouplingGenealogy.initial (Finset.range N)) =
      ∏ i, a ^ (t i).size * (1 - a) ^ ((t i).size - 1) := by
  apply Finset.prod_congr rfl
  intro i _
  rw [CouplingGenealogy.planeComponent_initial _ (Finset.mem_range.mpr i.isLt),
    completionPotential_initial (t i).2.1]
  rfl

theorem forestCompletionPotential_of_empty (N : ℕ) (t : Fin N → FiniteShape) (a : ℝ)
    (s : CouplingGenealogy) (hs : s.Valid (Finset.range N)) (he : s.carrier.active = ∅) :
    forestCompletionPotential N t a s = if forestShape N s = t then 1 else 0 := by
  have hcomp (i : Fin N) : (s.planeComponent (Finset.range N) i.val).active = ∅ := by
    simp only [CouplingGenealogy.planeComponent, he, Finset.filter_empty, Finset.image_empty]
  have hprod : forestCompletionPotential N t a s =
      ∏ i, if forestShape N s i = t i then (1 : ℝ) else 0 := by
    apply Finset.prod_congr rfl
    intro i _
    exact completionPotential_of_empty_shape
      (s.planeComponent_valid hs (Finset.mem_range.mpr i.isLt)) (hcomp i) (t i) a
  rw [hprod]
  by_cases ht : forestShape N s = t
  · simp [ht]
  · rw [ite_eq_right ht]
    obtain ⟨i, hi⟩ : ∃ i, forestShape N s i ≠ t i := by
      by_contra hn
      apply ht
      exact funext (not_exists_not.mp hn)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

end HeightPaper.CountCoupling
