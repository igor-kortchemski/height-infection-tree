module

public import HeightPaper.Model.DepthReset
public import HeightPaper.Model.PrescribedPath
public import Mathlib.Data.Finset.Sort

/-! # The ordered active-depth list is the actual tree profile -/

@[expose] public section

namespace HeightPaper.Model

def activeDepths (s : State) : List ℕ := (s.active.sort (· ≤ ·)).map s.tree.depth

@[simp] theorem activeDepths_length (s : State) : (activeDepths s).length = infectious s := by
  simp [activeDepths, infectious]

theorem activeDepths_depthWeight (w : ℝ) (s : State) :
    depthWeight w (activeDepths s) = activeWeight w s := by
  unfold depthWeight activeDepths activeWeight
  rw [List.map_map, ← List.sum_toFinset _ (s.active.sort_nodup (· ≤ ·)), Finset.sort_toFinset]
  rfl

private theorem sort_insert_greatest {α : Type*} [LinearOrder α]
    (s : Finset α) (a : α) (ha : ∀ b ∈ s, b < a) :
    (insert a s).sort (· ≤ ·) = s.sort (· ≤ ·) ++ [a] := by
  have hs : (s.sort (· ≤ ·) ++ [a]).SortedLT := by
    rw [List.sortedLT_append]
    refine ⟨s.sortedLT_sort, by simp [List.sortedLT_iff_pairwise], ?_⟩
    intro b hb c hc
    simp only [List.mem_singleton] at hc
    subst c
    exact ha b ((Finset.mem_sort _).mp hb)
  apply (insert a s).sortedLT_sort.eq_of_mem_iff hs
  intro b
  simp [or_comm]

private theorem sort_erase_eq {α : Type*} [LinearOrder α]
    (s : Finset α) (a : α) :
    (s.erase a).sort (· ≤ ·) = (s.sort (· ≤ ·)).erase a := by
  apply List.Pairwise.eq_of_mem_iff (s.erase a).sortedLT_sort.pairwise
    (s.sortedLT_sort.pairwise.erase a)
  intro b
  simp only [Finset.mem_sort, Finset.mem_erase, (s.sort_nodup (· ≤ ·)).mem_erase_iff]

theorem activeDepths_getD_rank (s : State) (r : Fin s.active.card) :
    ((activeDepths s)[r.val]?).getD 0 = s.tree.depth (s.active.orderEmbOfFin rfl r) := by
  have hr : r.val < (s.active.sort (· ≤ ·)).length := by simp
  simp only [activeDepths, List.getElem?_map, List.getElem?_eq_getElem hr,
    Option.map_some, Option.getD_some, Finset.orderEmbOfFin_apply, Fin.getElem_fin]

/-- Recovery removes exactly the chosen ordered active rank, even if several
active vertices have equal depths. -/
theorem activeDepths_recover_rank (s : State) (r : Fin s.active.card) :
    activeDepths (recover s (s.active.orderEmbOfFin rfl r)) =
      (activeDepths s).eraseIdx r.val := by
  unfold activeDepths
  change ((s.active.erase (s.active.orderEmbOfFin rfl r)).sort (· ≤ ·)).map s.tree.depth = _
  rw [sort_erase_eq, Finset.orderEmbOfFin_apply, Fin.getElem_fin,
    (s.active.sort_nodup (· ≤ ·)).erase_getElem r.val (by simp),
    List.eraseIdx_map]

/-- Infection appends the child after all old active vertices in birth order. -/
theorem activeDepths_infect (s : State) (v : Fin s.vertices) :
    activeDepths (infect s v) = activeDepths s ++ [s.tree.depth v + 1] := by
  have hgreat : ∀ b ∈ s.active.map Fin.castSuccEmb, b < Fin.last s.vertices := by
    intro b hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hb
    exact a.isLt
  have hmap : (s.active.map Fin.castSuccEmb).sort (· ≤ ·) =
      (s.active.sort (· ≤ ·)).map Fin.castSuccEmb := by
    symm
    exact Finset.map_sort Fin.castSuccEmb s.active (· ≤ ·) (· ≤ ·)
      (fun _ _ _ _ ↦ Iff.rfl)
  unfold activeDepths
  change ((insert (Fin.last s.vertices) (s.active.map Fin.castSuccEmb)).sort (· ≤ ·)).map
    (s.tree.attach v).depth = _
  rw [sort_insert_greatest _ _ hgreat, hmap, List.map_append, List.map_map]
  simp only [List.map_cons, List.map_nil, Tree.depth_attach_new]
  congr 1
  apply List.map_congr_left
  intro a _
  exact Tree.depth_attach_old s.tree v a

/-- The list dynamics are exactly the existing prescribed tree update. -/
theorem activeDepths_prescribedUpdate_rank (birth : Bool) (s : State) (r : Fin s.active.card) :
    activeDepths (prescribedUpdate birth s (s.active.orderEmbOfFin rfl r)) =
      depthUpdate birth r.val (activeDepths s) := by
  cases birth with
  | false => exact activeDepths_recover_rank s r
  | true =>
      simpa only [prescribedUpdate, depthUpdate, ↓reduceIte, activeDepths_getD_rank] using
        activeDepths_infect s (s.active.orderEmbOfFin rfl r)

theorem activeDepths_le_vertices (s : State) : ∀ d ∈ activeDepths s, d ≤ s.vertices := by
  intro d hd
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hd
  exact (Tree.depth_lt_size s.tree v).le

end HeightPaper.Model
