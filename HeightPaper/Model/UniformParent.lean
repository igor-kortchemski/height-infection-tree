module

public import HeightPaper.Model.PrescribedPath
public import Mathlib.Data.Finset.Sort
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Prescribed trees driven by uniform parent ranks

Active vertices are enumerated in infection-label order.  On the unit interval
the rank is exactly the source's ceiling rule, with zero-based indexing.  The
clamp only totalizes inputs outside `(0,1]`.
-/

@[expose] public section

open MeasureTheory

namespace HeightPaper.Model

noncomputable def uniformRank (m : ℕ) (hm : 0 < m) (v : ℝ) : Fin m :=
  ⟨min (Nat.ceil ((m : ℝ) * v) - 1) (m - 1), by omega⟩

theorem uniformRank_val_of_unit {m : ℕ} (hm : 0 < m) {v : ℝ}
    (_hv : 0 < v) (hv1 : v ≤ 1) :
    (uniformRank m hm v).val = Nat.ceil ((m : ℝ) * v) - 1 := by
  have hc : Nat.ceil ((m : ℝ) * v) ≤ m := by
    apply Nat.ceil_le.mpr
    nlinarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  exact min_eq_left (by omega)

theorem uniformRank_eq_iff {m : ℕ} (hm : 0 < m) {v : ℝ}
    (hv : 0 < v) (hv1 : v ≤ 1) (r : Fin m) :
    uniformRank m hm v = r ↔ (r.val : ℝ) / m < v ∧ v ≤ (r.val + 1 : ℝ) / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : 0 < Nat.ceil ((m : ℝ) * v) := Nat.ceil_pos.mpr (mul_pos hmR hv)
  rw [Fin.ext_iff, uniformRank_val_of_unit hm hv hv1]
  have he : Nat.ceil ((m : ℝ) * v) - 1 = r.val ↔
      Nat.ceil ((m : ℝ) * v) = r.val + 1 := by omega
  rw [he, Nat.ceil_eq_iff (by omega), Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    div_lt_iff₀ hmR, le_div_iff₀ hmR]
  simp only [mul_comm]

theorem measurable_uniformRank (m : ℕ) (hm : 0 < m) :
    Measurable (uniformRank m hm) := by
  exact (measurable_of_countable (fun a : ℕ ↦
    (⟨min (a - 1) (m - 1), by omega⟩ : Fin m))).comp
      (Nat.measurable_ceil.comp (measurable_id.const_mul (m : ℝ)))

/-- The increasing enumeration of the active infection labels. -/
noncomputable def activeAtRank (s : State) (r : Fin s.active.card) : Fin s.vertices :=
  s.active.orderEmbOfFin rfl r

theorem activeAtRank_mem (s : State) (r : Fin s.active.card) :
    activeAtRank s r ∈ s.active := Finset.orderEmbOfFin_mem s.active rfl r

theorem activeAtRank_injective (s : State) : Function.Injective (activeAtRank s) :=
  (s.active.orderEmbOfFin rfl).injective

theorem activeAtRank_range (s : State) : Set.range (activeAtRank s) = s.active :=
  Finset.range_orderEmbOfFin s.active rfl

/-- One prescribed infection or recovery, using the selected uniform rank.
Empty active populations are absorbing, exactly as in `prescribedStep`. -/
noncomputable def rankUpdate (birth : Bool) (s : State) (v : ℝ) : State :=
  if hs : s.active.Nonempty then
    prescribedUpdate birth s (activeAtRank s (uniformRank s.active.card hs.card_pos v))
  else s

theorem rankUpdate_of_nonempty (birth : Bool) (s : State) (hs : s.active.Nonempty)
    (v : ℝ) : rankUpdate birth s v =
      prescribedUpdate birth s (activeAtRank s (uniformRank s.active.card hs.card_pos v)) := by
  simp only [rankUpdate, dite_eq_left hs]

theorem infectious_rankUpdate (birth : Bool) (s : State) (hs : s.active.Nonempty)
    (v : ℝ) : infectious (rankUpdate birth s v) = prescribedActiveCount birth (infectious s) := by
  rw [rankUpdate_of_nonempty birth s hs v]
  exact infectious_prescribedUpdate birth (activeAtRank_mem s _)

theorem measurable_rankUpdate (birth : Bool) (s : State) : Measurable (rankUpdate birth s) := by
  classical
  change Measurable (fun v ↦ rankUpdate birth s v)
  by_cases hs : s.active.Nonempty
  · simp only [rankUpdate, dite_eq_left hs]
    exact (measurable_of_countable (fun r : Fin s.active.card ↦
      prescribedUpdate birth s (activeAtRank s r))).comp (measurable_uniformRank _ _)
  · simpa only [rankUpdate, dite_eq_right hs] using (measurable_const : Measurable (fun _ : ℝ ↦ s))

/-- The entire tree process on a single independent-uniform coordinate space. -/
noncomputable def rankState (events : ℕ → Bool) (s₀ : State) (u : ℕ → ℝ) : ℕ → State
  | 0 => s₀
  | k + 1 => rankUpdate (events k) (rankState events s₀ u k) (u k)

theorem rankState_congr_prefix (events : ℕ → Bool) (s₀ : State) {u v : ℕ → ℝ}
    (k : ℕ) (huv : ∀ j < k, u j = v j) :
    rankState events s₀ u k = rankState events s₀ v k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [rankState, rankState, ih (fun j hj ↦ huv j (by omega)), huv k (by omega)]

theorem infectious_rankState (events : ℕ → Bool) (s₀ : State) (u : ℕ → ℝ) (k : ℕ)
    (hpos : ∀ j < k, 0 < prescribedWalk events (infectious s₀) j) :
    infectious (rankState events s₀ u k) = prescribedWalk events (infectious s₀) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hc := ih (fun j hj ↦ hpos j (by omega))
      have hs : (rankState events s₀ u k).active.Nonempty := by
        apply Finset.card_pos.mp
        change 0 < infectious (rankState events s₀ u k)
        rw [hc]
        exact hpos k (by omega)
      rw [rankState, infectious_rankUpdate _ _ hs, hc]
      rfl

/-- The rank sequence depends on each fresh uniform and on the deterministic
prescribed count alone.  In particular it does not inspect past tree depths. -/
noncomputable def prescribedRanks (events : ℕ → Bool) (i₀ : ℕ) (u : ℕ → ℝ) (k : ℕ) : ℕ :=
  min (Nat.ceil ((prescribedWalk events i₀ k : ℝ) * u k) - 1)
    (prescribedWalk events i₀ k - 1)

theorem prescribedRanks_lt (events : ℕ → Bool) (i₀ : ℕ) (u : ℕ → ℝ) (k : ℕ)
    (hpos : 0 < prescribedWalk events i₀ k) :
    prescribedRanks events i₀ u k < prescribedWalk events i₀ k := by
  unfold prescribedRanks
  omega

theorem prescribedRanks_eq_rank (events : ℕ → Bool) (i₀ : ℕ) (u : ℕ → ℝ) (k : ℕ)
    (hpos : 0 < prescribedWalk events i₀ k) :
    prescribedRanks events i₀ u k = (uniformRank _ hpos (u k)).val := rfl

theorem rankState_parent_rank_eq (events : ℕ → Bool) (s₀ : State) (u : ℕ → ℝ) (k : ℕ)
    (hpos : ∀ j < k, 0 < prescribedWalk events (infectious s₀) j)
    (hs : (rankState events s₀ u k).active.Nonempty) :
    (uniformRank _ hs.card_pos (u k)).val = prescribedRanks events (infectious s₀) u k := by
  have hc := infectious_rankState events s₀ u k hpos
  change (rankState events s₀ u k).active.card = _ at hc
  simp only [uniformRank, prescribedRanks, hc]

theorem prescribedRanks_congr_tail (events : ℕ → Bool) (i₀ : ℕ) {u v : ℕ → ℝ}
    (N : ℕ) (huv : ∀ k ≥ N, u k = v k) (k : ℕ) (hk : N ≤ k) :
    prescribedRanks events i₀ u k = prescribedRanks events i₀ v k := by
  unfold prescribedRanks
  rw [huv k hk]

end HeightPaper.Model
