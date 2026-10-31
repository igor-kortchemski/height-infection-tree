module

public import HeightPaper.Model.ActiveDepthList
public import HeightPaper.Model.UniformParent

/-! # Resetting depths in the actual independent-parent construction -/

@[expose] public section

namespace HeightPaper.Model

/-- On every positive prescribed prefix, the ordered-depth recursion is
exactly the profile of the actual rank-driven infection tree. -/
theorem activeDepths_rankState (events : ℕ → Bool) (s₀ : State) (u : ℕ → ℝ) (k : ℕ)
    (hpos : ∀ j < k, 0 < prescribedWalk events (infectious s₀) j) :
    activeDepths (rankState events s₀ u k) =
      depthRun events (prescribedRanks events (infectious s₀) u) (activeDepths s₀) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hp : ∀ j < k, 0 < prescribedWalk events (infectious s₀) j :=
        fun j hj ↦ hpos j (by omega)
      have hs : (rankState events s₀ u k).active.Nonempty := by
        apply Finset.card_pos.mp
        change 0 < infectious (rankState events s₀ u k)
        rw [infectious_rankState events s₀ u k hp]
        exact hpos k (by omega)
      rw [rankState, rankUpdate_of_nonempty _ _ hs, activeAtRank,
        activeDepths_prescribedUpdate_rank, rankState_parent_rank_eq events s₀ u k hp hs, ih hp]
      rfl

/-- All active depths at the cutoff are reset to zero. The initial list length
is deterministic once the event word is fixed. -/
noncomputable def rankResetDepths (events : ℕ → Bool) (i₀ N : ℕ) (u : ℕ → ℝ) (k : ℕ) : List ℕ :=
  depthRun (fun i ↦ events (N + i)) (fun i ↦ prescribedRanks events i₀ u (N + i))
    (List.replicate (prescribedWalk events i₀ N) 0) k

/-- The reset construction ignores every uniform before the cutoff. -/
theorem rankResetDepths_congr_tail (events : ℕ → Bool) (i₀ N : ℕ) {u v : ℕ → ℝ}
    (huv : ∀ j ≥ N, u j = v j) (k : ℕ) :
    rankResetDepths events i₀ N u k = rankResetDepths events i₀ N v k := by
  have hh : (fun i ↦ prescribedRanks events i₀ u (N + i)) =
      (fun i ↦ prescribedRanks events i₀ v (N + i)) := by
    funext i
    exact prescribedRanks_congr_tail events i₀ N huv (N + i) (by omega)
  simp only [rankResetDepths, hh]

/-- The actual and reset generating functions differ by at most a finite
positive factor, at every later time and every positive real tilt. -/
theorem rankResetDepths_weight_bounds (events : ℕ → Bool) (s₀ : State) (u : ℕ → ℝ)
    (N k : ℕ) (hpos : ∀ j < N + k, 0 < prescribedWalk events (infectious s₀) j)
    {w : ℝ} (hw : 1 ≤ w) :
    depthWeight w (rankResetDepths events (infectious s₀) N u k) ≤
        activeWeight w (rankState events s₀ u (N + k)) ∧
      activeWeight w (rankState events s₀ u (N + k)) ≤
        w ^ (rankState events s₀ u N).vertices *
          depthWeight w (rankResetDepths events (infectious s₀) N u k) := by
  have hpN : ∀ j < N, 0 < prescribedWalk events (infectious s₀) j :=
    fun j hj ↦ hpos j (by omega)
  have hlen : (activeDepths (rankState events s₀ u N)).length =
      prescribedWalk events (infectious s₀) N := by
    rw [activeDepths_length, infectious_rankState events s₀ u N hpN]
  have hactual : activeDepths (rankState events s₀ u (N + k)) =
      depthRun (fun i ↦ events (N + i))
        (fun i ↦ prescribedRanks events (infectious s₀) u (N + i))
        (activeDepths (rankState events s₀ u N)) k := by
    rw [activeDepths_rankState events s₀ u (N + k) hpos, depthRun_add,
      activeDepths_rankState events s₀ u N hpN]
  have hb := depthRun_zero_reset_weight_bounds
    (fun i ↦ events (N + i)) (fun i ↦ prescribedRanks events (infectious s₀) u (N + i))
    (activeDepths (rankState events s₀ u N)) (activeDepths_le_vertices _) hw k
  rw [hlen] at hb
  simpa only [rankResetDepths, ← hactual, activeDepths_depthWeight] using hb

end HeightPaper.Model
