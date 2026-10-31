module

public import HeightPaper.Model.UniformParent
public import HeightPaper.Model.UnshiftedProfile

/-! # Deterministic bounds for every finite prefix of the rank process -/

@[expose] public section

open scoped BigOperators

namespace HeightPaper.Model

theorem vertices_rankUpdate_le (birth : Bool) (s : State) (v : ℝ) :
    (rankUpdate birth s v).vertices ≤ s.vertices + 1 := by
  unfold rankUpdate
  split_ifs
  · cases birth <;> simp [prescribedUpdate, infect, recover]
  · omega

theorem vertices_rankState_le (events : ℕ → Bool) (s₀ : State) (u : ℕ → ℝ) (k : ℕ) :
    (rankState events s₀ u k).vertices ≤ s₀.vertices + k := by
  induction k with
  | zero => simp [rankState]
  | succ k ih =>
      exact (vertices_rankUpdate_le (events k) (rankState events s₀ u k) (u k)).trans (by omega)

theorem norm_normalizedActiveWeight_le_pow {W : ℝ} (hW : 1 ≤ W)
    {w : ℂ} (hw : ‖w‖ ≤ W) (s : State) :
    ‖normalizedActiveWeight w s‖ ≤ W ^ s.vertices := by
  by_cases hi : infectious s = 0
  · simp only [normalizedActiveWeight, hi, Nat.cast_zero, div_zero, norm_zero]
    exact pow_nonneg (zero_le_one.trans hW) _
  have hpos : (0 : ℝ) < infectious s := by exact_mod_cast Nat.pos_of_ne_zero hi
  rw [normalizedActiveWeight, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hpos).mpr
  unfold activeWeight
  calc
    _ ≤ ∑ v ∈ s.active, ‖w ^ s.tree.depth v‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ s.active, W ^ s.vertices := by
      apply Finset.sum_le_sum
      intro v _
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) hw _).trans
        (pow_le_pow_right₀ hW (Tree.depth_lt_size s.tree v).le)
    _ = _ := by simp [infectious, mul_comm]

/-- Extinct paths are included: totalized normalized mass is zero there.
The bound is independent of the initial susceptible counter and all draws. -/
theorem norm_rank_unshifted_profile_le {W : ℝ} (hW : 1 ≤ W)
    {w : ℂ} (hw : ‖w‖ ≤ W) (hwr : 1 ≤ w.re)
    (events : ℕ → Bool) (n k : ℕ) (v : ℕ → ℝ) :
    ‖prescribedNormalizedProfile w events (initial n) 0 k
      (rankState events (initial n) v k)‖ ≤ W ^ (k + 1) := by
  rw [prescribedNormalizedProfile, norm_div, prescribedNormalizerFrom_zero]
  apply (div_le_self (norm_nonneg _)
    (one_le_norm_prescribedNormalizer hwr events (infectious (initial n)) k)).trans
  apply (norm_normalizedActiveWeight_le_pow hW hw _).trans
  apply pow_le_pow_right₀ hW
  have hh := vertices_rankState_le events (initial n) v k
  simpa only [initial, Nat.add_comm] using hh

/-- A retained cutoff only removes factors of modulus at least one at a
positive real weight; the same deterministic rank bound applies. -/
theorem norm_rank_shifted_profile_le {W : ℝ} (hW : 1 ≤ W)
    {w : ℂ} (hw : ‖w‖ ≤ W) (hwr : 1 ≤ w.re)
    (events : ℕ → Bool) (n J k : ℕ) (v : ℕ → ℝ) :
    ‖prescribedNormalizedProfile w events (initial n) J k
      (rankState events (initial n) v k)‖ ≤ W ^ (k + 1) := by
  rw [prescribedNormalizedProfile, norm_div]
  apply (div_le_self (norm_nonneg _)
    (one_le_norm_prescribedNormalizerFrom hwr events (infectious (initial n)) J k)).trans
  apply (norm_normalizedActiveWeight_le_pow hW hw _).trans
  apply pow_le_pow_right₀ hW
  have hh := vertices_rankState_le events (initial n) v k
  simpa only [initial, Nat.add_comm] using hh

end HeightPaper.Model
