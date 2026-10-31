module

public import HeightPaper.Model.CountCoupling
public import HeightPaper.Model.ReciprocalCoupling
public import HeightPaper.Model.RealNormalizer

/-!
# Prescribed tree counts and the coupled signed walks

The prescribed tree law uses natural active counts; the common-uniform
coupling uses unabsorbed integer walks. They agree up to every surviving
horizon, including the after-event index in each birth reciprocal.
-/

@[expose] public section

open scoped BigOperators

namespace HeightPaper.CountCoupling

open Model

theorem prescribedWalk_cast_eq_of_positive (events : ℕ → Bool) (S : ℕ → ℤ)
    (hzero : S 0 = 1)
    (hstep : ∀ k, S (k + 1) = S k + if events k then 1 else -1)
    {H : ℕ} (hs : ∀ j < H, 0 < S j) :
    (prescribedWalk events 1 H : ℤ) = S H := by
  induction H with
  | zero => simpa only [prescribedWalk, Nat.cast_one] using hzero.symm
  | succ H ih =>
      have hi := ih (fun j hj ↦ hs j (by omega))
      have hp := hs H (by omega)
      rw [prescribedWalk, prescribedActiveCount, hstep]
      cases events H <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · have hn : 1 ≤ prescribedWalk events 1 H := by omega
        rw [Nat.cast_sub hn, Nat.cast_one, hi]
        omega
      · simp only [Nat.cast_add, Nat.cast_one, hi]

theorem localWalk_succ (l : ℝ) (u : ℕ → ℝ) (k : ℕ) :
    localWalk l u (k + 1) = localWalk l u k +
      if localBirth l u k then 1 else -1 := by
  simp only [localWalk, Finset.sum_range_succ]
  omega

theorem prescribedWalk_local_cast {l : ℝ} {u : ℕ → ℝ} {H : ℕ}
    (hs : ∀ j ≤ H, 0 < localWalk l u j) {k : ℕ} (hk : k ≤ H) :
    (prescribedWalk (localBirth l u) 1 k : ℤ) = localWalk l u k := by
  apply prescribedWalk_cast_eq_of_positive _ _ (by simp [localWalk]) (localWalk_succ l u)
  exact fun j hj ↦ hs j (by omega)

theorem prescribedWalk_finite_cast {l : ℝ} {n : ℕ} {u : ℕ → ℝ} {H : ℕ}
    (hs : ∀ j ≤ H, 0 < finiteWalk l n u j) {k : ℕ} (hk : k ≤ H) :
    (prescribedWalk (finiteBirth l n u) 1 k : ℤ) = finiteWalk l n u k := by
  apply prescribedWalk_cast_eq_of_positive _ _ (finiteWalk_zero l n u) (finiteWalk_succ l n u)
  exact fun j hj ↦ hs j (by omega)

theorem prescribedWalk_local_real {l : ℝ} {u : ℕ → ℝ} {H : ℕ}
    (hs : ∀ j ≤ H, 0 < localWalk l u j) {k : ℕ} (hk : k ≤ H) :
    (prescribedWalk (localBirth l u) 1 k : ℝ) = (localWalk l u k : ℝ) := by
  exact_mod_cast prescribedWalk_local_cast hs hk

theorem prescribedWalk_finite_real {l : ℝ} {n : ℕ} {u : ℕ → ℝ} {H : ℕ}
    (hs : ∀ j ≤ H, 0 < finiteWalk l n u j) {k : ℕ} (hk : k ≤ H) :
    (prescribedWalk (finiteBirth l n u) 1 k : ℝ) = (finiteWalk l n u k : ℝ) := by
  exact_mod_cast prescribedWalk_finite_cast hs hk

theorem prescribedWalk_local_pos {l : ℝ} {u : ℕ → ℝ} {H : ℕ}
    (hs : ∀ j ≤ H, 0 < localWalk l u j) {k : ℕ} (hk : k ≤ H) :
    0 < prescribedWalk (localBirth l u) 1 k := by
  have h := prescribedWalk_local_cast hs hk
  have hp := hs k hk
  omega

theorem prescribedWalk_finite_pos {l : ℝ} {n : ℕ} {u : ℕ → ℝ} {H : ℕ}
    (hs : ∀ j ≤ H, 0 < finiteWalk l n u j) {k : ℕ} (hk : k ≤ H) :
    0 < prescribedWalk (finiteBirth l n u) 1 k := by
  have h := prescribedWalk_finite_cast hs hk
  have hp := hs k hk
  omega

theorem birthReciprocal_eq_after_count (events : ℕ → Bool) (i₀ k : ℕ) :
    birthReciprocal events i₀ k =
      (if events k then (1 : ℝ) else 0) / (prescribedWalk events i₀ (k + 1) : ℝ) := by
  cases he : events k <;>
    simp [birthReciprocal, prescribedWalk, prescribedActiveCount, he]

theorem birthReciprocal_local_eq {l : ℝ} {u : ℕ → ℝ} {H : ℕ}
    (hs : ∀ j ≤ H, 0 < localWalk l u j) {k : ℕ} (hk : k < H) :
    birthReciprocal (localBirth l u) 1 k =
      (if localBirth l u k then (1 : ℝ) else 0) / (localWalk l u (k + 1) : ℝ) := by
  rw [birthReciprocal_eq_after_count, prescribedWalk_local_real hs (by omega)]

theorem birthReciprocal_finite_eq {l : ℝ} {n : ℕ} {u : ℕ → ℝ} {H : ℕ}
    (hs : ∀ j ≤ H, 0 < finiteWalk l n u j) {k : ℕ} (hk : k < H) :
    birthReciprocal (finiteBirth l n u) 1 k =
      (if finiteBirth l n u k then (1 : ℝ) else 0) / (finiteWalk l n u (k + 1) : ℝ) := by
  rw [birthReciprocal_eq_after_count, prescribedWalk_finite_real hs (by omega)]

theorem sum_birthReciprocal_local_eq {l : ℝ} {u : ℕ → ℝ} {H : ℕ}
    (hs : ∀ j ≤ H, 0 < localWalk l u j) {k : ℕ} (hk : k ≤ H) :
    ∑ i ∈ Finset.range k, birthReciprocal (localBirth l u) 1 i =
      birthReciprocalSum (fun j ↦ (localWalk l u j : ℝ)) (localBirth l u) k := by
  apply Finset.sum_congr rfl
  intro i hi
  exact birthReciprocal_local_eq hs ((Finset.mem_range.mp hi).trans_le hk)

theorem sum_birthReciprocal_finite_eq {l : ℝ} {n : ℕ} {u : ℕ → ℝ} {H : ℕ}
    (hs : ∀ j ≤ H, 0 < finiteWalk l n u j) {k : ℕ} (hk : k ≤ H) :
    ∑ i ∈ Finset.range k, birthReciprocal (finiteBirth l n u) 1 i =
      birthReciprocalSum (fun j ↦ (finiteWalk l n u j : ℝ)) (finiteBirth l n u) k := by
  apply Finset.sum_congr rfl
  intro i hi
  exact birthReciprocal_finite_eq hs ((Finset.mem_range.mp hi).trans_le hk)

end HeightPaper.CountCoupling
