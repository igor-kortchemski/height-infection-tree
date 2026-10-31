module

public import HeightPaper.Model.ProfileMoments
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.InsertIdx

/-!
# Ordered active depths and resetting the finite past

The same sequence of parent ranks evolves two lists whose corresponding
depths differ by at most a fixed prefix bound. This is the deterministic
comparison needed to show that real profile zero sets ignore any finite
initial segment of the parent choices.
-/

@[expose] public section

open scoped BigOperators

namespace HeightPaper.Model

/-- The selected active parent stays active at a birth, and the new child is
appended in birth order. A recovery deletes the selected active rank. -/
def depthUpdate (birth : Bool) (rank : ℕ) (ds : List ℕ) : List ℕ :=
  if birth then ds ++ [(ds[rank]?).getD 0 + 1] else ds.eraseIdx rank

def depthRun (events : ℕ → Bool) (ranks : ℕ → ℕ) (ds : List ℕ) : ℕ → List ℕ
  | 0 => ds
  | k + 1 => depthUpdate (events k) (ranks k) (depthRun events ranks ds k)

/-- The first list has the original heights and the second the reset heights. -/
def DepthWithin (B : ℕ) (xs ys : List ℕ) : Prop :=
  List.Forall₂ (fun x y ↦ y ≤ x ∧ x ≤ y + B) xs ys

theorem DepthWithin.length_eq {B : ℕ} {xs ys : List ℕ} (h : DepthWithin B xs ys) :
    xs.length = ys.length := List.Forall₂.length_eq h

theorem DepthWithin.getD {B : ℕ} {xs ys : List ℕ} (h : DepthWithin B xs ys) (i : ℕ) :
    (ys[i]?).getD 0 ≤ (xs[i]?).getD 0 ∧
      (xs[i]?).getD 0 ≤ (ys[i]?).getD 0 + B := by
  induction h generalizing i with
  | nil => simp
  | @cons x y xs ys hxy hxs ih =>
      cases i with
      | zero => simpa using hxy
      | succ i => simpa using ih i

theorem DepthWithin.eraseIdx {B : ℕ} {xs ys : List ℕ}
    (h : DepthWithin B xs ys) (i : ℕ) : DepthWithin B (xs.eraseIdx i) (ys.eraseIdx i) := by
  induction h generalizing i with
  | nil => exact List.Forall₂.nil
  | @cons x y xs ys hxy hxs ih =>
      cases i with
      | zero => exact hxs
      | succ i => exact List.Forall₂.cons hxy (ih i)

theorem DepthWithin.depthUpdate {B : ℕ} {xs ys : List ℕ}
    (h : DepthWithin B xs ys) (birth : Bool) (rank : ℕ) :
    DepthWithin B (depthUpdate birth rank xs) (depthUpdate birth rank ys) := by
  cases birth with
  | false => exact h.eraseIdx rank
  | true =>
      apply List.rel_append h
      apply List.Forall₂.cons
      · have hh := h.getD rank
        constructor <;> omega
      · exact List.Forall₂.nil

theorem DepthWithin.depthRun {B : ℕ} {xs ys : List ℕ}
    (h : DepthWithin B xs ys) (events : ℕ → Bool) (ranks : ℕ → ℕ) (k : ℕ) :
    DepthWithin B (depthRun events ranks xs k) (depthRun events ranks ys k) := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih.depthUpdate (events k) (ranks k)

theorem depthWithin_zero_reset {B : ℕ} (xs : List ℕ) (hB : ∀ x ∈ xs, x ≤ B) :
    DepthWithin B xs (List.replicate xs.length 0) := by
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons x xs ih =>
      apply List.Forall₂.cons
      · exact ⟨Nat.zero_le _, by simpa using hB x (by simp)⟩
      · exact ih (fun y hy ↦ hB y (by simp [hy]))

/-- The ordered-depth dynamics can be restarted at any event time. -/
theorem depthRun_add (events : ℕ → Bool) (ranks : ℕ → ℕ) (ds : List ℕ) (N k : ℕ) :
    depthRun events ranks ds (N + k) =
      depthRun (fun i ↦ events (N + i)) (fun i ↦ ranks (N + i))
        (depthRun events ranks ds N) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change depthUpdate (events (N + k)) (ranks (N + k)) (depthRun events ranks ds (N + k)) = _
      rw [ih]
      rfl

def depthWeight (w : ℝ) (ds : List ℕ) : ℝ := (ds.map (fun d ↦ w ^ d)).sum

theorem depthWeight_nonneg {w : ℝ} (hw : 0 ≤ w) (ds : List ℕ) : 0 ≤ depthWeight w ds := by
  unfold depthWeight
  exact List.sum_nonneg (fun _ h ↦ by
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp h
    exact pow_nonneg hw d)

/-- Positive real generating functions are comparable by a finite prefix
factor, simultaneously for every later time and every common rank sequence. -/
theorem DepthWithin.depthWeight {B : ℕ} {xs ys : List ℕ}
    (h : DepthWithin B xs ys) {w : ℝ} (hw : 1 ≤ w) :
    depthWeight w ys ≤ depthWeight w xs ∧
      depthWeight w xs ≤ w ^ B * depthWeight w ys := by
  induction h with
  | nil => simp [Model.depthWeight]
  | @cons x y xs ys hxy hxs ih =>
      have hlo := pow_le_pow_right₀ hw hxy.1
      have hhi := pow_le_pow_right₀ hw hxy.2
      rw [pow_add] at hhi
      simp only [Model.depthWeight, List.map_cons, List.sum_cons] at ih ⊢
      constructor <;> nlinarith

theorem depthRun_zero_reset_weight_bounds (events : ℕ → Bool) (ranks : ℕ → ℕ)
    (xs : List ℕ) {B : ℕ} (hB : ∀ x ∈ xs, x ≤ B) {w : ℝ} (hw : 1 ≤ w) (k : ℕ) :
    depthWeight w (depthRun events ranks (List.replicate xs.length 0) k) ≤
        depthWeight w (depthRun events ranks xs k) ∧
      depthWeight w (depthRun events ranks xs k) ≤
        w ^ B * depthWeight w (depthRun events ranks (List.replicate xs.length 0) k) :=
  ((depthWithin_zero_reset xs hB).depthRun events ranks k).depthWeight hw

end HeightPaper.Model
