module

public import HeightPaper.Probability.UniformWalk
public import HeightPaper.Model.EpidemicEventOrder

/-!
# The finite-population walk on the common uniform space

The susceptible budget starts at `n` and the per-pair rate is exactly `l / n`.
The integer walk is unabsorbed. At an exhausted susceptible budget every
subsequent increment is minus one, including on the null uniform endpoint.
The comparison statements are pathwise, without a probabilistic hypothesis.
-/

@[expose] public section

open scoped BigOperators NNReal

namespace HeightPaper.CountCoupling

/-- Infection threshold with `H` remaining susceptibles. -/
noncomputable def finiteThreshold (l : ℝ) (n H : ℕ) : ℝ :=
  birthThreshold (l * (H : ℝ) / n)

/-- A depleted budget cannot produce another infection. -/
noncomputable def budgetBirth (l : ℝ) (n H : ℕ) (v : ℝ) : Bool :=
  decide (0 < H ∧ v ≤ finiteThreshold l n H)

noncomputable def finiteSusceptible (l : ℝ) (n : ℕ) (u : ℕ → ℝ) : ℕ → ℕ
  | 0 => n
  | k + 1 => if budgetBirth l n (finiteSusceptible l n u k) (u k)
      then finiteSusceptible l n u k - 1 else finiteSusceptible l n u k

noncomputable def finiteBirth (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ) : Bool :=
  budgetBirth l n (finiteSusceptible l n u k) (u k)

/-- The source walk continues after its first visit to zero. -/
noncomputable def finiteWalk (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ) : ℤ :=
  1 + ∑ i ∈ Finset.range k, if finiteBirth l n u i then 1 else -1

/-- The deterministic lower comparison uses the remaining budget `n - k`.
Its exhausted-budget convention is minus one. -/
noncomputable def lowerBirth (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ) : Bool :=
  budgetBirth l n (n - k) (u k)

noncomputable def lowerWalk (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ) : ℤ :=
  1 + ∑ i ∈ Finset.range k, if lowerBirth l n u i then 1 else -1

@[simp] theorem finiteSusceptible_zero (l : ℝ) (n : ℕ) (u : ℕ → ℝ) :
    finiteSusceptible l n u 0 = n := rfl

@[simp] theorem finiteWalk_zero (l : ℝ) (n : ℕ) (u : ℕ → ℝ) :
    finiteWalk l n u 0 = 1 := by simp [finiteWalk]

theorem finiteSusceptible_succ (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ) :
    finiteSusceptible l n u (k + 1) =
      if finiteBirth l n u k then finiteSusceptible l n u k - 1
      else finiteSusceptible l n u k := rfl

theorem finiteWalk_succ (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ) :
    finiteWalk l n u (k + 1) = finiteWalk l n u k +
      if finiteBirth l n u k then 1 else -1 := by
  simp only [finiteWalk, Finset.sum_range_succ]
  omega

@[simp] theorem budgetBirth_zero (l : ℝ) (n : ℕ) (v : ℝ) :
    budgetBirth l n 0 v = false := by simp [budgetBirth]

theorem finiteSusceptible_bounds (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ) :
    n - k ≤ finiteSusceptible l n u k ∧ finiteSusceptible l n u k ≤ n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [finiteSusceptible_succ]
      split <;> omega

theorem finiteBirth_pos {l : ℝ} {n k : ℕ} {u : ℕ → ℝ}
    (hb : finiteBirth l n u k = true) : 0 < finiteSusceptible l n u k := by
  exact (of_decide_eq_true hb).1

/-- The susceptible budget is exactly the initial budget minus the infections
performed so far. -/
theorem finiteSusceptible_add_births (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ) :
    finiteSusceptible l n u k +
      ∑ i ∈ Finset.range k, (if finiteBirth l n u i then 1 else 0 : ℕ) = n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [finiteSusceptible_succ, Finset.sum_range_succ]
      cases hb : finiteBirth l n u k with
      | false => simpa [hb] using ih
      | true =>
          have hp := finiteBirth_pos hb
          simp only [↓reduceIte]
          omega

theorem finiteWalk_eq_budget (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ) :
    finiteWalk l n u k = 1 + 2 * ((n : ℤ) - finiteSusceptible l n u k) - k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [finiteWalk_succ, finiteSusceptible_succ, ih]
      cases hb : finiteBirth l n u k with
      | false => simp; omega
      | true =>
          have hp := finiteBirth_pos hb
          rw [ite_eq_left (by simp), ite_eq_left (by simp),
            Nat.cast_sub (by omega : 1 ≤ finiteSusceptible l n u k)]
          push_cast
          ring

theorem finiteThreshold_mono {l : ℝ} (hl : 0 ≤ l) (n : ℕ) {H J : ℕ}
    (h : H ≤ J) : finiteThreshold l n H ≤ finiteThreshold l n J := by
  apply birthThreshold_mono (by positivity)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast h) hl)
    (Nat.cast_nonneg n)

theorem finiteThreshold_le_local {l : ℝ} (hl : 0 ≤ l) {n H : ℕ}
    (hn : 0 < n) (hH : H ≤ n) : finiteThreshold l n H ≤ birthThreshold l := by
  apply birthThreshold_mono (by positivity)
  apply (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hH) hl

theorem finiteBirth_implies_local {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : 0 < n)
    (u : ℕ → ℝ) (k : ℕ) (hb : finiteBirth l n u k = true) :
    localBirth l u k = true := by
  have hb' : u k ≤ finiteThreshold l n (finiteSusceptible l n u k) := by
    exact (of_decide_eq_true hb).2
  apply decide_eq_true_eq.mpr
  exact hb'.trans (finiteThreshold_le_local hl hn (finiteSusceptible_bounds l n u k).2)

theorem lowerBirth_implies_finite {l : ℝ} (hl : 0 ≤ l) (n : ℕ)
    (u : ℕ → ℝ) (k : ℕ) (hb : lowerBirth l n u k = true) :
    finiteBirth l n u k = true := by
  have hb' : 0 < n - k ∧ u k ≤ finiteThreshold l n (n - k) := of_decide_eq_true hb
  apply decide_eq_true_eq.mpr
  exact ⟨hb'.1.trans_le (finiteSusceptible_bounds l n u k).1,
    hb'.2.trans (finiteThreshold_mono hl n (finiteSusceptible_bounds l n u k).1)⟩

/-- The pathwise sandwich in the source coupled construction, including times
beyond susceptible exhaustion. -/
theorem walk_sandwich {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : 0 < n)
    (u : ℕ → ℝ) (k : ℕ) :
    lowerWalk l n u k ≤ finiteWalk l n u k ∧ finiteWalk l n u k ≤ localWalk l u k := by
  constructor <;> simp only [lowerWalk, finiteWalk, localWalk] <;> gcongr with i hi
  · have h := lowerBirth_implies_finite hl n u i
    cases hb : lowerBirth l n u i <;> cases hf : finiteBirth l n u i <;>
      simp_all
  · have h := finiteBirth_implies_local hl hn u i
    cases hb : finiteBirth l n u i <;> cases hf : localBirth l u i <;>
      simp_all

/-- A disagreement can only occur inside the deterministic gap between the
lower and upper thresholds. -/
theorem birth_disagreement_subset {l : ℝ} (hl : 0 ≤ l) {n k : ℕ}
    (hk : k < n) (u : ℕ → ℝ) (hne : finiteBirth l n u k ≠ localBirth l u k) :
    finiteThreshold l n (n - k) < u k ∧ u k ≤ birthThreshold l := by
  have hn : 0 < n := by omega
  have hupper := finiteBirth_implies_local hl hn u k
  have hlower := lowerBirth_implies_finite hl n u k
  have hf : finiteBirth l n u k = false := by
    cases hf : finiteBirth l n u k <;> cases hh : localBirth l u k <;> simp_all
  have hloc : localBirth l u k = true := by
    cases hh : localBirth l u k <;> simp_all
  have hlow : lowerBirth l n u k = false := by
    cases hh : lowerBirth l n u k <;> simp_all
  constructor
  · have h := of_decide_eq_false hlow
    simp only [not_and] at h
    exact lt_of_not_ge (h (by omega))
  · exact of_decide_eq_true hloc

/-- Avoiding all deterministic threshold gaps forces exact equality of every
prefix, including prefixes on which either walk has already reached zero. -/
theorem prefix_eq_of_no_threshold_gap {l : ℝ} (hl : 0 ≤ l) {n K : ℕ}
    (hK : K ≤ n) (u : ℕ → ℝ)
    (hgap : ∀ i < K, ¬ (finiteThreshold l n (n - i) < u i ∧ u i ≤ birthThreshold l)) :
    ∀ k ≤ K, finiteWalk l n u k = localWalk l u k := by
  intro k hk
  unfold finiteWalk localWalk
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hiK : i < K := (Finset.mem_range.mp hi).trans_le hk
  have heq : finiteBirth l n u i = localBirth l u i := by
    by_contra hne
    exact hgap i hiK (birth_disagreement_subset hl (hiK.trans_le hK) u hne)
  rw [heq]

/-- The source infection threshold is exactly the existing epidemic threshold
at the per-pair rate `l / n`. -/
theorem finiteThreshold_eq_infectionProbability (l : ℝ≥0) (n H : ℕ) :
    finiteThreshold l n H = (HeightPaper.Model.infectionProbability (l / n) H : ℝ) := by
  simp only [finiteThreshold, birthThreshold, HeightPaper.Model.infectionProbability,
    NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, NNReal.coe_natCast]
  congr 1 <;> ring

/-- Away from the null uniform endpoint, the exhausted-budget guard agrees
with the source threshold convention. -/
theorem budgetBirth_eq_threshold_of_pos (l : ℝ) (n H : ℕ) {v : ℝ} (hv : 0 < v) :
    budgetBirth l n H v = decide (v ≤ finiteThreshold l n H) := by
  by_cases hH : 0 < H
  · simp [budgetBirth, hH]
  · have hz : H = 0 := by omega
    simp [hz, finiteThreshold, birthThreshold, not_le.mpr hv]

/-- The recursive threshold is the exact source formula with the accumulated
infection indicators, for positive uniform coordinates. -/
theorem finiteBirth_eq_source (l : ℝ) {n : ℕ} (hn : 0 < n) (u : ℕ → ℝ) (k : ℕ)
    (hu : 0 < u k) :
    finiteBirth l n u k = decide (u k ≤ birthThreshold
      (l * (1 - (∑ i ∈ Finset.range k, if finiteBirth l n u i then (1 : ℝ) else 0) / n))) := by
  rw [finiteBirth, budgetBirth_eq_threshold_of_pos l n _ hu]
  have hbudget := congrArg (fun m : ℕ ↦ (m : ℝ)) (finiteSusceptible_add_births l n u k)
  push_cast at hbudget
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : l * (finiteSusceptible l n u k : ℝ) / n =
      l * (1 - (∑ i ∈ Finset.range k, if finiteBirth l n u i then (1 : ℝ) else 0) / n) := by
    field_simp
    rw [← hbudget]
    ring
  simp only [finiteThreshold, hp]

/-- Increasing the parameter decreases the remaining susceptible budget.
The proof compares only equal budgets; instantaneous infection indicators need
not be monotone when the two budgets have already diverged. -/
theorem finiteSusceptible_antitone {l₀ l : ℝ} (h₀ : 0 ≤ l₀) (hl : l₀ ≤ l)
    (n : ℕ) (u : ℕ → ℝ) (k : ℕ) :
    finiteSusceptible l n u k ≤ finiteSusceptible l₀ n u k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      by_cases heq : finiteSusceptible l n u k = finiteSusceptible l₀ n u k
      · have hb : finiteBirth l₀ n u k = true → finiteBirth l n u k = true := by
          intro h
          have hh := of_decide_eq_true h
          apply decide_eq_true_eq.mpr
          rw [heq]
          refine ⟨hh.1, hh.2.trans ?_⟩
          apply birthThreshold_mono (by positivity)
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg _)) (Nat.cast_nonneg n)
        rw [finiteSusceptible_succ, finiteSusceptible_succ, heq]
        cases hlow : finiteBirth l₀ n u k <;> cases hhigh : finiteBirth l n u k <;>
          simp_all
      · have hlt : finiteSusceptible l n u k < finiteSusceptible l₀ n u k := lt_of_le_of_ne ih heq
        rw [finiteSusceptible_succ, finiteSusceptible_succ]
        split <;> split <;> omega

/-- Source parameter monotonicity for the jointly constructed finite walks. -/
theorem finiteWalk_mono_parameter {l₀ l : ℝ} (h₀ : 0 ≤ l₀) (hl : l₀ ≤ l)
    (n : ℕ) (u : ℕ → ℝ) (k : ℕ) : finiteWalk l₀ n u k ≤ finiteWalk l n u k := by
  rw [finiteWalk_eq_budget, finiteWalk_eq_budget]
  have h := finiteSusceptible_antitone h₀ hl n u k
  exact_mod_cast (show 1 + 2 * ((n : ℤ) - (finiteSusceptible l₀ n u k : ℤ)) - k ≤
      1 + 2 * ((n : ℤ) - (finiteSusceptible l n u k : ℤ)) - k by omega)

/-- On an early prefix, a fixed local walk at the minimum infection pressure
is a lower bound. This is the additional comparison used for reciprocal counts. -/
theorem early_localWalk_le {l : ℝ} (hl : 0 ≤ l) {n K : ℕ} (hK : K < n)
    (u : ℕ → ℝ) {k : ℕ} (hk : k ≤ K) :
    localWalk (l * ((n - K : ℕ) : ℝ) / n) u k ≤ finiteWalk l n u k := by
  unfold localWalk finiteWalk
  gcongr with i hi
  have hiK : i < K := (Finset.mem_range.mp hi).trans_le hk
  have hH : n - K ≤ finiteSusceptible l n u i :=
    (Nat.sub_le_sub_left hiK.le n).trans (finiteSusceptible_bounds l n u i).1
  have hpos : 0 < finiteSusceptible l n u i := lt_of_lt_of_le (by omega) hH
  have himp : localBirth (l * ((n - K : ℕ) : ℝ) / n) u i = true →
      finiteBirth l n u i = true := by
    intro hb
    apply decide_eq_true_eq.mpr
    exact ⟨hpos, (of_decide_eq_true hb).trans (finiteThreshold_mono hl n hH)⟩
  cases hb : localBirth (l * ((n - K : ℕ) : ℝ) / n) u i <;>
    cases hf : finiteBirth l n u i <;> simp_all

/-- The actual susceptible/infectious update: extinction is absorbing. -/
noncomputable def uniformCountUpdate (l : ℝ) (n : ℕ) (v : ℝ) (c : ℕ × ℕ) : ℕ × ℕ :=
  if c.2 = 0 then c else if budgetBirth l n c.1 v
    then (c.1 - 1, c.2 + 1) else (c.1, c.2 - 1)

/-- The absorbed count process driven by the same uniform coordinates. -/
noncomputable def absorbedCounts (l : ℝ) (n : ℕ) (u : ℕ → ℝ) : ℕ → ℕ × ℕ
  | 0 => (n, 1)
  | k + 1 => uniformCountUpdate l n (u k) (absorbedCounts l n u k)

/-- Exact correspondence up to and including the first visit to zero. -/
theorem absorbedCounts_eq_before_hit (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ)
    (hpos : ∀ j < k, 0 < finiteWalk l n u j) :
    (absorbedCounts l n u k).1 = finiteSusceptible l n u k ∧
      ((absorbedCounts l n u k).2 : ℤ) = finiteWalk l n u k := by
  induction k with
  | zero => simp [absorbedCounts]
  | succ k ih =>
      obtain ⟨hH, hI⟩ := ih (fun j hj ↦ hpos j (by omega))
      have hi : 0 < (absorbedCounts l n u k).2 := by
        have hh := hpos k (by omega)
        rw [← hI] at hh
        exact_mod_cast hh
      rw [absorbedCounts, uniformCountUpdate, ite_eq_right (by omega)]
      rw [hH]
      change (if finiteBirth l n u k then
          (finiteSusceptible l n u k - 1, (absorbedCounts l n u k).2 + 1)
        else (finiteSusceptible l n u k, (absorbedCounts l n u k).2 - 1)).1 = _ ∧
        ((if finiteBirth l n u k then
          (finiteSusceptible l n u k - 1, (absorbedCounts l n u k).2 + 1)
        else (finiteSusceptible l n u k, (absorbedCounts l n u k).2 - 1)).2 : ℤ) = _
      rw [finiteSusceptible_succ, finiteWalk_succ]
      cases hb : finiteBirth l n u k <;>
        simp [Nat.cast_sub (by omega : 1 ≤ (absorbedCounts l n u k).2), hI, sub_eq_add_neg]

/-- The absorbed construction remains fixed forever after its first zero. -/
theorem absorbedCounts_absorbed (l : ℝ) (n : ℕ) (u : ℕ → ℝ) {k : ℕ}
    (hk : (absorbedCounts l n u k).2 = 0) (j : ℕ) :
    absorbedCounts l n u (k + j) = absorbedCounts l n u k := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.add_succ, absorbedCounts, ih]
      simp [uniformCountUpdate, hk]

/-- At a first zero of the unabsorbed walk, the two susceptible counts agree,
and every later absorbed infectious count is zero. -/
theorem absorbedCounts_at_first_zero (l : ℝ) (n : ℕ) (u : ℕ → ℝ) {τ : ℕ}
    (hpos : ∀ j < τ, 0 < finiteWalk l n u j) (hzero : finiteWalk l n u τ = 0)
    (j : ℕ) : absorbedCounts l n u (τ + j) = (finiteSusceptible l n u τ, 0) := by
  obtain ⟨hH, hI⟩ := absorbedCounts_eq_before_hit l n u τ hpos
  have hz : (absorbedCounts l n u τ).2 = 0 := by exact_mod_cast hI.trans hzero
  rw [absorbedCounts_absorbed l n u hz j]
  exact Prod.ext hH hz

end HeightPaper.CountCoupling
