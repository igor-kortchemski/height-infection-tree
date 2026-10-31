module

public import HeightPaper.Probability.KernelIteration
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push

/-!
# The two-colour urn used in the nonvanishing argument

The total number of balls is deterministic. At a step with increment `x ≥ -1`,
a uniformly chosen colour receives `x` balls; `x = -1` removes the chosen ball.
The kernel is defined on integer red counts, and its reachable support is proved
to stay between zero and the current total. The formulas below retain arbitrary
integer increments, rather than only infection/recovery increments.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace HeightPaper.Urn

/-- A red/blue draw with red probability `p`. -/
noncomputable def draw (p : ℝ≥0) (hp : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b ↦ cond b p (1 - p)) (by simp [hp])

@[simp] theorem draw_apply (p : ℝ≥0) (hp : p ≤ 1) (b : Bool) :
    draw p hp b = cond b (p : ℝ≥0∞) (1 - p) := by
  cases b <;> simp [draw]

/-- The fraction of red balls. This is used only at strictly positive totals. -/
noncomputable def proportion (s r : ℤ) : ℝ := (r : ℝ) / s

noncomputable def redProbability (s r : ℤ) (hs : 0 < s) (hr : 0 ≤ r) : ℝ≥0 :=
  ⟨proportion s r, div_nonneg (Int.cast_nonneg hr) (Int.cast_nonneg hs.le)⟩

theorem redProbability_le_one (s r : ℤ) (hs : 0 < s) (hr : 0 ≤ r) (hrs : r ≤ s) :
    redProbability s r hs hr ≤ 1 := by
  change (r : ℝ) / s ≤ 1
  exact (div_le_one (Int.cast_pos.mpr hs)).mpr (Int.cast_le.mpr hrs)

/-- The actual red-count transition. The fallback on invalid states is never
visited from a valid initial urn under an admissible increment sequence. -/
noncomputable def step (s x : ℤ) (hs : 0 < s) (r : ℤ) : PMF ℤ :=
  if h : 0 ≤ r ∧ r ≤ s then
    (draw (redProbability s r hs h.1) (redProbability_le_one s r hs h.1 h.2)).map
      (fun b ↦ if b then r + x else r)
  else PMF.pure r

theorem finite_support_step (s x : ℤ) (hs : 0 < s) (r : ℤ) :
    (step s x hs r).support.Finite := by
  unfold step
  split
  · exact FinitePMF.finite_support_map _ (Set.toFinite _) _
  · rw [PMF.support_pure]; exact Set.finite_singleton _

theorem integral_draw (p : ℝ≥0) (hp : p ≤ 1) (f : Bool → ℝ) :
    (∫ b, f b ∂(draw p hp).toMeasure) = p * f true + (1 - (p : ℝ)) * f false := by
  simp [PMF.integral_eq_sum, draw_apply, ENNReal.toReal_sub_of_le
    (show (p : ℝ≥0∞) ≤ 1 by exact_mod_cast hp) (by simp)]

/-- The two-branch expectation formula for the genuine urn transition. -/
theorem integral_step (s x r : ℤ) (hs : 0 < s) (hr : 0 ≤ r) (hrs : r ≤ s)
    (f : ℤ → ℝ) :
    (∫ q, f q ∂(step s x hs r).toMeasure) =
      proportion s r * f (r + x) + (1 - proportion s r) * f r := by
  rw [step, dite_eq_left ⟨hr, hrs⟩, ← PMF.toMeasure_map _ _ (measurable_of_countable _),
    integral_map_of_stronglyMeasurable (measurable_of_countable _)
      (measurable_of_countable f).stronglyMeasurable, integral_draw]
  rfl

/-- A draw cannot create an invalid red count, including removal at a monochromatic urn. -/
theorem step_support_valid (s x r : ℤ) (hs : 0 < s) (hx : -1 ≤ x)
    (_hnext : 0 < s + x) (hr : 0 ≤ r) (hrs : r ≤ s) :
    ∀ q ∈ (step s x hs r).support, 0 ≤ q ∧ q ≤ s + x := by
  intro q hq
  rw [step, dite_eq_left ⟨hr, hrs⟩, PMF.mem_support_map_iff] at hq
  obtain ⟨b, hb, rfl⟩ := hq
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hlt : r < s := by
      by_contra hn
      have heq : r = s := by omega
      subst r
      have hp : redProbability s s hs hs.le = 1 := by
        apply Subtype.ext
        simp [redProbability, proportion, ne_of_gt (Int.cast_pos.mpr hs : (0 : ℝ) < s)]
      simp [PMF.mem_support_iff, hp] at hb
    omega
  · simp only [↓reduceIte]
    have hpos : 0 < r := by
      by_contra hn
      have heq : r = 0 := by omega
      subst r
      have hp : redProbability s 0 hs (le_refl 0) = 0 := by
        apply Subtype.ext
        simp [redProbability, proportion]
      simp [PMF.mem_support_iff, hp] at hb
    omega

/-- The one-step martingale identity in the proof of the urn convergence lemma. -/
theorem integral_proportion_step (s x r : ℤ) (hs : 0 < s) (hnext : 0 < s + x)
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    (∫ q, proportion (s + x) q ∂(step s x hs r).toMeasure) = proportion s r := by
  rw [integral_step s x r hs hr hrs]
  unfold proportion
  push_cast
  have hs0 : (s : ℝ) ≠ 0 := ne_of_gt (Int.cast_pos.mpr hs)
  have hn0 : (s : ℝ) + x ≠ 0 := by exact_mod_cast ne_of_gt hnext
  field_simp
  ring

/-- The exact second-moment recurrence in the proof of `prop urnes`. -/
theorem integral_proportion_sq_step (s x r : ℤ) (hs : 0 < s)
    (hnext : 0 < s + x) (hr : 0 ≤ r) (hrs : r ≤ s) :
    (∫ q, (proportion (s + x) q) ^ 2 ∂(step s x hs r).toMeasure) =
      (1 - (x : ℝ) ^ 2 / ((s + x : ℤ) : ℝ) ^ 2) * (proportion s r) ^ 2 +
        ((x : ℝ) ^ 2 / ((s + x : ℤ) : ℝ) ^ 2) * proportion s r := by
  rw [integral_step s x r hs hr hrs]
  unfold proportion
  push_cast
  have hs0 : (s : ℝ) ≠ 0 := ne_of_gt (Int.cast_pos.mpr hs)
  have hn0 : (s : ℝ) + x ≠ 0 := by exact_mod_cast ne_of_gt hnext
  field_simp
  ring


/-- A deterministic increment schedule with a positive total at every time.
`increment k` is the paper's increment numbered `k + 1`. -/
structure Schedule where
  total : ℕ → ℤ
  increment : ℕ → ℤ
  positive : ∀ k, 0 < total k
  next : ∀ k, total (k + 1) = total k + increment k
  increment_ge : ∀ k, -1 ≤ increment k

/-- Marginal red-count law of the actual urn. -/
noncomputable def law (D : Schedule) (r₀ : ℤ) (k : ℕ) : PMF ℤ :=
  FinitePMF.kernelEvolve (PMF.pure r₀)
    (fun j ↦ step (D.total j) (D.increment j) (D.positive j)) k

@[simp] theorem law_zero (D : Schedule) (r₀ : ℤ) : law D r₀ 0 = PMF.pure r₀ := rfl

theorem law_succ (D : Schedule) (r₀ : ℤ) (k : ℕ) :
    law D r₀ (k + 1) = (law D r₀ k).bind
      (step (D.total k) (D.increment k) (D.positive k)) := rfl

theorem finite_support_law (D : Schedule) (r₀ : ℤ) (k : ℕ) :
    (law D r₀ k).support.Finite :=
  FinitePMF.kernelEvolve_support_finite _ _
    (by rw [PMF.support_pure]; exact Set.finite_singleton _)
    (fun j r ↦ finite_support_step _ _ _ r) k

/-- Reachable red and blue counts stay nonnegative. -/
theorem law_support_valid (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) (k : ℕ) :
    ∀ r ∈ (law D r₀ k).support, 0 ≤ r ∧ r ≤ D.total k := by
  induction k with
  | zero =>
      intro r hr
      rw [law_zero, PMF.mem_support_pure_iff] at hr
      subst r
      exact ⟨hr₀, hr₀s⟩
  | succ k ih =>
      intro r hr
      rw [law_succ, PMF.mem_support_bind_iff] at hr
      obtain ⟨q, hq, hr⟩ := hr
      obtain ⟨hq0, hqs⟩ := ih q hq
      rw [D.next]
      exact step_support_valid _ _ _ (D.positive k) (D.increment_ge k)
        (by rw [← D.next]; exact D.positive _) hq0 hqs r hr

theorem integral_law_succ (D : Schedule) (r₀ : ℤ) (k : ℕ) (f : ℤ → ℝ) :
    (∫ r, f r ∂(law D r₀ (k + 1)).toMeasure) =
      ∫ r, (∫ q, f q ∂(step (D.total k) (D.increment k) (D.positive k) r).toMeasure)
        ∂(law D r₀ k).toMeasure :=
  FinitePMF.kernelEvolve_integral_succ _ _
    (by rw [PMF.support_pure]; exact Set.finite_singleton _)
    (fun j r ↦ finite_support_step _ _ _ r) (fun _ ↦ measurable_of_countable _) k f

/-- Every finite-time red fraction has the initial expectation. -/
theorem integral_proportion_law (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) (k : ℕ) :
    (∫ r, proportion (D.total k) r ∂(law D r₀ k).toMeasure) =
      proportion (D.total 0) r₀ := by
  induction k with
  | zero => simp [PMF.toMeasure_pure]
  | succ k ih =>
      rw [integral_law_succ]
      refine Eq.trans (integral_congr_ae ?_) ih
      apply FinitePMF.ae_of_forall_mem_support
      intro r hr
      obtain ⟨hr0, hrs⟩ := law_support_valid D r₀ hr₀ hr₀s k r hr
      rw [D.next]
      exact integral_proportion_step _ _ _ (D.positive k)
        (by rw [← D.next]; exact D.positive _) hr0 hrs

/-- The deterministic factor governing loss of variance from the two-colour state. -/
noncomputable def retention (D : Schedule) (k : ℕ) : ℝ :=
  1 - (D.increment k : ℝ) ^ 2 / (D.total (k + 1) : ℝ) ^ 2

/-- The second moment satisfies precisely the scalar recurrence in the paper. -/
theorem integral_proportion_sq_law_succ (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) (k : ℕ) :
    (∫ r, (proportion (D.total (k + 1)) r) ^ 2 ∂(law D r₀ (k + 1)).toMeasure) =
      retention D k * (∫ r, (proportion (D.total k) r) ^ 2 ∂(law D r₀ k).toMeasure) +
        (1 - retention D k) * proportion (D.total 0) r₀ := by
  rw [integral_law_succ]
  have hi (f : ℤ → ℝ) := FinitePMF.integrable_of_finite_support _
    (finite_support_law D r₀ k) f
  calc
    _ = ∫ r, (retention D k * (proportion (D.total k) r) ^ 2 +
        (1 - retention D k) * proportion (D.total k) r) ∂(law D r₀ k).toMeasure := by
      apply integral_congr_ae
      apply FinitePMF.ae_of_forall_mem_support
      intro r hr
      obtain ⟨hr0, hrs⟩ := law_support_valid D r₀ hr₀ hr₀s k r hr
      simpa [retention, D.next] using
        integral_proportion_sq_step (D.total k) (D.increment k) r (D.positive k)
          (by rw [← D.next]; exact D.positive _) hr0 hrs
    _ = _ := by
      rw [integral_add (hi _) (hi _), integral_const_mul, integral_const_mul,
        integral_proportion_law D r₀ hr₀ hr₀s k]

/-- The exact finite-product second moment, before passing to the martingale limit.
No convergence or nonvanishing conclusion is assumed in this formula. -/
theorem integral_proportion_sq_law (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) (k : ℕ) :
    (∫ r, (proportion (D.total k) r) ^ 2 ∂(law D r₀ k).toMeasure) =
      proportion (D.total 0) r₀ +
        ((proportion (D.total 0) r₀) ^ 2 - proportion (D.total 0) r₀) *
          ∏ j ∈ Finset.range k, retention D j := by
  induction k with
  | zero => simp [PMF.toMeasure_pure]
  | succ k ih =>
      rw [integral_proportion_sq_law_succ D r₀ hr₀ hr₀s, ih, Finset.prod_range_succ]
      ring

/-- Expected mixed-colour mass is the initial mixed mass times the same product. -/
theorem integral_mixed_law (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) (k : ℕ) :
    (∫ r, proportion (D.total k) r * (1 - proportion (D.total k) r)
      ∂(law D r₀ k).toMeasure) =
      proportion (D.total 0) r₀ * (1 - proportion (D.total 0) r₀) *
        ∏ j ∈ Finset.range k, retention D j := by
  have hi (f : ℤ → ℝ) := FinitePMF.integrable_of_finite_support _
    (finite_support_law D r₀ k) f
  simp_rw [show ∀ a : ℝ, a * (1 - a) = a - a ^ 2 by intro a; ring]
  rw [integral_sub (hi _) (hi _), integral_proportion_law D r₀ hr₀ hr₀s,
    integral_proportion_sq_law D r₀ hr₀ hr₀s]
  ring

end HeightPaper.Urn
