module

public import HeightPaper.Model.Profile

/-!
# Normalized profiles under a prescribed event

These are the finite one-step identities behind `lem:Mk is a martingale`.
The infection or recovery event is prescribed, and only the active vertex is
drawn uniformly. This differs from averaging the epidemic's event choice.
No process filtration or conditional-expectation theorem is asserted here.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.Model

/-- The active generating function divided by the number of active vertices.
For `w = exp z`, this is the paper's normalized Laplace transform. -/
noncomputable def normalizedActiveWeight (w : ℂ) (s : State) : ℂ :=
  activeWeight w s / (infectious s : ℂ)

@[simp] theorem normalizedActiveWeight_initial (w : ℂ) (n : ℕ) :
    normalizedActiveWeight w (initial n) = 1 := by
  simp [normalizedActiveWeight]

theorem normalizedActiveWeight_one (s : State) (h : s.active.Nonempty) :
    normalizedActiveWeight 1 s = 1 := by
  have hi : (infectious s : ℂ) ≠ 0 := by exact_mod_cast h.card_pos.ne'
  simp [normalizedActiveWeight, hi]

/-- A prescribed infection has the source's normalized multiplier, whose
denominator is the active count *after* the infection. -/
theorem uniformInfect_normalized_integral (w : ℂ) (s : State)
    (h : s.active.Nonempty) :
    (∫ v, normalizedActiveWeight w (infect s v) ∂(uniformActive s h).toMeasure) =
      normalizedActiveWeight w s * (1 + (w - 1) / ((infectious s : ℂ) + 1)) := by
  have hi : (infectious s : ℂ) ≠ 0 := by exact_mod_cast h.card_pos.ne'
  have hip : (infectious s : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (infectious s)
  simp only [normalizedActiveWeight, infectious_infect, Nat.cast_add, Nat.cast_one]
  rw [integral_div, uniformInfect_integral]
  field_simp
  ring

/-- A prescribed recovery preserves the expected normalized profile, provided
at least one active vertex remains. The hypothesis excludes extinction. -/
theorem uniformRecover_normalized_integral (w : ℂ) (s : State)
    (h : s.active.Nonempty) (hi : 1 < infectious s) :
    (∫ v, normalizedActiveWeight w (recover s v) ∂(uniformActive s h).toMeasure) =
      normalizedActiveWeight w s := by
  have hi0 : (infectious s : ℂ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hi).ne'
  have him : (infectious s : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hi.ne')
  rw [uniformActive_integral]
  have hsum : (∑ v ∈ s.active, normalizedActiveWeight w (recover s v)) =
      (∑ v ∈ s.active, activeWeight w (recover s v)) / ((infectious s : ℂ) - 1) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [normalizedActiveWeight, infectious_recover hv,
      Nat.cast_sub (Nat.one_le_of_lt hi), Nat.cast_one]
  rw [hsum, div_right_comm, ← uniformActive_integral s h, uniformRecover_integral w s h]
  unfold normalizedActiveWeight
  field_simp

/-- Dividing by the updated, nonzero product normalizer cancels the prescribed
infection multiplier. This is a one-step expectation identity, not a claim
about the conditional expectation of an entire process. -/
theorem uniformInfect_normalized_div_integral (w C : ℂ) (s : State)
    (h : s.active.Nonempty)
    (hfactor : 1 + (w - 1) / ((infectious s : ℂ) + 1) ≠ 0) :
    (∫ v, normalizedActiveWeight w (infect s v) /
        (C * (1 + (w - 1) / ((infectious s : ℂ) + 1)))
      ∂(uniformActive s h).toMeasure) = normalizedActiveWeight w s / C := by
  rw [integral_div, uniformInfect_normalized_integral]
  exact mul_div_mul_right _ _ hfactor

/-- Recovery leaves the product normalizer unchanged. -/
theorem uniformRecover_normalized_div_integral (w C : ℂ) (s : State)
    (h : s.active.Nonempty) (hi : 1 < infectious s) :
    (∫ v, normalizedActiveWeight w (recover s v) / C
      ∂(uniformActive s h).toMeasure) = normalizedActiveWeight w s / C := by
  rw [integral_div, uniformRecover_normalized_integral w s h hi]

/-- The update when the event is prescribed: `true` adds an active child and
`false` freezes the chosen vertex. This is the paper's attachment/freezing
construction, with no random infection/recovery choice. -/
def prescribedUpdate (birth : Bool) (s : State) (v : Fin s.vertices) : State :=
  if birth then infect s v else recover s v

/-- Active count after a prescribed event. -/
def prescribedActiveCount (birth : Bool) (i : ℕ) : ℕ :=
  if birth then i + 1 else i - 1

theorem infectious_prescribedUpdate (birth : Bool) {s : State} {v : Fin s.vertices}
    (hv : v ∈ s.active) :
    infectious (prescribedUpdate birth s v) = prescribedActiveCount birth (infectious s) := by
  cases birth <;> simp [prescribedUpdate, prescribedActiveCount, infectious_recover hv]

/-- Positivity of the active-count walk at every time in a finite event word,
including its initial and terminal times. -/
def PositiveActivePath : ℕ → List Bool → Prop
  | i, [] => 0 < i
  | i, birth :: events => 0 < i ∧ PositiveActivePath (prescribedActiveCount birth i) events

theorem PositiveActivePath.initial_pos {i : ℕ} {events : List Bool}
    (h : PositiveActivePath i events) : 0 < i := by
  cases events with
  | nil => exact h
  | cons birth events => exact h.1

/-- The normalized one-step factor; recovery has factor one. -/
noncomputable def prescribedProfileFactor (w : ℂ) (birth : Bool) (i : ℕ) : ℂ :=
  if birth then 1 + (w - 1) / ((i : ℂ) + 1) else 1

theorem uniformPrescribed_normalized_integral (w : ℂ) (birth : Bool) (s : State)
    (h : s.active.Nonempty) (hi : 0 < prescribedActiveCount birth (infectious s)) :
    (∫ v, normalizedActiveWeight w (prescribedUpdate birth s v)
      ∂(uniformActive s h).toMeasure) =
      normalizedActiveWeight w s * prescribedProfileFactor w birth (infectious s) := by
  cases birth with
  | false =>
      have hi' : 1 < infectious s := by
        simpa only [prescribedActiveCount, Bool.false_eq_true, ↓reduceIte,
          Nat.sub_pos_iff_lt] using hi
      simpa [prescribedUpdate, prescribedProfileFactor] using
        uniformRecover_normalized_integral w s h hi'
  | true =>
      exact uniformInfect_normalized_integral w s h

/-- A finite iterated expectation over uniform active-vertex draws for a
prescribed event word. The construction stops if there are no active vertices;
`PositiveActivePath` excludes this case in the product theorem below. Each
individual integral is over a finite space. -/
noncomputable def prescribedExpectation : List Bool → (State → ℂ) → State → ℂ
  | [], f, s => f s
  | birth :: events, f, s =>
      if h : s.active.Nonempty then
        ∫ v, prescribedExpectation events f (prescribedUpdate birth s v)
          ∂(uniformActive s h).toMeasure
      else f s

/-- The source's product normalizer along a finite deterministic active-count
walk, written recursively in chronological order. -/
noncomputable def prescribedProfileProduct (w : ℂ) : List Bool → ℕ → ℂ
  | [], _ => 1
  | birth :: events, i => prescribedProfileFactor w birth i *
      prescribedProfileProduct w events (prescribedActiveCount birth i)

/-- A constant denominator can be taken outside all the finite expectations. -/
theorem prescribedExpectation_div_const (events : List Bool) (f : State → ℂ)
    (C : ℂ) (s : State) :
    prescribedExpectation events (fun t => f t / C) s =
      prescribedExpectation events f s / C := by
  induction events generalizing s with
  | nil => rfl
  | cons birth events ih =>
      simp only [prescribedExpectation]
      split_ifs
      · simp_rw [ih]
        exact integral_div _ _
      · rfl

/-- Iterating the prescribed one-step expectations gives the exact product
formula. This statement concerns finite iterated draws; identifying the
epidemic conditioned on its whole event sequence and constructing its
canonical filtration are separate obligations. -/
theorem prescribedExpectation_normalizedActiveWeight (w : ℂ) (events : List Bool)
    (s : State) (hpath : PositiveActivePath (infectious s) events) :
    prescribedExpectation events (normalizedActiveWeight w) s =
      normalizedActiveWeight w s * prescribedProfileProduct w events (infectious s) := by
  induction events generalizing s with
  | nil => simp [prescribedExpectation, prescribedProfileProduct]
  | cons birth events ih =>
      have h : s.active.Nonempty := Finset.card_pos.mp hpath.1
      have hi : 0 < prescribedActiveCount birth (infectious s) := hpath.2.initial_pos
      rw [prescribedExpectation, dite_eq_left h, uniformActive_integral]
      have hsum :
          (∑ v ∈ s.active,
              prescribedExpectation events (normalizedActiveWeight w) (prescribedUpdate birth s v)) =
            (∑ v ∈ s.active, normalizedActiveWeight w (prescribedUpdate birth s v)) *
              prescribedProfileProduct w events (prescribedActiveCount birth (infectious s)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v hv
        have hcount := infectious_prescribedUpdate birth hv
        rw [ih (prescribedUpdate birth s v) (hcount ▸ hpath.2), hcount]
      rw [hsum, mul_div_right_comm, ← uniformActive_integral s h,
        uniformPrescribed_normalized_integral w birth s h hi]
      simp only [prescribedProfileProduct, mul_assoc]

/-- In particular, a process started from its single active root has expected
normalized profile equal to the source's product. -/
theorem prescribedExpectation_normalized_initial (w : ℂ) (events : List Bool) (n : ℕ)
    (hpath : PositiveActivePath 1 events) :
    prescribedExpectation events (normalizedActiveWeight w) (initial n) =
      prescribedProfileProduct w events 1 := by
  simpa using prescribedExpectation_normalizedActiveWeight w events (initial n)
    (by simpa using hpath)

/-- Division by a nonzero product preserves the initial normalized profile in
finite expectation. Nonvanishing is explicit for complex weights. -/
theorem prescribedExpectation_normalized_div_product (w : ℂ) (events : List Bool)
    (s : State) (hpath : PositiveActivePath (infectious s) events)
    (hC : prescribedProfileProduct w events (infectious s) ≠ 0) :
    prescribedExpectation events
        (fun t => normalizedActiveWeight w t /
          prescribedProfileProduct w events (infectious s)) s =
      normalizedActiveWeight w s := by
  rw [prescribedExpectation_div_const,
    prescribedExpectation_normalizedActiveWeight w events s hpath]
  exact mul_div_cancel_right₀ _ hC

/-- Positive real weights have nonzero one-step factors. Thus the real Laplace
transform does not need the complex-parameter zero-avoidance cutoff. -/
theorem prescribedProfileFactor_ne_zero_of_pos {x : ℝ} (hx : 0 < x)
    (birth : Bool) (i : ℕ) : prescribedProfileFactor (x : ℂ) birth i ≠ 0 := by
  cases birth with
  | false => simp [prescribedProfileFactor]
  | true =>
      have hip : (i : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
      have heq : prescribedProfileFactor (x : ℂ) true i =
          (((i : ℝ) + x) / ((i : ℝ) + 1) : ℝ) := by
        simp only [prescribedProfileFactor, ↓reduceIte, Complex.ofReal_div,
          Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
        field_simp
        ring
      rw [heq]
      exact_mod_cast (div_pos (by positivity : 0 < (i : ℝ) + x)
        (by positivity : 0 < (i : ℝ) + 1)).ne'

theorem prescribedProfileProduct_ne_zero_of_pos {x : ℝ} (hx : 0 < x)
    (events : List Bool) (i : ℕ) : prescribedProfileProduct (x : ℂ) events i ≠ 0 := by
  induction events generalizing i with
  | nil => simp [prescribedProfileProduct]
  | cons birth events ih =>
      exact mul_ne_zero (prescribedProfileFactor_ne_zero_of_pos hx birth i)
        (ih (prescribedActiveCount birth i))

end HeightPaper.Model
