module

public import HeightPaper.Model.PrescribedPath

/-!
# Separating the epidemic event choice from uniform tree updates

The actual epidemic kernel is a mixture of the prescribed-event kernels. The
event probability depends only on the susceptible count, and the uniform active
vertex can be drawn after the event instead of before it.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace HeightPaper.Model

@[simp] theorem eventChoice_zero_eq_pure_false (rate : ℝ≥0) :
    eventChoice rate 0 = PMF.pure false := by
  ext b
  cases b <;> simp

/-- The two independent one-step choices can be taken in event-first order.
This remains valid at zero susceptible count and at extinction. -/
theorem step_eq_eventChoice_bind_prescribed (rate : ℝ≥0) (s : State) :
    step rate s = (eventChoice rate s.susceptible).bind (fun birth ↦ prescribedStep birth s) := by
  classical
  by_cases ha : s.active.Nonempty
  · by_cases hH : 0 < s.susceptible
    · rw [step, dite_eq_left ha]
      have hf (v : Fin s.vertices) :
          (fun birth ↦ if birth = true ∧ 0 < s.susceptible then infect s v else recover s v) =
            (fun birth ↦ prescribedUpdate birth s v) := by
        funext birth
        cases birth <;> simp [prescribedUpdate, hH]
      simp_rw [hf, prescribedStep, dite_eq_left ha, PMF.map, Function.comp_def]
      exact PMF.bind_comm _ _ _
    · have hzero : s.susceptible = 0 := by omega
      simp only [step, prescribedStep, dite_eq_left ha, hzero, eventChoice_zero_eq_pure_false,
        PMF.pure_map, PMF.pure_bind, Bool.false_eq_true, false_and, ite_false]
      rfl
  · simp [step, prescribedStep, ha]

/-- The prescribed-event kernel has a deterministic active count while the
current state is active. -/
theorem infectious_mem_support_prescribedStep (birth : Bool) (s : State)
    (ha : s.active.Nonempty) {t : State} (ht : t ∈ (prescribedStep birth s).support) :
    infectious t = prescribedActiveCount birth (infectious s) := by
  rw [prescribedStep, dite_eq_left ha] at ht
  obtain ⟨v, hv, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
  exact infectious_prescribedUpdate birth ((mem_support_uniformActive ha v).mp hv)

theorem prescribedStep_apply_eq_zero_of_count_ne (birth : Bool) (s : State)
    (ha : s.active.Nonempty) (t : State)
    (ht : infectious t ≠ prescribedActiveCount birth (infectious s)) :
    prescribedStep birth s t = 0 := by
  by_contra hn
  exact ht (infectious_mem_support_prescribedStep birth s ha ((PMF.mem_support_iff _ _).mpr hn))

/-- Restricting an epidemic step to the active-count increment of a prescribed
event selects exactly that mixture component. -/
theorem step_count_indicator (rate : ℝ≥0) (birth : Bool) (s : State)
    (ha : s.active.Nonempty) (t : State) :
    (if infectious t = prescribedActiveCount birth (infectious s) then step rate s t else 0) =
      eventChoice rate s.susceptible birth * prescribedStep birth s t := by
  classical
  have hi : 0 < infectious s := ha.card_pos
  have hdistinct : infectious s + 1 ≠ infectious s - 1 := by omega
  by_cases ht : infectious t = prescribedActiveCount birth (infectious s)
  · rw [ite_eq_left ht, step_eq_eventChoice_bind_prescribed, PMF.bind_apply,
      tsum_fintype, Fintype.sum_bool]
    cases birth with
    | false =>
        have hz := prescribedStep_apply_eq_zero_of_count_ne true s ha t (by
          simp only [prescribedActiveCount, Bool.false_eq_true, ↓reduceIte] at ht ⊢
          omega)
        rw [hz, mul_zero, zero_add]
    | true =>
        have hz := prescribedStep_apply_eq_zero_of_count_ne false s ha t (by
          simp only [prescribedActiveCount, Bool.false_eq_true, ↓reduceIte] at ht ⊢
          omega)
        rw [hz, mul_zero, add_zero]
  · rw [ite_eq_right ht, prescribedStep_apply_eq_zero_of_count_ne birth s ha t ht, mul_zero]

/-- Susceptibles evolve deterministically once the event is specified. -/
def prescribedSusceptibleWalk (events : ℕ → Bool) (H₀ : ℕ) : ℕ → ℕ
  | 0 => H₀
  | k + 1 => if events k then prescribedSusceptibleWalk events H₀ k - 1
      else prescribedSusceptibleWalk events H₀ k

theorem susceptible_prescribedUpdate (birth : Bool) (s : State) (v : Fin s.vertices) :
    (prescribedUpdate birth s v).susceptible =
      if birth then s.susceptible - 1 else s.susceptible := by
  cases birth <;> rfl

/-- The event probabilities are constant over every prescribed-history support,
because they depend only on this deterministic susceptible walk. -/
theorem susceptible_kernelPathLaw_prescribed (events : ℕ → Bool) (s₀ : State) (k : ℕ)
    (hpos : ∀ j < k, 0 < prescribedWalk events (infectious s₀) j)
    (q : FinitePath k)
    (hq : q ∈ (kernelPathLaw (fun j ↦ prescribedStep (events j)) s₀ k).support) :
    q.last.susceptible = prescribedSusceptibleWalk events s₀.susceptible k := by
  induction k with
  | zero =>
      rw [kernelPathLaw, PMF.mem_support_pure_iff] at hq
      subst q
      rfl
  | succ k ih =>
      obtain ⟨p, hp, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp hq
      obtain ⟨s, hs, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
      have hc := infectious_kernelPathLaw_prescribed events s₀ k
        (fun j hj ↦ hpos j (by omega)) p hp
      have hactive : p.last.active.Nonempty := by
        apply Finset.card_pos.mp
        change 0 < infectious p.last
        rw [hc]
        exact hpos k (by omega)
      change s ∈ (prescribedStep (events k) p.last).support at hs
      rw [prescribedStep, dite_eq_left hactive] at hs
      obtain ⟨v, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
      rw [FinitePath.append_last, susceptible_prescribedUpdate,
        ih (fun j hj ↦ hpos j (by omega)) p hp]
      rfl

end HeightPaper.Model
