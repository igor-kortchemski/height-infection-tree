module

public import HeightPaper.Model.EpidemicEventOrder

/-!
# The epidemic law conditioned on a finite event word

On a positive active-count word, the actual joint history mass factors into a
count-only event probability and the prescribed uniform attachment/freezing
history law. Normalizing the event cylinder therefore gives exactly the
prescribed history PMF.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace HeightPaper.Model

private theorem map_append_apply {N : ℕ} (q : FinitePath N) (ν : PMF State) (s : State) :
    (ν.map q.append) (q.append s) = ν s := by
  classical
  rw [PMF.map_apply]
  calc
    _ = if q.append s = q.append s then ν s else 0 := by
      apply tsum_eq_single s
      intro t ht
      have hne : q.append s ≠ q.append t := by
        intro he
        have he' := congrArg FinitePath.last he
        simp only [FinitePath.append_last] at he'
        exact ht he'.symm
      simp only [hne, ite_false]
    _ = _ := ite_eq_left rfl

private theorem map_append_apply_eq_zero {N : ℕ} (q p : FinitePath N) (ν : PMF State)
    (s : State) (hqp : q ≠ p) : (ν.map q.append) (p.append s) = 0 := by
  by_contra hn
  obtain ⟨t, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr hn)
  apply hqp
  have he' := congrArg FinitePath.prefixPath he
  simpa only [FinitePath.prefix_append] using he'

/-- A history point mass splits into its prefix mass and last transition mass. -/
theorem kernelPathLaw_apply_append (K : ℕ → State → PMF State) (s₀ : State)
    {N : ℕ} (q : FinitePath N) (s : State) :
    kernelPathLaw K s₀ (N + 1) (q.append s) =
      kernelPathLaw K s₀ N q * K N q.last s := by
  rw [kernelPathLaw, PMF.bind_apply]
  calc
    _ = kernelPathLaw K s₀ N q * ((K N q.last).map q.append) (q.append s) := by
      apply tsum_eq_single q
      intro p hp
      rw [map_append_apply_eq_zero p q _ s hp, mul_zero]
    _ = _ := by rw [map_append_apply]

/-- The cylinder records the complete active-count word through the horizon. -/
def eventCylinder (events : ℕ → Bool) (i₀ N : ℕ) : Set (FinitePath N) :=
  {q | ∀ k ≤ N, infectious (q.eval k) = prescribedWalk events i₀ k}

theorem mem_eventCylinder_append (events : ℕ → Bool) (i₀ : ℕ) {N : ℕ}
    (q : FinitePath N) (s : State) :
    q.append s ∈ eventCylinder events i₀ (N + 1) ↔
      q ∈ eventCylinder events i₀ N ∧ infectious s = prescribedWalk events i₀ (N + 1) := by
  constructor
  · intro h
    constructor
    · intro k hk
      simpa only [FinitePath.append_eval_of_le q s hk] using h k (by omega)
    · simpa only [FinitePath.eval_last, FinitePath.append_last] using h (N + 1) le_rfl
  · rintro ⟨hq, hs⟩ k hk
    by_cases hkN : k ≤ N
    · simpa only [FinitePath.append_eval_of_le q s hkN] using hq k hkN
    · have heq : k = N + 1 := by omega
      subst k
      simpa only [FinitePath.eval_last, FinitePath.append_last] using hs

/-- Every supported prescribed history lies in its active-count cylinder. -/
theorem mem_eventCylinder_of_prescribed_support (events : ℕ → Bool) (s₀ : State) (N : ℕ)
    (hpos : ∀ k < N, 0 < prescribedWalk events (infectious s₀) k)
    (q : FinitePath N)
    (hq : q ∈ (kernelPathLaw (fun k ↦ prescribedStep (events k)) s₀ N).support) :
    q ∈ eventCylinder events (infectious s₀) N := by
  intro k hk
  have hp : q.prefixAt k ∈ (kernelPathLaw (fun i ↦ prescribedStep (events i)) s₀ k).support := by
    rw [← kernelPathLaw_map_prefixAt _ s₀ N k hk]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩
  simpa only [FinitePath.prefixAt_last] using
    infectious_kernelPathLaw_prescribed events s₀ k (fun i hi ↦ hpos i (by omega)) (q.prefixAt k) hp

/-- The probability of the event word, before drawing any uniform vertices. -/
noncomputable def eventWordWeight (rate : ℝ≥0) (events : ℕ → Bool) (H₀ : ℕ) : ℕ → ℝ≥0∞
  | 0 => 1
  | k + 1 => eventWordWeight rate events H₀ k *
      eventChoice rate (prescribedSusceptibleWalk events H₀ k) (events k)

/-- Exact factorization of each restricted history mass. Positivity excludes
absorbing histories, where further artificial event choices would not be
recoverable from the active-count word. -/
theorem eventCylinder_mass_factorization (rate : ℝ≥0) (events : ℕ → Bool) (s₀ : State) (N : ℕ)
    (hpos : ∀ k ≤ N, 0 < prescribedWalk events (infectious s₀) k) (q : FinitePath N) :
    (eventCylinder events (infectious s₀) N).indicator
        (kernelPathLaw (fun _ ↦ step rate) s₀ N) q =
      eventWordWeight rate events s₀.susceptible N *
        kernelPathLaw (fun k ↦ prescribedStep (events k)) s₀ N q := by
  classical
  induction N with
  | zero =>
      change (eventCylinder events (infectious s₀) 0).indicator
        (kernelPathLaw (fun k ↦ prescribedStep (events k)) s₀ 0) q =
          1 * kernelPathLaw (fun k ↦ prescribedStep (events k)) s₀ 0 q
      rw [one_mul]
      by_cases hq : q ∈ eventCylinder events (infectious s₀) 0
      · exact Set.indicator_of_mem hq _
      · rw [Set.indicator_of_notMem hq]
        symm
        by_contra hn
        exact hq (mem_eventCylinder_of_prescribed_support events s₀ 0 (by omega) q
          ((PMF.mem_support_iff _ _).mpr hn))
  | succ N ih =>
      have hcalc (p : FinitePath N) (t : State) :
          (eventCylinder events (infectious s₀) (N + 1)).indicator
              (kernelPathLaw (fun _ ↦ step rate) s₀ (N + 1)) (p.append t) =
            eventWordWeight rate events s₀.susceptible (N + 1) *
              kernelPathLaw (fun k ↦ prescribedStep (events k)) s₀ (N + 1) (p.append t) := by
        have hi := ih (fun k hk ↦ hpos k (by omega)) p
        by_cases hp : kernelPathLaw (fun k ↦ prescribedStep (events k)) s₀ N p = 0
        · by_cases hc : p ∈ eventCylinder events (infectious s₀) N
          · simp only [Set.indicator_of_mem hc, hp, mul_zero] at hi
            simp only [Set.indicator, mem_eventCylinder_append, hc, true_and,
              kernelPathLaw_apply_append, hi, hp, zero_mul, mul_zero, ite_self]
          · simp only [Set.indicator, mem_eventCylinder_append, hc, false_and, ite_false,
              kernelPathLaw_apply_append, hp, zero_mul, mul_zero]
        · have hsupport : p ∈ (kernelPathLaw (fun k ↦ prescribedStep (events k)) s₀ N).support :=
            (PMF.mem_support_iff _ _).mpr hp
          have hc := mem_eventCylinder_of_prescribed_support events s₀ N
            (fun k hk ↦ hpos k (by omega)) p hsupport
          have hI := infectious_kernelPathLaw_prescribed events s₀ N
            (fun k hk ↦ hpos k (by omega)) p hsupport
          have hH := susceptible_kernelPathLaw_prescribed events s₀ N
            (fun k hk ↦ hpos k (by omega)) p hsupport
          have hactive : p.last.active.Nonempty := by
            apply Finset.card_pos.mp
            change 0 < infectious p.last
            rw [hI]
            exact hpos N (by omega)
          have hn : prescribedWalk events (infectious s₀) (N + 1) =
              prescribedActiveCount (events N) (infectious p.last) := by rw [hI]; rfl
          simp only [Set.indicator_of_mem hc] at hi
          simp only [Set.indicator, mem_eventCylinder_append, hc, true_and,
            kernelPathLaw_apply_append]
          rw [hn]
          have hsplit :
              (if infectious t = prescribedActiveCount (events N) (infectious p.last) then
                kernelPathLaw (fun _ ↦ step rate) s₀ N p * step rate p.last t else 0) =
              kernelPathLaw (fun _ ↦ step rate) s₀ N p *
                (if infectious t = prescribedActiveCount (events N) (infectious p.last) then
                  step rate p.last t else 0) := by split_ifs <;> simp
          rw [hsplit, step_count_indicator rate (events N) p.last hactive t, hi, hH, eventWordWeight]
          ac_rfl
      simpa only [FinitePath.append_prefix_last] using hcalc q.prefixPath q.last

/-- Summing the restricted masses gives the count-only event-word probability. -/
theorem eventCylinder_mass_sum (rate : ℝ≥0) (events : ℕ → Bool) (s₀ : State) (N : ℕ)
    (hpos : ∀ k ≤ N, 0 < prescribedWalk events (infectious s₀) k) :
    (∑' q, (eventCylinder events (infectious s₀) N).indicator
      (kernelPathLaw (fun _ ↦ step rate) s₀ N) q) =
      eventWordWeight rate events s₀.susceptible N := by
  simp_rw [eventCylinder_mass_factorization rate events s₀ N hpos]
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

theorem eventCylinder_probability (rate : ℝ≥0) (events : ℕ → Bool) (s₀ : State) (N : ℕ)
    (hpos : ∀ k ≤ N, 0 < prescribedWalk events (infectious s₀) k) :
    (kernelPathMeasure (fun _ ↦ step rate) s₀ N) (eventCylinder events (infectious s₀) N) =
      eventWordWeight rate events s₀.susceptible N := by
  rw [kernelPathMeasure, PMF.toMeasure_apply _ (by trivial)]
  exact eventCylinder_mass_sum rate events s₀ N hpos

/-- The actual epidemic history PMF conditioned on a positive event cylinder is
exactly the prescribed uniform attachment/freezing history PMF. Positive cylinder
probability is expressed by a supported witness, as required by `PMF.filter`. -/
theorem kernelPathLaw_filter_eventCylinder (rate : ℝ≥0) (events : ℕ → Bool) (s₀ : State) (N : ℕ)
    (hpos : ∀ k ≤ N, 0 < prescribedWalk events (infectious s₀) k)
    (h : ∃ q ∈ eventCylinder events (infectious s₀) N,
      q ∈ (kernelPathLaw (fun _ ↦ step rate) s₀ N).support) :
    (kernelPathLaw (fun _ ↦ step rate) s₀ N).filter
        (eventCylinder events (infectious s₀) N) h =
      kernelPathLaw (fun k ↦ prescribedStep (events k)) s₀ N := by
  have hsum := eventCylinder_mass_sum rate events s₀ N hpos
  have hw : eventWordWeight rate events s₀.susceptible N ≠ 0 := by
    obtain ⟨q, hq, hsupport⟩ := h
    have he := eventCylinder_mass_factorization rate events s₀ N hpos q
    rw [Set.indicator_of_mem hq] at he
    intro hz
    rw [hz, zero_mul] at he
    exact (PMF.mem_support_iff _ _).mp hsupport he
  have hwtop : eventWordWeight rate events s₀.susceptible N ≠ ∞ := by
    rw [← hsum]
    exact PMF.tsum_coe_indicator_ne_top _ _
  ext q
  rw [PMF.filter_apply, eventCylinder_mass_factorization rate events s₀ N hpos q, hsum]
  calc
    _ = kernelPathLaw (fun k ↦ prescribedStep (events k)) s₀ N q *
        (eventWordWeight rate events s₀.susceptible N *
          (eventWordWeight rate events s₀.susceptible N)⁻¹) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hw hwtop, mul_one]

/-- The earlier epidemic path construction is the constant-kernel instance. -/
theorem pathLaw_eq_kernelPathLaw (rate : ℝ≥0) (n N : ℕ) :
    pathLaw rate n N = kernelPathLaw (fun _ ↦ step rate) (initial n) N := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [pathLaw, kernelPathLaw, ih]

/-- Conditioning the actual epidemic from its single initial infectious root
on a positive finite event word gives exactly the prescribed tree process. -/
theorem pathLaw_filter_eventCylinder (rate : ℝ≥0) (n : ℕ) (events : ℕ → Bool) (N : ℕ)
    (hpos : ∀ k ≤ N, 0 < prescribedWalk events 1 k)
    (h : ∃ q ∈ eventCylinder events 1 N, q ∈ (pathLaw rate n N).support) :
    (pathLaw rate n N).filter (eventCylinder events 1 N) h =
      kernelPathLaw (fun k ↦ prescribedStep (events k)) (initial n) N := by
  have hh := kernelPathLaw_filter_eventCylinder rate events (initial n) N
    (by simpa using hpos) (by simpa only [← pathLaw_eq_kernelPathLaw, infectious_initial] using h)
  simpa only [← pathLaw_eq_kernelPathLaw, infectious_initial] using hh

end HeightPaper.Model
