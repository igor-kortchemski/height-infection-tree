module

public import HeightPaper.Model.ObservedEvents

/-!
# Averaging uniform positive-event-word estimates

Finite active histories are partitioned by their observed birth/recovery
words. The exact epidemic mass factorization transfers a uniform prescribed
word bound to the actual path law, including arbitrary good-word conditions
and bad events depending on the word.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped NNReal ENNReal BigOperators

namespace HeightPaper.Model

/-- Extend a finite event word by recoveries outside its recorded horizon. -/
def extendEventWord {N : ℕ} (w : Fin N → Bool) (k : ℕ) : Bool :=
  if h : k < N then w ⟨k, h⟩ else false

/-- The finite event word read from the active-count increments. -/
def observedEventWord {N : ℕ} (p : FinitePath N) : Fin N → Bool :=
  fun k ↦ observedBirth p.eval k

/-- A finite history has constant state, hence no observed births, after its
horizon. Thus extending its finite word loses no observed information. -/
theorem extend_observedEventWord {N : ℕ} (p : FinitePath N) :
    extendEventWord (observedEventWord p) = observedBirth p.eval := by
  funext k
  by_cases hk : k < N
  · simp [extendEventWord, hk, observedEventWord]
  · have hkN : N ≤ k := Nat.le_of_not_gt hk
    have hkN' : N ≤ k + 1 := by omega
    simp [extendEventWord, hk, observedBirth, FinitePath.eval,
      Nat.min_eq_right hkN, Nat.min_eq_right hkN']

/-- On a positive count cylinder, the active-count increment recovers each
prescribed event before the horizon. -/
theorem observedBirth_eq_of_eventCylinder {events : ℕ → Bool} {N : ℕ}
    {p : FinitePath N} (hp : p ∈ eventCylinder events 1 N)
    (_hpos : ∀ k ≤ N, 0 < prescribedWalk events 1 k) {k : ℕ} (hk : k < N) :
    observedBirth p.eval k = events k := by
  have hI := hp k hk.le
  have hI' := hp (k + 1) (by omega)
  unfold observedBirth
  rw [hI, hI', prescribedWalk]
  cases he : events k with
  | false =>
      simp only [prescribedActiveCount, Bool.false_eq_true, ↓reduceIte]
      simp only [decide_eq_false_iff_not]
      omega
  | true => simp [prescribedActiveCount]

/-- Distinct finite positive count cylinders belong to distinct observed-word
fibers. This is the disjointness used in the averaging argument. -/
theorem eventCylinder_subset_observedEventWord {N : ℕ} (w : Fin N → Bool)
    (hpos : ∀ k ≤ N, 0 < prescribedWalk (extendEventWord w) 1 k) :
    eventCylinder (extendEventWord w) 1 N ⊆ {p | observedEventWord p = w} := by
  intro p hp
  funext k
  change observedBirth p.eval k = w k
  rw [observedBirth_eq_of_eventCylinder hp hpos k.isLt]
  simp [extendEventWord, k.isLt]

/-- An event restricted to a positive cylinder has exactly the prescribed
word probability multiplied by the epidemic cylinder probability. -/
theorem kernelPathMeasure_eventCylinder_inter (rate : ℝ≥0) (events : ℕ → Bool)
    (s₀ : State) (N : ℕ) (hpos : ∀ k ≤ N, 0 < prescribedWalk events (infectious s₀) k)
    (B : Set (FinitePath N)) :
    (kernelPathMeasure (fun _ ↦ step rate) s₀ N).real
        (eventCylinder events (infectious s₀) N ∩ B) =
      (kernelPathMeasure (fun _ ↦ step rate) s₀ N).real
        (eventCylinder events (infectious s₀) N) *
      (kernelPathMeasure (fun k ↦ prescribedStep (events k)) s₀ N).real B := by
  classical
  have he : (kernelPathMeasure (fun _ ↦ step rate) s₀ N)
        (eventCylinder events (infectious s₀) N ∩ B) =
      eventWordWeight rate events s₀.susceptible N *
        (kernelPathMeasure (fun k ↦ prescribedStep (events k)) s₀ N) B := by
    simp only [kernelPathMeasure, PMF.toMeasure_apply _ (show MeasurableSet
      (eventCylinder events (infectious s₀) N ∩ B) from trivial),
      PMF.toMeasure_apply _ (show MeasurableSet B from trivial)]
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro q
    by_cases hq : q ∈ B
    · rw [Set.indicator_of_mem hq]
      have hfact := eventCylinder_mass_factorization rate events s₀ N hpos q
      simpa only [Set.indicator, Set.mem_inter_iff, hq, and_true] using hfact
    · simp only [Set.indicator, Set.mem_inter_iff, hq, and_false, ↓reduceIte, mul_zero]
  simp only [measureReal_def, he, eventCylinder_probability rate events s₀ N hpos,
    ENNReal.toReal_mul]

/-- Initial-root specialization of exact cylinder averaging. -/
theorem pathMeasure_eventCylinder_inter (rate : ℝ≥0) (n : ℕ) (events : ℕ → Bool)
    (N : ℕ) (hpos : ∀ k ≤ N, 0 < prescribedWalk events 1 k) (B : Set (FinitePath N)) :
    (pathMeasure rate n N).real (eventCylinder events 1 N ∩ B) =
      (pathMeasure rate n N).real (eventCylinder events 1 N) *
        (kernelPathMeasure (fun k ↦ prescribedStep (events k)) (initial n) N).real B := by
  have he : pathMeasure rate n N = kernelPathMeasure (fun _ ↦ step rate) (initial n) N := by
    unfold pathMeasure kernelPathMeasure
    rw [pathLaw_eq_kernelPathLaw]
  rw [he]
  simpa only [infectious_initial] using kernelPathMeasure_eventCylinder_inter rate events
    (initial n) N (by simpa only [infectious_initial] using hpos) B

/-- A uniform bound for each positive good event word transfers to the actual
active epidemic law. The bad event may depend on the same word, and may inspect
any coordinates of the finite path. -/
theorem pathMeasure_positive_eventWord_bound (rate : ℝ≥0) (n N : ℕ)
    (G : (ℕ → Bool) → Prop) (bad : (ℕ → Bool) → Set (FinitePath N))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ events : ℕ → Bool,
      (∀ k ≤ N, 0 < prescribedWalk events 1 k) → G events →
      (kernelPathMeasure (fun k ↦ prescribedStep (events k)) (initial n) N).real (bad events) ≤ ε) :
    (pathMeasure rate n N).real
      {p | p.last.active.Nonempty ∧ G (observedBirth p.eval) ∧ p ∈ bad (observedBirth p.eval)} ≤ ε := by
  classical
  let fiber : (Fin N → Bool) → Set (FinitePath N) := fun w ↦ {p | observedEventWord p = w}
  let E : (Fin N → Bool) → Set (FinitePath N) := fun w ↦
    {p | p.last.active.Nonempty ∧ G (observedBirth p.eval) ∧
      p ∈ bad (observedBirth p.eval) ∧ observedEventWord p = w}
  have hobs {p : FinitePath N} {w : Fin N → Bool} (hw : observedEventWord p = w) :
      observedBirth p.eval = extendEventWord w := by
    rw [← extend_observedEventWord p, hw]
  have hEbound (w : Fin N → Bool) :
      (pathMeasure rate n N).real (E w) ≤ ε * (pathMeasure rate n N).real (fiber w) := by
    by_cases hgood : (∀ k ≤ N, 0 < prescribedWalk (extendEventWord w) 1 k) ∧ G (extendEventWord w)
    · have hmono : (pathMeasure rate n N).real (E w) ≤
          (pathMeasure rate n N).real (eventCylinder (extendEventWord w) 1 N ∩ bad (extendEventWord w)) := by
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        apply PMF.toMeasure_mono _ (show MeasurableSet (E w) from trivial)
        intro p hp
        have heq := hobs hp.1.2.2.2
        have hpath := (mem_support_pathLaw_iff p).mp hp.2
        refine ⟨?_, ?_⟩
        · simpa only [heq] using supportedPath_mem_observed_eventCylinder p hpath hp.1.1
        · simpa only [heq] using hp.1.2.2.1
      rw [pathMeasure_eventCylinder_inter rate n _ N hgood.1] at hmono
      have hc : (pathMeasure rate n N).real (eventCylinder (extendEventWord w) 1 N) ≤
          (pathMeasure rate n N).real (fiber w) :=
        measureReal_mono (eventCylinder_subset_observedEventWord w hgood.1)
      calc
        _ ≤ _ := hmono
        _ ≤ (pathMeasure rate n N).real (eventCylinder (extendEventWord w) 1 N) * ε :=
          mul_le_mul_of_nonneg_left (hbound _ hgood.1 hgood.2) measureReal_nonneg
        _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hc hε
    · have hzero : (pathMeasure rate n N) (E w) = 0 := by
        apply (PMF.toMeasure_apply_eq_zero_iff _ (show MeasurableSet (E w) from trivial)).mpr
        apply Set.disjoint_left.mpr
        intro p hsupport hp
        have heq := hobs hp.2.2.2
        have hpath := (mem_support_pathLaw_iff p).mp hsupport
        apply hgood
        refine ⟨?_, ?_⟩
        · intro k hk
          have ha : (p.eval N).active.Nonempty := by rw [FinitePath.eval_last]; exact hp.1
          simpa only [heq] using hpath.observedWalk_pos ha hk
        · simpa only [heq] using hp.2.1
      rw [measureReal_def, hzero, ENNReal.toReal_zero]
      exact mul_nonneg hε measureReal_nonneg
  have hdisj : Pairwise (fun v w ↦ Disjoint (fiber v) (fiber w)) := by
    intro v w hvw
    apply Set.disjoint_left.mpr
    intro p hpv hpw
    exact hvw (hpv.symm.trans hpw)
  have hunion : (⋃ w, fiber w) = Set.univ := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨observedEventWord p, rfl⟩
  have hsum : ∑ w, (pathMeasure rate n N).real (fiber w) = 1 := by
    rw [← measureReal_iUnion_fintype hdisj (fun _ ↦ by trivial), hunion, probReal_univ]
  calc
    _ ≤ (pathMeasure rate n N).real (⋃ w, E w) := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro p hp
      exact Set.mem_iUnion.mpr ⟨observedEventWord p, hp.1, hp.2.1, hp.2.2, rfl⟩
    _ ≤ ∑ w, (pathMeasure rate n N).real (E w) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ w, ε * (pathMeasure rate n N).real (fiber w) := Finset.sum_le_sum (fun w _ ↦ hEbound w)
    _ = ε := by rw [← Finset.mul_sum, hsum, mul_one]

end HeightPaper.Model
