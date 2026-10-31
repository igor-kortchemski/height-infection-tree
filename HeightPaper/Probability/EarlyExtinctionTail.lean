module

public import HeightPaper.Probability.EpidemicMoments
public import HeightPaper.Probability.ExtinctionTimes

/-!
# A geometric tail for early extinction

The geometric infectious-count test function killed at extinction contracts
strictly while infection pressure remains uniformly supercritical. Combined
with the one-step extinction flux, it bounds the tail of early extinction
without constructing a branching coupling.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

noncomputable def activeGeometric (q : ℝ) (s : State) : ℝ :=
  if infectious s = 0 then 0 else q ^ infectious s

noncomputable def geometricContraction (R q : ℝ) : ℝ :=
  (R * q ^ 2 + 1) / (q * (1 + R))

theorem activeGeometric_nonneg {q : ℝ} (hq : 0 ≤ q) (s : State) :
    0 ≤ activeGeometric q s := by
  unfold activeGeometric
  split_ifs <;> positivity

theorem geometricContraction_pos {R q : ℝ} (hR : 0 ≤ R) (hq : 0 < q) :
    0 < geometricContraction R q := by unfold geometricContraction; positivity

theorem geometricContraction_lt_one {R q : ℝ} (hR : 0 ≤ R) (hq : 0 < q)
    (hq1 : q < 1) (hRq : 1 < R * q) : geometricContraction R q < 1 := by
  unfold geometricContraction
  apply (div_lt_one (by positivity)).mpr
  have h := mul_neg_of_neg_of_pos (sub_neg.mpr hq1) (sub_pos.mpr hRq)
  nlinarith

theorem geometricContraction_antitone_pressure {R x q : ℝ} (hR : 0 ≤ R)
    (hx : R ≤ x) (hq : 0 < q) (hq1 : q ≤ 1) :
    geometricContraction x q ≤ geometricContraction R q := by
  have hx0 : 0 ≤ x := hR.trans hx
  unfold geometricContraction
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hsq : 0 ≤ 1 - q ^ 2 := by nlinarith
  have hh := mul_nonneg (sub_nonneg.mpr hx) hsq
  have hhh := mul_nonneg hq.le hh
  nlinarith

/-- The geometric test function killed at zero contracts at every active state. -/
theorem step_activeGeometric_integral_le (rate : ℝ≥0) (s : State) {R q : ℝ}
    (hR : 0 ≤ R) (hq : 0 < q) (hq1 : q ≤ 1)
    (hpressure : R ≤ infectionPressure rate s) :
    (∫ t, activeGeometric q t ∂(step rate s).toMeasure) ≤
      geometricContraction R q * activeGeometric q s := by
  by_cases ha : s.active.Nonempty
  · have hz : infectious s ≠ 0 := Nat.ne_of_gt ha.card_pos
    have hle : (∫ t, activeGeometric q t ∂(step rate s).toMeasure) ≤
        ∫ t, q ^ infectious t ∂(step rate s).toMeasure := by
      apply integral_mono (integrable_step _ _ _) (integrable_step _ _ _)
      intro t
      unfold activeGeometric
      split_ifs
      · exact pow_nonneg hq.le _
      · exact le_rfl
    rw [step_infectious_power_integral rate s ha hq] at hle
    have hf := mul_le_mul_of_nonneg_left
      (geometricContraction_antitone_pressure hR hpressure hq hq1) (pow_nonneg hq.le (infectious s))
    exact hle.trans (by simpa [activeGeometric, hz, geometricContraction, mul_comm] using hf)
  · have hzero : infectious s = 0 := by
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp ha)
    rw [step_absorbed rate (Finset.not_nonempty_iff_eq_empty.mp ha), PMF.toMeasure_pure]
    simp [activeGeometric, hzero]

/-- The only additional extinct mass in one event is controlled by the killed
geometric moment at the starting state. -/
theorem step_extinction_integral_le (rate : ℝ≥0) (s : State) {q : ℝ} (hq : 0 < q) :
    (∫ t, {t : State | infectious t = 0}.indicator (fun _ ↦ (1 : ℝ)) t
      ∂(step rate s).toMeasure) ≤
      {t : State | infectious t = 0}.indicator (fun _ ↦ (1 : ℝ)) s + activeGeometric q s / q := by
  have hsupp : ∀ᵐ t ∂(step rate s).toMeasure, t ∈ (step rate s).support := by
    apply ae_iff.mpr
    apply (PMF.toMeasure_apply_eq_zero_iff _ (show MeasurableSet {t | t ∉ (step rate s).support} from trivial)).mpr
    exact Set.disjoint_left.mpr (fun t ht hn ↦ hn ht)
  have h := integral_mono_ae (integrable_step rate s
      ({t : State | infectious t = 0}.indicator (fun _ ↦ (1 : ℝ))))
    (integrable_const ({t : State | infectious t = 0}.indicator (fun _ ↦ (1 : ℝ)) s + activeGeometric q s / q))
    (hsupp.mono (fun t ht ↦ by
      by_cases hs : infectious s = 0
      · simp only [Set.indicator_apply, mem_ofPred_eq, hs, ↓reduceIte, activeGeometric, zero_div, add_zero]
        split_ifs <;> norm_num
      · by_cases hz : infectious t = 0
        · have hi : infectious s = 1 := by
            have hh := infectious_le_step_add_one ht
            omega
          simp [hz, hi, activeGeometric, hq.ne']
        · simp [hz, hs]
          exact div_nonneg (activeGeometric_nonneg hq.le s) hq.le))
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- Finite-horizon killed geometric moments decay exponentially as long as the
worst possible infection pressure remains above `R`. -/
theorem evolve_activeGeometric_integral_le (rate : ℝ≥0) (n horizon k : ℕ)
    {R q : ℝ} (hR : 0 ≤ R) (hq : 0 < q) (hq1 : q ≤ 1)
    (hpressure : R ≤ (rate : ℝ) * (n - horizon : ℕ)) (hk : k ≤ horizon) :
    (∫ s, activeGeometric q s ∂(evolve rate n k).toMeasure) ≤
      q * geometricContraction R q ^ k := by
  induction k with
  | zero => simp [evolve, PMF.toMeasure_pure, activeGeometric]
  | succ k ih =>
    rw [evolve_integral_succ]
    have hstep : (∫ s, (∫ t, activeGeometric q t ∂(step rate s).toMeasure)
        ∂(evolve rate n k).toMeasure) ≤
        ∫ s, geometricContraction R q * activeGeometric q s ∂(evolve rate n k).toMeasure := by
      apply integral_mono_ae (evolve_integrable _ _ _ _) (evolve_integrable _ _ _ _)
      have hsupp : ∀ᵐ s ∂(evolve rate n k).toMeasure, s ∈ (evolve rate n k).support := by
        apply ae_iff.mpr
        apply (PMF.toMeasure_apply_eq_zero_iff _ (show MeasurableSet {s | s ∉ (evolve rate n k).support} from trivial)).mpr
        exact Set.disjoint_left.mpr (fun s hs hn ↦ hn hs)
      filter_upwards [hsupp] with s hs
      apply step_activeGeometric_integral_le rate s hR hq hq1
      apply hpressure.trans
      unfold infectionPressure
      have hh : n - horizon ≤ s.susceptible := (Nat.sub_le_sub_left (by omega : k ≤ horizon) n).trans
        (evolve_susceptible_lower hs)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hh) rate.coe_nonneg
    rw [integral_const_mul] at hstep
    have hmul := mul_le_mul_of_nonneg_left (ih (by omega)) (geometricContraction_pos hR hq).le
    exact hstep.trans (by simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul)

/-- Extinction mass plus the killed geometric budget. -/
noncomputable def extinctionPotential (q ρ : ℝ) (s : State) : ℝ :=
  {t : State | infectious t = 0}.indicator (fun _ ↦ (1 : ℝ)) s +
    activeGeometric q s / (q * (1 - ρ))

theorem step_extinctionPotential_integral_le (rate : ℝ≥0) (s : State) {R q : ℝ}
    (hR : 0 ≤ R) (hq : 0 < q) (hq1 : q < 1) (hRq : 1 < R * q)
    (hpressure : R ≤ infectionPressure rate s) :
    (∫ t, extinctionPotential q (geometricContraction R q) t ∂(step rate s).toMeasure) ≤
      extinctionPotential q (geometricContraction R q) s := by
  have hρ := geometricContraction_lt_one hR hq hq1 hRq
  have hd : 0 < q * (1 - geometricContraction R q) := mul_pos hq (sub_pos.mpr hρ)
  have hA := div_le_div_of_nonneg_right
    (step_activeGeometric_integral_le rate s hR hq hq1.le hpressure) hd.le
  have hE := step_extinction_integral_le rate s hq
  unfold extinctionPotential
  rw [integral_add (integrable_step _ _ _) (integrable_step _ _ _), integral_div]
  have heq : {t : State | infectious t = 0}.indicator (fun _ ↦ (1 : ℝ)) s + activeGeometric q s / q +
      geometricContraction R q * activeGeometric q s / (q * (1 - geometricContraction R q)) =
      {t : State | infectious t = 0}.indicator (fun _ ↦ (1 : ℝ)) s +
        activeGeometric q s / (q * (1 - geometricContraction R q)) := by
    field_simp
    ring
  exact (add_le_add hE hA).trans_eq heq

/-- The extinction budget decreases between any two times inside a uniformly
supercritical early horizon. -/
theorem evolve_extinctionPotential_integral_le (rate : ℝ≥0) (n horizon i j : ℕ)
    {R q : ℝ} (hR : 0 ≤ R) (hq : 0 < q) (hq1 : q < 1) (hRq : 1 < R * q)
    (hpressure : R ≤ (rate : ℝ) * (n - horizon : ℕ)) (hij : i ≤ j) (hj : j ≤ horizon) :
    (∫ s, extinctionPotential q (geometricContraction R q) s ∂(evolve rate n j).toMeasure) ≤
      ∫ s, extinctionPotential q (geometricContraction R q) s ∂(evolve rate n i).toMeasure := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    apply le_trans _ (ih (by omega))
    rw [evolve_integral_succ]
    apply integral_mono_ae (evolve_integrable _ _ _ _) (evolve_integrable _ _ _ _)
    have hsupp : ∀ᵐ s ∂(evolve rate n j).toMeasure, s ∈ (evolve rate n j).support := by
      apply ae_iff.mpr
      apply (PMF.toMeasure_apply_eq_zero_iff _ (show MeasurableSet {s | s ∉ (evolve rate n j).support} from trivial)).mpr
      exact Set.disjoint_left.mpr (fun s hs hn ↦ hn hs)
    filter_upwards [hsupp] with s hs
    apply step_extinctionPotential_integral_le rate s hR hq hq1 hRq
    apply hpressure.trans
    unfold infectionPressure
    have hh : n - horizon ≤ s.susceptible := (Nat.sub_le_sub_left (by omega : j ≤ horizon) n).trans
      (evolve_susceptible_lower hs)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hh) rate.coe_nonneg

/-- Extinction gained between two early times has a geometric tail in the
first time, uniformly over the finite population. -/
theorem evolve_extinction_sub_le_geometric (rate : ℝ≥0) (n horizon i j : ℕ)
    {R q : ℝ} (hR : 0 ≤ R) (hq : 0 < q) (hq1 : q < 1) (hRq : 1 < R * q)
    (hpressure : R ≤ (rate : ℝ) * (n - horizon : ℕ)) (hij : i ≤ j) (hj : j ≤ horizon) :
    (evolve rate n j).toMeasure.real {s | infectious s = 0} -
      (evolve rate n i).toMeasure.real {s | infectious s = 0} ≤
      geometricContraction R q ^ i / (1 - geometricContraction R q) := by
  have hρ := geometricContraction_lt_one hR hq hq1 hRq
  have hd : 0 < q * (1 - geometricContraction R q) := mul_pos hq (sub_pos.mpr hρ)
  have hpot := evolve_extinctionPotential_integral_le rate n horizon i j hR hq hq1 hRq hpressure hij hj
  simp only [extinctionPotential] at hpot
  rw [integral_add (evolve_integrable _ _ _ _) (evolve_integrable _ _ _ _),
    integral_add (evolve_integrable _ _ _ _) (evolve_integrable _ _ _ _),
    integral_indicator_const (1 : ℝ) (show MeasurableSet {s : State | infectious s = 0} from trivial),
    integral_indicator_const (1 : ℝ) (show MeasurableSet {s : State | infectious s = 0} from trivial),
    integral_div, integral_div] at hpot
  simp only [smul_eq_mul, mul_one] at hpot
  have hnonneg : 0 ≤ (∫ s, activeGeometric q s ∂(evolve rate n j).toMeasure) /
      (q * (1 - geometricContraction R q)) :=
    div_nonneg (integral_nonneg (fun s ↦ activeGeometric_nonneg hq.le s)) hd.le
  have hAk := evolve_activeGeometric_integral_le rate n horizon i hR hq hq1.le hpressure (hij.trans hj)
  have hdiv := div_le_div_of_nonneg_right hAk hd.le
  have heq : (q * geometricContraction R q ^ i) / (q * (1 - geometricContraction R q)) =
      geometricContraction R q ^ i / (1 - geometricContraction R q) := by
    field_simp
  rw [heq] at hdiv
  linarith

/-- A genuine-event tail at an extinct later state equals the extra extinct
mass gained after the earlier observation, under the actual path law. -/
theorem evolve_late_extinction_probability_eq (rate : ℝ≥0) (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    (evolve rate n j).toMeasure.real {s | infectious s = 0 ∧ i < eventCount s} =
      (evolve rate n j).toMeasure.real {s | infectious s = 0} -
        (evolve rate n i).toMeasure.real {s | infectious s = 0} := by
  rw [← pathMeasure_event_at rate n j j le_rfl {s | infectious s = 0 ∧ i < eventCount s},
    ← pathMeasure_event_at rate n j j le_rfl {s | infectious s = 0},
    ← pathMeasure_event_at rate n j i hij {s | infectious s = 0}]
  let E := {p : FinitePath j | infectious (p.eval j) = 0}
  let B := {p : FinitePath j | infectious (p.eval i) = 0}
  have hdiff : (pathMeasure rate n j).real
      {p | infectious (p.eval j) = 0 ∧ i < eventCount (p.eval j)} =
      (pathMeasure rate n j).real (E \ B) := by
    apply measureReal_congr
    filter_upwards [ae_supportedPath rate n j] with p hp
    apply propext
    constructor
    · rintro ⟨hz, he⟩
      refine ⟨hz, ?_⟩
      intro hi
      have ha : (p.eval i).active = ∅ := Finset.card_eq_zero.mp hi
      have hs := hp.absorbed_stable hij le_rfl ha
      have hb := evolve_eventCount_le (hp.mem_evolve hij)
      rw [hs] at he
      omega
    · rintro ⟨hz, hi⟩
      exact ⟨hz, hp.active_earlier_lt_eventCount hij le_rfl (Nat.pos_of_ne_zero hi) hz⟩
  change (pathMeasure rate n j).real {p | infectious (p.eval j) = 0 ∧ i < eventCount (p.eval j)} =
    (pathMeasure rate n j).real E - (pathMeasure rate n j).real B
  rw [hdiff, measureReal_sdiff' (show MeasurableSet B from trivial)]
  congr 1
  apply measureReal_congr
  filter_upwards [ae_supportedPath rate n j] with p hp
  apply propext
  constructor
  · rintro (h | h)
    · exact h
    · exact hp.infectious_eq_zero_later hij le_rfl h
  · exact Or.inl

/-- Uniform finite-population geometric bound on extinct histories whose
genuine event count exceeds `i`, within a supercritical early horizon. -/
theorem evolve_late_extinction_le_geometric (rate : ℝ≥0) (n horizon i : ℕ)
    {R q : ℝ} (hR : 0 ≤ R) (hq : 0 < q) (hq1 : q < 1) (hRq : 1 < R * q)
    (hpressure : R ≤ (rate : ℝ) * (n - horizon : ℕ)) (hi : i ≤ horizon) :
    (evolve rate n horizon).toMeasure.real {s | infectious s = 0 ∧ i < eventCount s} ≤
      geometricContraction R q ^ i / (1 - geometricContraction R q) := by
  rw [evolve_late_extinction_probability_eq rate n hi]
  exact evolve_extinction_sub_le_geometric rate n horizon i horizon hR hq hq1 hRq hpressure hi le_rfl

end HeightPaper.Model
