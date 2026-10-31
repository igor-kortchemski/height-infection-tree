module

public import HeightPaper.Probability.CorrectedCouplingFreshPairs
public import HeightPaper.Probability.UniformWalkBounds

/-!
# Extinction of the constant-threshold upper count walk

For a recovery parameter above one half, the unabsorbed count walk has
negative drift.  The strong law gives a finite hit of zero from every finite
positive initial population.  The actual coupled upper forest still needs a
pathwise identification of its active count with this stopped walk.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal Topology

namespace HeightPaper.CountCoupling

noncomputable def constantThresholdStep (p : ℝ) (k : ℕ)
    (u : ℕ → ℝ) : ℝ :=
  if recoveryThresholdBirth p (u k) then 1 else -1

theorem measurable_constantThresholdStep (p : ℝ) (k : ℕ) :
    Measurable (constantThresholdStep p k) := by
  exact (measurable_of_countable
    (fun b : Bool ↦ if b then (1 : ℝ) else -1)).comp
    ((measurable_recoveryThresholdBirth p).comp (measurable_pi_apply k))

theorem constantThresholdStep_mem_Icc (p : ℝ) (k : ℕ)
    (u : ℕ → ℝ) :
    constantThresholdStep p k u ∈ Icc (-1 : ℝ) 1 := by
  unfold constantThresholdStep
  split <;> norm_num

theorem integrable_constantThresholdStep (p : ℝ) (k : ℕ) :
    Integrable (constantThresholdStep p k) uniformLaw :=
  Integrable.of_mem_Icc (-1) 1
    (measurable_constantThresholdStep p k).aemeasurable
    (Filter.Eventually.of_forall (constantThresholdStep_mem_Icc p k))

theorem constantThresholdStep_independent (p : ℝ) :
    iIndepFun (constantThresholdStep p) uniformLaw := by
  have hm : Measurable
      (fun x : ℝ ↦ if recoveryThresholdBirth p x then (1 : ℝ) else -1) :=
    (measurable_of_countable
      (fun b : Bool ↦ if b then (1 : ℝ) else -1)).comp
      (measurable_recoveryThresholdBirth p)
  exact uniformLaw_independent.comp
    (fun _ x ↦ if recoveryThresholdBirth p x then (1 : ℝ) else -1)
    (fun _ ↦ hm)

theorem constantThresholdStep_identDistrib (p : ℝ) (i j : ℕ) :
    IdentDistrib (constantThresholdStep p i)
      (constantThresholdStep p j) uniformLaw uniformLaw := by
  have h : IdentDistrib (fun u : ℕ → ℝ ↦ u i)
      (fun u ↦ u j) uniformLaw uniformLaw :=
    ⟨(measurable_pi_apply i).aemeasurable,
      (measurable_pi_apply j).aemeasurable,
      by rw [uniformLaw_map_eval, uniformLaw_map_eval]⟩
  have hm : Measurable
      (fun x : ℝ ↦ if recoveryThresholdBirth p x then (1 : ℝ) else -1) :=
    (measurable_of_countable
      (fun b : Bool ↦ if b then (1 : ℝ) else -1)).comp
      (measurable_recoveryThresholdBirth p)
  convert h.comp hm using 1 <;> funext u <;>
    simp [constantThresholdStep]

theorem integral_constantThresholdStep
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    (∫ u, constantThresholdStep p k u ∂uniformLaw) = 1 - 2 * p := by
  let A : Set (ℕ → ℝ) :=
    {u | recoveryThresholdBirth p (u k) = true}
  have hA : MeasurableSet A :=
    ((measurable_recoveryThresholdBirth p).comp
      (measurable_pi_apply k)) (measurableSet_singleton true)
  have hmass : uniformLaw A = ENNReal.ofReal (1 - p) := by
    have hset : A = (fun u : ℕ → ℝ ↦ u k) ⁻¹' Set.Ici p := by
      ext u
      simp [A, recoveryThresholdBirth]
    rw [hset, ← Measure.map_apply (measurable_pi_apply k)
      measurableSet_Ici, uniformLaw_map_eval]
    exact unitUniform_ge_of_unit hp0 hp1
  have heq : constantThresholdStep p k =
      fun u ↦ 2 * A.indicator (fun _ ↦ (1 : ℝ)) u - 1 := by
    funext u
    simp only [constantThresholdStep, A, Set.indicator,
      Set.mem_ofPred_eq]
    cases recoveryThresholdBirth p (u k) <;> norm_num
  rw [heq, integral_sub
    ((integrable_const (1 : ℝ)).indicator hA |>.const_mul 2)
    (integrable_const 1), integral_const_mul,
    integral_indicator_const _ hA]
  simp only [smul_eq_mul, mul_one, integral_const, probReal_univ]
  rw [Measure.real, hmass,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp1)]
  ring

theorem constantThresholdStep_strongLaw
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ᵐ u ∂uniformLaw,
      Tendsto (fun k : ℕ ↦
        (∑ i ∈ Finset.range k, constantThresholdStep p i u) / k)
        atTop (𝓝 (1 - 2 * p)) := by
  have h := strong_law_ae_real (constantThresholdStep p)
    (integrable_constantThresholdStep p 0)
    (fun i j hij ↦ (constantThresholdStep_independent p).indepFun hij)
    (fun i ↦ constantThresholdStep_identDistrib p i 0)
  rwa [integral_constantThresholdStep hp0 hp1 0] at h

theorem constantCouplingCount_cast (N : ℕ) (p : ℝ)
    (u : ℕ → ℝ) (k : ℕ) :
    (couplingActiveCount N
      (adaptiveCouplingWord (fun _ ↦ p) u k) : ℝ) =
      N + ∑ i ∈ Finset.range k, constantThresholdStep p i u := by
  induction k with
  | zero => simp [couplingActiveCount, adaptiveCouplingWord]
  | succ k ih =>
      rw [adaptiveCouplingWord_succ,
        couplingActiveCount_append_singleton]
      simp only [Finset.sum_range_succ]
      cases hb : recoveryThresholdBirth p (u k) <;>
        simp [constantThresholdStep, hb, ih] <;> ring

theorem constantCouplingCount_strongLaw
    (N : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ᵐ u ∂uniformLaw,
      Tendsto (fun k : ℕ ↦
        (couplingActiveCount N
          (adaptiveCouplingWord (fun _ ↦ p) u k) : ℝ) / k)
        atTop (𝓝 (1 - 2 * p)) := by
  filter_upwards [constantThresholdStep_strongLaw hp0 hp1] with u hu
  have hN : Tendsto (fun k : ℕ ↦ (N : ℝ) / k)
      atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))) using 1
    · funext k
      ring
    · simp
  have hh := hN.add hu
  simpa only [constantCouplingCount_cast, add_div, zero_add]
    using hh

/-- A nearest-neighbor walk started above zero cannot become nonpositive
without visiting zero. -/
theorem constantCouplingCount_hit_zero_of_nonpos
    (N : ℕ) (hN : 0 < N) (p : ℝ) (u : ℕ → ℝ)
    (k : ℕ)
    (hk : couplingActiveCount N
      (adaptiveCouplingWord (fun _ ↦ p) u k) ≤ 0) :
    ∃ j ≤ k,
      couplingActiveCount N
        (adaptiveCouplingWord (fun _ ↦ p) u j) = 0 := by
  induction k with
  | zero =>
      simp [couplingActiveCount, adaptiveCouplingWord] at hk
      omega
  | succ k ih =>
      by_cases hprev : couplingActiveCount N
          (adaptiveCouplingWord (fun _ ↦ p) u k) ≤ 0
      · obtain ⟨j, hjk, hj⟩ := ih hprev
        exact ⟨j, by omega, hj⟩
      · have hpos : 0 < couplingActiveCount N
            (adaptiveCouplingWord (fun _ ↦ p) u k) := by omega
        refine ⟨k + 1, le_rfl, ?_⟩
        simp only [adaptiveCouplingWord_succ,
          couplingActiveCount_append_singleton] at hk ⊢
        cases hb : recoveryThresholdBirth p (u k) <;>
          simp only [hb, ite_true] at hk ⊢ <;> omega

/-- The constant-threshold upper count path started from any finite nonempty
forest becomes empty almost surely when the recovery probability exceeds one
half. -/
theorem constantCouplingCount_ae_hits_zero
    (N : ℕ) (hN : 0 < N)
    {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) :
    ∀ᵐ u ∂uniformLaw, ∃ k,
      couplingActiveCount N
        (adaptiveCouplingWord (fun _ ↦ p) u k) = 0 := by
  filter_upwards [constantCouplingCount_strongLaw N (by linarith) hp1]
    with u hu
  have hneg : 1 - 2 * p < 0 := by linarith
  have hev := (hu.eventually (Iio_mem_nhds hneg)).and
    (eventually_gt_atTop (0 : ℕ))
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  obtain ⟨hdiv, hKpos⟩ := hK K le_rfl
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hcountneg :
      (couplingActiveCount N
        (adaptiveCouplingWord (fun _ ↦ p) u K) : ℝ) < 0 := by
    have hmul := (div_lt_iff₀ hKreal).mp hdiv
    nlinarith
  have hcount : couplingActiveCount N
      (adaptiveCouplingWord (fun _ ↦ p) u K) ≤ 0 := by
    exact_mod_cast hcountneg.le
  obtain ⟨j, _, hj⟩ :=
    constantCouplingCount_hit_zero_of_nonpos N hN p u K hcount
  exact ⟨j, hj⟩

end HeightPaper.CountCoupling
