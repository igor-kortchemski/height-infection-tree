module

public import HeightPaper.Probability.CorrectedCouplingInfiniteWord
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Source probabilities and the corrected event on binary path space

Every binary-process probability law supplies the cylinder factors required by
the adaptive realization. No independence of its events is assumed. Recovery
probabilities at null prefixes are totalized by real division by zero.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HeightPaper.CountCoupling

def sourceCylinder (w : List Bool) : Set (ℕ → Bool) :=
  {x | sourceCouplingPrefix x w.length = w}

theorem measurableSet_sourceCylinder (w : List Bool) :
    MeasurableSet (sourceCylinder w) :=
  (measurable_sourceCouplingPrefix w.length) (measurableSet_singleton w)

theorem mem_sourceCylinder_append (x : ℕ → Bool) (w : List Bool) (b : Bool) :
    x ∈ sourceCylinder (w ++ [b]) ↔
      x ∈ sourceCylinder w ∧ x w.length = b := by
  change sourceCouplingPrefix x (w ++ [b]).length = w ++ [b] ↔
    sourceCouplingPrefix x w.length = w ∧ x w.length = b
  rw [List.length_append, List.length_singleton, sourceCouplingPrefix_succ]
  constructor
  · intro h
    obtain ⟨hp, ht⟩ := List.append_inj h (sourceCouplingPrefix_length x w.length)
    exact ⟨hp, by simpa using ht⟩
  · rintro ⟨hp, ht⟩
    rw [hp, ht]

theorem sourceCylinder_append_subset (w : List Bool) (b : Bool) :
    sourceCylinder (w ++ [b]) ⊆ sourceCylinder w :=
  fun x hx ↦ ((mem_sourceCylinder_append x w b).mp hx).1

theorem sourceCylinder_partition (w : List Bool) :
    sourceCylinder w =
      sourceCylinder (w ++ [false]) ∪ sourceCylinder (w ++ [true]) := by
  ext x
  simp only [Set.mem_union, mem_sourceCylinder_append]
  cases x w.length <;> simp

theorem sourceCylinder_children_disjoint (w : List Bool) :
    Disjoint (sourceCylinder (w ++ [false])) (sourceCylinder (w ++ [true])) := by
  apply Set.disjoint_left.mpr
  intro x hf ht
  have hf' := ((mem_sourceCylinder_append x w false).mp hf).2
  have ht' := ((mem_sourceCylinder_append x w true).mp ht).2
  exact Bool.false_ne_true (hf'.symm.trans ht')

/-- The conditional recovery probability, with value zero on null prefixes. -/
noncomputable def sourceRecoveryRate (μ : Measure (ℕ → Bool)) (w : List Bool) : ℝ :=
  μ.real (sourceCylinder (w ++ [false])) / μ.real (sourceCylinder w)

theorem sourceRecoveryRate_mem_unit
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ] (w : List Bool) :
    0 ≤ sourceRecoveryRate μ w ∧ sourceRecoveryRate μ w ≤ 1 := by
  have hn : 0 ≤ μ.real (sourceCylinder (w ++ [false])) := measureReal_nonneg
  have hd : 0 ≤ μ.real (sourceCylinder w) := measureReal_nonneg
  have hle : μ.real (sourceCylinder (w ++ [false])) ≤ μ.real (sourceCylinder w) :=
    measureReal_mono (sourceCylinder_append_subset w false)
  constructor
  · exact div_nonneg hn hd
  · by_cases hz : μ.real (sourceCylinder w) = 0
    · simp [sourceRecoveryRate, hz]
    · exact (div_le_one (lt_of_le_of_ne hd (Ne.symm hz))).mpr hle

theorem sourceRecoveryRate_cylinder_factor
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (w : List Bool) (b : Bool) :
    μ (sourceCylinder (w ++ [b])) =
      μ (sourceCylinder w) * adaptiveStepMass (sourceRecoveryRate μ w) b := by
  have hsum : μ.real (sourceCylinder w) =
      μ.real (sourceCylinder (w ++ [false])) +
        μ.real (sourceCylinder (w ++ [true])) := by
    rw [sourceCylinder_partition w]
    exact measureReal_union (sourceCylinder_children_disjoint w)
      (measurableSet_sourceCylinder _)
  have hn0 : 0 ≤ μ.real (sourceCylinder (w ++ [false])) := measureReal_nonneg
  have hn1 : 0 ≤ μ.real (sourceCylinder (w ++ [true])) := measureReal_nonneg
  have hfalse : μ.real (sourceCylinder (w ++ [false])) =
      μ.real (sourceCylinder w) * sourceRecoveryRate μ w := by
    by_cases hz : μ.real (sourceCylinder w) = 0
    · have hc : μ.real (sourceCylinder (w ++ [false])) = 0 := by linarith
      simp [hz, hc]
    · simp [sourceRecoveryRate, mul_div_cancel₀ _ hz]
  have htrue : μ.real (sourceCylinder (w ++ [true])) =
      μ.real (sourceCylinder w) * (1 - sourceRecoveryRate μ w) := by
    rw [mul_sub, mul_one, ← hfalse]
    linarith
  cases b
  · simp only [adaptiveStepMass, Bool.false_eq_true, ↓reduceIte]
    rw [← ofReal_measureReal (μ := μ) (s := sourceCylinder (w ++ [false])),
      ← ofReal_measureReal (μ := μ) (s := sourceCylinder w),
      ← ENNReal.ofReal_mul (measureReal_nonneg : 0 ≤ μ.real (sourceCylinder w)),
      ← hfalse]
  · simp only [adaptiveStepMass, ↓reduceIte]
    rw [← ofReal_measureReal (μ := μ) (s := sourceCylinder (w ++ [true])),
      ← ofReal_measureReal (μ := μ) (s := sourceCylinder w),
      ← ENNReal.ofReal_mul (measureReal_nonneg : 0 ≤ μ.real (sourceCylinder w)),
      ← htrue]

/-- Every source process satisfies the exact conditional-cylinder hypothesis
of the complete adaptive-process law theorem. -/
theorem sourceRecoveryRate_factors
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (k : ℕ) (w : List Bool) (b : Bool) (hw : w.length = k) :
    μ {x | sourceCouplingPrefix x (k + 1) = w ++ [b]} =
      μ {x | sourceCouplingPrefix x k = w} *
        adaptiveStepMass (sourceRecoveryRate μ w) b := by
  simpa only [sourceCylinder, List.length_append, List.length_singleton, hw] using
    sourceRecoveryRate_cylinder_factor μ w b

/-- The corrected event is a property of the source path, including the
terminal recovery and imposing no bounds after its first extinction. -/
def sourceCorrectedGood (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (x : ℕ → Bool) : Prop :=
  ∀ k : ℕ,
    (∀ j ≤ k, 0 < couplingActiveCount N (sourceCouplingPrefix x j)) →
      p ≤ r (sourceCouplingPrefix x k) ∧ r (sourceCouplingPrefix x k) ≤ q

theorem measurableSet_sourceCorrectedGood
    (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) :
    MeasurableSet {x | sourceCorrectedGood N p q r x} := by
  have hcount (j : ℕ) : Measurable
      (fun x : ℕ → Bool ↦ couplingActiveCount N (sourceCouplingPrefix x j)) :=
    (measurable_of_countable (couplingActiveCount N)).comp
      (measurable_sourceCouplingPrefix j)
  have hrate (j : ℕ) : Measurable
      (fun x : ℕ → Bool ↦ r (sourceCouplingPrefix x j)) :=
    (measurable_of_countable r).comp (measurable_sourceCouplingPrefix j)
  simp only [sourceCorrectedGood, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.imp
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_lt measurable_const (hcount j)
  · exact (measurableSet_le measurable_const (hrate k)).inter
      (measurableSet_le (hrate k) measurable_const)

theorem sourceCorrectedGood_adaptive_iff
    (N : ℕ) (p q : ℝ) (r : List Bool → ℝ) (u : ℕ → ℝ) :
    sourceCorrectedGood N p q r (adaptiveCouplingProcess r u) ↔
      correctedCouplingGood N p q r u := by
  simp only [sourceCorrectedGood, correctedCouplingGood,
    sourceCouplingPrefix_adaptiveCouplingProcess]

/-- Realized prefixes almost surely never belong to a null cylinder. -/
theorem ae_source_prefix_nonnull (μ : Measure (ℕ → Bool)) :
    ∀ᵐ x ∂μ, ∀ k, μ (sourceCylinder (sourceCouplingPrefix x k)) ≠ 0 := by
  have hw (w : List Bool) :
      ∀ᵐ x ∂μ, x ∈ sourceCylinder w → μ (sourceCylinder w) ≠ 0 := by
    by_cases hz : μ (sourceCylinder w) = 0
    · have hnot : ∀ᵐ x ∂μ, x ∉ sourceCylinder w := by
        rw [ae_iff]
        simpa using hz
      filter_upwards [hnot] with x hx
      exact fun hm ↦ False.elim (hx hm)
    · exact Filter.Eventually.of_forall (fun _ _ ↦ hz)
  filter_upwards [ae_all_iff.mpr hw] with x hx
  intro k
  apply hx (sourceCouplingPrefix x k)
  simp [sourceCylinder, sourceCouplingPrefix_length]

/-- Changing a conditional-rate version on null prefixes does not change
the corrected event, up to a null set. -/
theorem sourceCorrectedGood_ae_congr_rate
    (μ : Measure (ℕ → Bool)) (N : ℕ) (p q : ℝ)
    (r s : List Bool → ℝ)
    (hrs : ∀ w, μ (sourceCylinder w) ≠ 0 → r w = s w) :
    ∀ᵐ x ∂μ, sourceCorrectedGood N p q r x ↔ sourceCorrectedGood N p q s x := by
  filter_upwards [ae_source_prefix_nonnull μ] with x hx
  have hrate (k : ℕ) : r (sourceCouplingPrefix x k) = s (sourceCouplingPrefix x k) :=
    hrs _ (hx k)
  simp only [sourceCorrectedGood, hrate]

/-- An arbitrary source probability law is realized by its own conditional
recovery rates and independent uniforms, without extra cylinder hypotheses. -/
theorem source_process_law_canonical_rates
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ] :
    μ = uniformLaw.map (adaptiveCouplingProcess (sourceRecoveryRate μ)) :=
  sourceCouplingProcess_law_of_cylinder_factors μ (sourceRecoveryRate μ)
    (sourceRecoveryRate_mem_unit μ) (sourceRecoveryRate_factors μ)

end HeightPaper.CountCoupling
