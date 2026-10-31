module

public import HeightPaper.Probability.CorrectedCouplingWord
public import HeightPaper.Probability.CountCouplingLaw

/-!
# Law of an adaptive recovery word

The common uniform sequence realizes every finite history of the conditional
recovery kernel. This is one marginal-law ingredient for the corrected
geometric tree coupling; it does not yet construct the forest sandwich.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

instance : MeasurableSpace (List Bool) := ⊤

theorem measurable_recoveryThresholdBirth (a : ℝ) :
    Measurable (recoveryThresholdBirth a) := by
  have h : MeasurableSet {x : ℝ | a ≤ x} := measurableSet_Ici
  unfold recoveryThresholdBirth
  have heq : (fun x : ℝ ↦ decide (a ≤ x)) =
      (fun x : ℝ ↦ if a ≤ x then true else false) := by
    funext x
    by_cases hx : a ≤ x <;> simp [hx]
  rw [heq]
  exact (measurable_const.ite h measurable_const :
    Measurable (fun x : ℝ ↦ if a ≤ x then true else false))

theorem adaptiveCouplingWord_congr_prefix (r : List Bool → ℝ)
    {u v : ℕ → ℝ} (k : ℕ) (huv : ∀ i < k, u i = v i) :
    adaptiveCouplingWord r u k = adaptiveCouplingWord r v k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [adaptiveCouplingWord_succ,
        ih (fun i hi ↦ huv i (by omega)), huv k (by omega)]

theorem measurable_adaptiveCouplingWord (r : List Bool → ℝ) (k : ℕ) :
    Measurable (fun u : ℕ → ℝ ↦ adaptiveCouplingWord r u k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      have hm : Measurable (fun x : List Bool × ℝ ↦
          x.1 ++ [recoveryThresholdBirth (r x.1) x.2]) := by
        apply measurable_from_prod_countable_right
        intro w
        exact (measurable_of_countable (fun b : Bool ↦ w ++ [b])).comp
          (measurable_recoveryThresholdBirth (r w))
      exact hm.comp (ih.prodMk (measurable_pi_apply k))

theorem adaptiveCouplingWord_indep_next (r : List Bool → ℝ) (k : ℕ) :
    IndepFun (fun u : ℕ → ℝ ↦ adaptiveCouplingWord r u k)
      (fun u ↦ u k) uniformLaw := by
  have hind := uniformLaw_independent.indepFun_set (Set.Iio k) {k}
    (by
      apply Set.disjoint_left.mpr
      intro i hi hsingle
      simp only [Set.mem_Iio, Set.mem_singleton_iff] at hi hsingle
      omega) (fun i ↦ measurable_pi_apply i)
  have hh := hind.comp
    ((measurable_adaptiveCouplingWord r k).comp (measurable_extendPast k))
    (measurable_pi_apply (⟨k, by simp⟩ : ({k} : Set ℕ)))
  have heq : ((fun u : ℕ → ℝ ↦ adaptiveCouplingWord r u k) ∘ extendPast k) ∘
      (fun (u : ℕ → ℝ) (i : Set.Iio k) ↦ u i) =
        (fun u : ℕ → ℝ ↦ adaptiveCouplingWord r u k) := by
    funext u
    apply adaptiveCouplingWord_congr_prefix
    intro i hi
    simp [extendPast, hi]
  rw [heq] at hh
  exact hh

/-- The genuine one-step law induced by a fresh uniform draw. -/
noncomputable def adaptiveCouplingStepLaw (r : List Bool → ℝ)
    (w : List Bool) : PMF (List Bool) :=
  (unitUniform.map (fun x ↦ w ++ [recoveryThresholdBirth (r w) x])).toPMF

theorem unitUniform_lt_of_unit {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    unitUniform {x : ℝ | x < t} = ENNReal.ofReal t := by
  have heq : Set.Iio t ∩ Set.Icc (0 : ℝ) 1 = Set.Ico 0 t := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨hxt, hx0, _⟩
      exact ⟨hx0, hxt⟩
    · rintro ⟨hx0, hxt⟩
      exact ⟨hxt, hx0, hxt.le.trans ht1⟩
  rw [show {x : ℝ | x < t} = Set.Iio t from rfl,
    unitUniform, Measure.restrict_apply measurableSet_Iio, heq,
    Real.volume_Ico, sub_zero]

theorem unitUniform_ge_of_unit {t : ℝ} (ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    unitUniform {x : ℝ | t ≤ x} = ENNReal.ofReal (1 - t) := by
  have heq : Set.Ici t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc t 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨htx, _, hx1⟩
      exact ⟨htx, hx1⟩
    · rintro ⟨htx, hx1⟩
      exact ⟨htx, ht0.trans htx, hx1⟩
  rw [show {x : ℝ | t ≤ x} = Set.Ici t from rfl,
    unitUniform, Measure.restrict_apply measurableSet_Ici, heq,
    Real.volume_Icc]

/-- The recovery mass of the one-step law is the prescribed conditional
recovery probability. -/
theorem adaptiveCouplingStepLaw_recovery {r : List Bool → ℝ} {w : List Bool}
    (hr0 : 0 ≤ r w) (hr1 : r w ≤ 1) :
    adaptiveCouplingStepLaw r w (w ++ [false]) = ENNReal.ofReal (r w) := by
  have hm : Measurable (fun x : ℝ ↦ w ++ [recoveryThresholdBirth (r w) x]) :=
    (measurable_of_countable (fun b : Bool ↦ w ++ [b])).comp
      (measurable_recoveryThresholdBirth (r w))
  have hpre : (fun x : ℝ ↦ w ++ [recoveryThresholdBirth (r w) x]) ⁻¹'
      {w ++ [false]} = {x : ℝ | x < r w} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro hh
      have hb := List.append_cancel_left hh
      have hf : recoveryThresholdBirth (r w) x = false := by simpa using hb
      by_contra hn
      have hle : r w ≤ x := le_of_not_gt hn
      simp [recoveryThresholdBirth, hle] at hf
    · intro hx
      have hn : ¬ r w ≤ x := not_le.mpr hx
      simp [recoveryThresholdBirth, hn]
  rw [adaptiveCouplingStepLaw, Measure.toPMF_apply,
    Measure.map_apply hm (measurableSet_singleton _), hpre,
    unitUniform_lt_of_unit hr0 hr1]

/-- The complementary birth mass is `1-r`. -/
theorem adaptiveCouplingStepLaw_birth {r : List Bool → ℝ} {w : List Bool}
    (hr0 : 0 ≤ r w) (hr1 : r w ≤ 1) :
    adaptiveCouplingStepLaw r w (w ++ [true]) =
      ENNReal.ofReal (1 - r w) := by
  have hm : Measurable (fun x : ℝ ↦ w ++ [recoveryThresholdBirth (r w) x]) :=
    (measurable_of_countable (fun b : Bool ↦ w ++ [b])).comp
      (measurable_recoveryThresholdBirth (r w))
  have hpre : (fun x : ℝ ↦ w ++ [recoveryThresholdBirth (r w) x]) ⁻¹'
      {w ++ [true]} = {x : ℝ | r w ≤ x} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro hh
      have hb := List.append_cancel_left hh
      have ht : recoveryThresholdBirth (r w) x = true := by simpa using hb
      simpa [recoveryThresholdBirth] using ht
    · intro hx
      simp [recoveryThresholdBirth, hx]
  rw [adaptiveCouplingStepLaw, Measure.toPMF_apply,
    Measure.map_apply hm (measurableSet_singleton _), hpre,
    unitUniform_ge_of_unit hr0 hr1]

noncomputable def adaptiveCouplingWordLaw (r : List Bool → ℝ) : ℕ → PMF (List Bool)
  | 0 => PMF.pure []
  | k + 1 => (adaptiveCouplingWordLaw r k).bind (adaptiveCouplingStepLaw r)

/-- Finite-word law of the adaptive process.  This applies even when a
previous word has probability zero, because its step kernel is totalized. -/
theorem adaptiveCouplingWord_law (r : List Bool → ℝ) (k : ℕ) :
    uniformLaw.map (fun u ↦ adaptiveCouplingWord r u k) =
      (adaptiveCouplingWordLaw r k).toMeasure := by
  induction k with
  | zero => simp [adaptiveCouplingWord, adaptiveCouplingWordLaw, PMF.toMeasure_pure]
  | succ k ih =>
      have heq : (fun u : ℕ → ℝ ↦ adaptiveCouplingWord r u (k + 1)) =
          fun u ↦ adaptiveCouplingWord r u k ++
            [recoveryThresholdBirth (r (adaptiveCouplingWord r u k)) (u k)] := by
        funext u
        rfl
      rw [heq]
      refine uniform_independent_update
        (fun u ↦ adaptiveCouplingWord r u k) k
        (fun w x ↦ w ++ [recoveryThresholdBirth (r w) x])
        (adaptiveCouplingWordLaw r k) (adaptiveCouplingStepLaw r)
        (measurable_adaptiveCouplingWord r k) ?_ ?_
        (adaptiveCouplingWord_indep_next r k) ih ?_
      · intro w
        exact (measurable_of_countable (fun b : Bool ↦ w ++ [b])).comp
          (measurable_recoveryThresholdBirth (r w))
      · rw [← heq]
        exact measurable_adaptiveCouplingWord r (k + 1)
      · intro w
        have hm : Measurable
            (fun x : ℝ ↦ w ++ [recoveryThresholdBirth (r w) x]) :=
          (measurable_of_countable (fun b : Bool ↦ w ++ [b])).comp
            (measurable_recoveryThresholdBirth (r w))
        change uniformLaw.map
          ((fun x : ℝ ↦ w ++ [recoveryThresholdBirth (r w) x]) ∘
            (fun u : ℕ → ℝ ↦ u k)) = _
        rw [← Measure.map_map hm (measurable_pi_apply k), uniformLaw_map_eval]
        exact (Measure.toPMF_toMeasure _).symm

end HeightPaper.CountCoupling
