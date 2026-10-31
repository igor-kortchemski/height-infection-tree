module

public import HeightPaper.Probability.CountCouplingBounds

/-!
# Exact common-uniform realization of the epidemic count path

The complete absorbed count history has the same law as the count projection
of the original finite epidemic. Fresh-coordinate independence is proved from
the product uniform law. The total stopped-walk identity connects this absorbed
history with the source's unabsorbed integer walk.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace HeightPaper.CountCoupling

/-- Counts after a prescribed event, with the original absorbing convention. -/
def countEventUpdate (b : Bool) (c : ℕ × ℕ) : ℕ × ℕ :=
  if c.2 = 0 then c else if b = true ∧ 0 < c.1 then (c.1 - 1, c.2 + 1)
    else (c.1, c.2 - 1)

noncomputable def countKernel (rate : ℝ≥0) (c : ℕ × ℕ) : PMF (ℕ × ℕ) :=
  (HeightPaper.Model.eventChoice rate c.1).map (fun b ↦ countEventUpdate b c)

/-- The actual epidemic kernel is exactly lumpable by its two counts. -/
theorem step_map_counts_eq_countKernel (rate : ℝ≥0) (s : HeightPaper.Model.State) :
    (HeightPaper.Model.step rate s).map HeightPaper.Model.counts =
      countKernel rate (HeightPaper.Model.counts s) := by
  by_cases ha : s.active.Nonempty
  · have hi : HeightPaper.Model.infectious s ≠ 0 := ne_of_gt ha.card_pos
    rw [countKernel, HeightPaper.Model.step_counts rate s ha]
    congr 1
    funext b
    cases b <;> by_cases hH : 0 < s.susceptible <;>
      simp [countEventUpdate, HeightPaper.Model.counts, hi, hH]
  · have hs : s.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have hi : HeightPaper.Model.infectious s = 0 := by
      simp [HeightPaper.Model.infectious, hs]
    rw [HeightPaper.Model.step_absorbed rate hs, PMF.pure_map]
    simp only [countKernel, countEventUpdate, HeightPaper.Model.counts, hi, ↓reduceIte]
    exact (PMF.map_const (p := HeightPaper.Model.eventChoice rate s.susceptible)
      (b := (s.susceptible, 0))).symm

theorem uniformCountUpdate_eq_eventUpdate (l : ℝ) (n : ℕ) (v : ℝ) (c : ℕ × ℕ) :
    uniformCountUpdate l n v c = countEventUpdate (budgetBirth l n c.1 v) c := by
  by_cases hi : c.2 = 0 <;> by_cases hH : 0 < c.1 <;>
    simp [uniformCountUpdate, countEventUpdate, budgetBirth, hi, hH]

/-- The uniform realization of the count kernel, now for every count pair. -/
theorem uniformCountUpdate_kernel (l : ℝ≥0) (n k : ℕ) (c : ℕ × ℕ) :
    uniformLaw.map (fun u ↦ uniformCountUpdate l n (u k) c) =
      (countKernel (l / n) c).toMeasure := by
  have heq : (fun u : ℕ → ℝ ↦ uniformCountUpdate l n (u k) c) =
      (fun b ↦ countEventUpdate b c) ∘ (fun u ↦ budgetBirth l n c.1 (u k)) := by
    funext u
    exact uniformCountUpdate_eq_eventUpdate l n (u k) c
  rw [heq, ← Measure.map_map (measurable_of_countable _)
    (measurable_budgetBirth l n k (fun _ ↦ c.1) measurable_const),
    uniformLaw_map_budgetBirth, PMF.toMeasure_map _ _ (measurable_of_countable _)]
  rfl

/-- An independent fresh draw implements the PMF transition by a genuine bind.
This elementary form is convenient for finite histories with countable values. -/
theorem uniform_independent_update {α β : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    (X : (ℕ → ℝ) → α) (k : ℕ) (f : α → ℝ → β) (p : PMF α) (Q : α → PMF β)
    (hX : Measurable X) (hf : ∀ a, Measurable (f a))
    (hZ : Measurable (fun u ↦ f (X u) (u k)))
    (hind : ProbabilityTheory.IndepFun X (fun u ↦ u k) uniformLaw)
    (hLaw : uniformLaw.map X = p.toMeasure)
    (hQ : ∀ a, uniformLaw.map (fun u ↦ f a (u k)) = (Q a).toMeasure) :
    uniformLaw.map (fun u ↦ f (X u) (u k)) = (p.bind Q).toMeasure := by
  classical
  ext t ht
  rw [Measure.map_apply hZ ht, PMF.toMeasure_bind_apply p Q t ht]
  have hsplit : (fun u : ℕ → ℝ ↦ f (X u) (u k)) ⁻¹' t =
      ⋃ a, X ⁻¹' {a} ∩ (fun u ↦ u k) ⁻¹' ((f a) ⁻¹' t) := by
    ext u
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    constructor
    · intro hu
      exact ⟨X u, rfl, hu⟩
    · rintro ⟨a, ha, hu⟩
      simpa only [ha] using hu
  rw [hsplit, measure_iUnion]
  · apply tsum_congr
    intro a
    rw [hind.measure_inter_preimage_eq_mul {a} ((f a) ⁻¹' t)
      (measurableSet_singleton a) ((hf a) ht)]
    have hp : uniformLaw (X ⁻¹' {a}) = p a := by
      rw [← Measure.map_apply hX (measurableSet_singleton a), hLaw,
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
    have hq : uniformLaw ((fun u ↦ u k) ⁻¹' ((f a) ⁻¹' t)) = (Q a).toMeasure t := by
      change uniformLaw ((fun u : ℕ → ℝ ↦ f a (u k)) ⁻¹' t) = _
      have hm : Measurable (fun u : ℕ → ℝ ↦ f a (u k)) :=
        (hf a).comp (measurable_pi_apply k)
      rw [← Measure.map_apply hm ht, hQ a]
    rw [hp, hq]
  · intro a b hab
    exact Set.disjoint_left.mpr (fun u hua hub ↦ hab (hua.1.symm.trans hub.1))
  · intro a
    exact (hX (measurableSet_singleton a)).inter ((measurable_pi_apply k) ((hf a) ht))

theorem absorbedCounts_congr_prefix (l : ℝ) (n : ℕ) {u v : ℕ → ℝ} (k : ℕ)
    (huv : ∀ j < k, u j = v j) : absorbedCounts l n u k = absorbedCounts l n v k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [absorbedCounts, absorbedCounts, ih (fun j hj ↦ huv j (by omega)), huv k (by omega)]

theorem measurable_absorbedCounts (l : ℝ) (n k : ℕ) :
    Measurable (fun u ↦ absorbedCounts l n u k) := by
  classical
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      have hH := measurable_fst.comp ih
      have hI := measurable_snd.comp ih
      have hb := measurable_budgetBirth l n k (fun u ↦ (absorbedCounts l n u k).1) hH
      have hinc := (measurable_of_countable (fun c : ℕ × ℕ ↦ (c.1 - 1, c.2 + 1))).comp ih
      have hdec := (measurable_of_countable (fun c : ℕ × ℕ ↦ (c.1, c.2 - 1))).comp ih
      simp only [absorbedCounts, uniformCountUpdate]
      exact Measurable.ite (hI (measurableSet_singleton 0)) ih
        (Measurable.ite (hb (measurableSet_singleton true)) hinc hdec)

/-- The full count history, including time zero. -/
noncomputable def uniformCountHistory (l : ℝ) (n : ℕ) (k : ℕ) (u : ℕ → ℝ) :
    Fin (k + 1) → ℕ × ℕ := fun i ↦ absorbedCounts l n u i.val

theorem measurable_uniformCountHistory (l : ℝ) (n k : ℕ) :
    Measurable (uniformCountHistory l n k) := by
  exact measurable_pi_iff.mpr (fun i ↦ measurable_absorbedCounts l n i.val)

def extendPast (k : ℕ) (v : Set.Iio k → ℝ) : ℕ → ℝ :=
  fun i ↦ if hi : i < k then v ⟨i, hi⟩ else 0

theorem measurable_extendPast (k : ℕ) : Measurable (extendPast k) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i < k <;> simp [extendPast, hi]
  exact measurable_pi_apply (⟨i, hi⟩ : Set.Iio k)

/-- The complete past count history is independent of the next uniform draw. -/
theorem uniformCountHistory_indep_next (l : ℝ) (n k : ℕ) :
    ProbabilityTheory.IndepFun (uniformCountHistory l n k) (fun u ↦ u k) uniformLaw := by
  have hind := uniformLaw_independent.indepFun_set (Set.Iio k) {k}
    (by
      apply Set.disjoint_left.mpr
      intro a ha hb
      simp only [Set.mem_Iio, Set.mem_singleton_iff] at ha hb
      omega) (fun i ↦ measurable_pi_apply i)
  have hh := hind.comp
    ((measurable_uniformCountHistory l n k).comp (measurable_extendPast k))
    (measurable_pi_apply (⟨k, by simp⟩ : ({k} : Set ℕ)))
  have heq : (uniformCountHistory l n k ∘ extendPast k) ∘
      (fun (u : ℕ → ℝ) (i : Set.Iio k) ↦ u i) = uniformCountHistory l n k := by
    funext u i
    apply absorbedCounts_congr_prefix
    intro j hj
    have hjk : j < k := lt_of_lt_of_le hj (by have := i.isLt; omega)
    simp [extendPast, hjk]
  rw [heq] at hh
  exact hh

def countAppend {k : ℕ} (c : Fin (k + 1) → ℕ × ℕ) (z : ℕ × ℕ) :
    Fin (k + 2) → ℕ × ℕ := Fin.lastCases z c

noncomputable def countPathLaw (rate : ℝ≥0) (n : ℕ) :
    (k : ℕ) → PMF (Fin (k + 1) → ℕ × ℕ)
  | 0 => PMF.pure (fun _ ↦ (n, 1))
  | k + 1 => (countPathLaw rate n k).bind fun c ↦
      (countKernel rate (c (Fin.last k))).map (fun z ↦ countAppend c z)

def stateCountHistory {k : ℕ} (p : HeightPaper.Model.FinitePath k) :
    Fin (k + 1) → ℕ × ℕ := fun i ↦ HeightPaper.Model.counts (p.state i)

theorem stateCountHistory_append {k : ℕ} (p : HeightPaper.Model.FinitePath k)
    (s : HeightPaper.Model.State) :
    stateCountHistory (p.append s) = countAppend (stateCountHistory p) (HeightPaper.Model.counts s) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;>
    simp [stateCountHistory, HeightPaper.Model.FinitePath.append, countAppend]

/-- The count-history law is exactly the pushforward of the original epidemic
state-history law, including absorbed self-loops. -/
theorem pathLaw_map_stateCountHistory (rate : ℝ≥0) (n k : ℕ) :
    (HeightPaper.Model.pathLaw rate n k).map stateCountHistory = countPathLaw rate n k := by
  induction k with
  | zero =>
      rw [HeightPaper.Model.pathLaw, PMF.pure_map]
      rfl
  | succ k ih =>
      rw [HeightPaper.Model.pathLaw, PMF.map_bind, countPathLaw, ← ih, PMF.bind_map]
      congr 1
      funext p
      rw [PMF.map_comp]
      have heq : stateCountHistory ∘ p.append =
          (fun z ↦ countAppend (stateCountHistory p) z) ∘ HeightPaper.Model.counts := by
        funext s
        exact stateCountHistory_append p s
      rw [heq, ← PMF.map_comp, step_map_counts_eq_countKernel]
      rfl


theorem measurable_uniformCountUpdate (l : ℝ) (n : ℕ) (c : ℕ × ℕ) :
    Measurable (fun v : ℝ ↦ uniformCountUpdate l n v c) := by
  have hB : Measurable (fun v : ℝ ↦ budgetBirth l n c.1 v) := by
    by_cases hH : 0 < c.1
    · simpa [budgetBirth, hH] using
        (measurable_const.ite (measurableSet_le measurable_id measurable_const) measurable_const :
          Measurable (fun v : ℝ ↦ if v ≤ finiteThreshold l n c.1 then true else false))
    · simp [budgetBirth, hH]
  simp_rw [uniformCountUpdate_eq_eventUpdate]
  exact (measurable_of_countable (fun b : Bool ↦ countEventUpdate b c)).comp hB

theorem uniformCountHistory_succ (l : ℝ) (n k : ℕ) (u : ℕ → ℝ) :
    uniformCountHistory l n (k + 1) u =
      countAppend (uniformCountHistory l n k u)
        (uniformCountUpdate l n (u k) (uniformCountHistory l n k u (Fin.last k))) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [uniformCountHistory, absorbedCounts, countAppend]

/-- Full finite-dimensional law of the common-uniform absorbed count process.
The independence of the fresh coordinate from the entire past is proved above. -/
theorem uniformCountHistory_law (l : ℝ≥0) (n k : ℕ) :
    uniformLaw.map (uniformCountHistory l n k) = (countPathLaw (l / n) n k).toMeasure := by
  induction k with
  | zero =>
      have heq : uniformCountHistory (l : ℝ) n 0 = fun _ ↦ fun _ ↦ (n, 1) := by
        funext u i
        simp [uniformCountHistory, absorbedCounts]
      rw [heq, countPathLaw, PMF.toMeasure_pure]
      simp
  | succ k ih =>
      have heq : uniformCountHistory (l : ℝ) n (k + 1) = fun u ↦
          countAppend (uniformCountHistory l n k u)
            (uniformCountUpdate l n (u k) (uniformCountHistory l n k u (Fin.last k))) := funext (uniformCountHistory_succ l n k)
      rw [heq, countPathLaw]
      refine uniform_independent_update (uniformCountHistory l n k) k
        (fun (c : Fin (k + 1) → ℕ × ℕ) (v : ℝ) ↦
          countAppend c (uniformCountUpdate l n v (c (Fin.last k))))
        (countPathLaw (l / n) n k)
        (fun c ↦ (countKernel (l / n) (c (Fin.last k))).map (fun z ↦ countAppend c z))
        (measurable_uniformCountHistory l n k) ?_ ?_ (uniformCountHistory_indep_next l n k) ih ?_
      · intro c
        exact (measurable_of_countable (fun z ↦ countAppend c z)).comp
          (measurable_uniformCountUpdate l n (c (Fin.last k)))
      · rw [← heq]
        exact measurable_uniformCountHistory l n (k + 1)
      · intro c
        have hm : Measurable (fun u : ℕ → ℝ ↦ uniformCountUpdate l n (u k) (c (Fin.last k))) :=
          (measurable_uniformCountUpdate l n (c (Fin.last k))).comp (measurable_pi_apply k)
        calc
          _ = (uniformLaw.map (fun u ↦ uniformCountUpdate l n (u k) (c (Fin.last k)))).map
              (countAppend c) := by
            simpa only [Function.comp_def] using
              (Measure.map_map (μ := uniformLaw) (measurable_of_countable (countAppend c)) hm).symm
          _ = (countKernel (l / n) (c (Fin.last k))).toMeasure.map (countAppend c) := by
            rw [uniformCountUpdate_kernel]
          _ = _ := PMF.toMeasure_map _ _ (measurable_of_countable _)

/-- The complete count path under the common uniforms has the same law as the
count projection of the original finite epidemic, at rate exactly `l / n`. -/
theorem uniformCountHistory_eq_epidemic (l : ℝ≥0) (n k : ℕ) :
    uniformLaw.map (uniformCountHistory l n k) =
      (HeightPaper.Model.pathMeasure (l / n) n k).map stateCountHistory := by
  rw [HeightPaper.Model.pathMeasure,
    PMF.toMeasure_map _ _ (HeightPaper.Model.FinitePath.measurable _),
    pathLaw_map_stateCountHistory]
  exact uniformCountHistory_law l n k

/-- A positive absorbed count at a later time forces positivity at every
previous time, because zero is absorbing. -/
theorem absorbedCounts_pos_past (l : ℝ) (n : ℕ) (u : ℕ → ℝ) {j k : ℕ}
    (hjk : j ≤ k) (hk : 0 < (absorbedCounts l n u k).2) :
    0 < (absorbedCounts l n u j).2 := by
  by_contra hj
  have hz : (absorbedCounts l n u j).2 = 0 := by omega
  have heq := absorbedCounts_absorbed l n u hz (k - j)
  rw [Nat.add_sub_of_le hjk] at heq
  have := congrArg Prod.snd heq
  omega

/-- Conversely, every positive absorbed count agrees with the unabsorbed walk;
positivity certifies that no earlier absorption occurred. -/
theorem absorbedCounts_cast_eq_of_pos (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ)
    (hk : 0 < (absorbedCounts l n u k).2) :
    ((absorbedCounts l n u k).2 : ℤ) = finiteWalk l n u k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      apply (absorbedCounts_eq_before_hit l n u k ?_).2
      intro j hj
      have hp := absorbedCounts_pos_past l n u hj.le hk
      rw [← ih j hj hp]
      exact_mod_cast hp

/-- Survival of the unabsorbed walk through a fixed horizon is exactly survival
of its absorbed count realization through that horizon. -/
theorem finiteWalk_survival_iff (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (K : ℕ) :
    (∀ j ≤ K, 0 < finiteWalk l n u j) ↔
      (∀ j ≤ K, 0 < (absorbedCounts l n u j).2) := by
  constructor
  · intro h j hj
    have heq := (absorbedCounts_eq_before_hit l n u j
      (fun i hi ↦ h i (hi.le.trans hj))).2
    have hp := h j hj
    rw [← heq] at hp
    exact_mod_cast hp
  · intro h j hj
    rw [← absorbedCounts_cast_eq_of_pos l n u j (h j hj)]
    exact_mod_cast h j hj

/-- A total stopped-walk identity: after any visit to zero the absorbed process
stays zero, even if the source unabsorbed walk subsequently becomes positive. -/
theorem absorbedCounts_integer_stopped (l : ℝ) (n : ℕ) (u : ℕ → ℝ) (k : ℕ) :
    ((absorbedCounts l n u k).2 : ℤ) =
      if ∀ j ≤ k, 0 < finiteWalk l n u j then finiteWalk l n u k else 0 := by
  classical
  by_cases h : ∀ j ≤ k, 0 < finiteWalk l n u j
  · rw [ite_eq_left h]
    exact (absorbedCounts_eq_before_hit l n u k (fun j hj ↦ h j hj.le)).2
  · rw [ite_eq_right h]
    have hz : (absorbedCounts l n u k).2 = 0 := by
      by_contra hz
      have hp : 0 < (absorbedCounts l n u k).2 := by omega
      apply h
      exact (finiteWalk_survival_iff l n u k).mpr
        (fun j hj ↦ absorbedCounts_pos_past l n u hj hp)
    simp [hz]

end HeightPaper.CountCoupling
