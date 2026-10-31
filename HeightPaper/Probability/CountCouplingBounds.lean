module

public import HeightPaper.Model.CountCoupling

/-!
# Quantitative agreement of the local and finite-population walks

The probability of any disagreement in the first `K ≤ n` steps is bounded by
`l * K² / n`. The same constant works for every `0 ≤ l ≤ L`, giving the weak
uniformity in the parameter used in the paper. The estimate is obtained on the
actual infinite product of uniform laws, not on a postulated coupling measure.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace HeightPaper.CountCoupling

theorem measurable_budgetBirth (l : ℝ) (n k : ℕ) (H : (ℕ → ℝ) → ℕ)
    (hH : Measurable H) : Measurable (fun u ↦ budgetBirth l n (H u) (u k)) := by
  have hA : MeasurableSet {u : ℕ → ℝ | 0 < H u ∧ u k ≤ finiteThreshold l n (H u)} :=
    (hH measurableSet_Ioi).inter (measurableSet_le (measurable_pi_apply k)
      ((measurable_of_countable (finiteThreshold l n)).comp hH))
  simpa [budgetBirth] using
    (measurable_const.ite hA measurable_const :
      Measurable (fun u : ℕ → ℝ ↦ if 0 < H u ∧ u k ≤ finiteThreshold l n (H u)
        then true else false))

theorem measurable_finiteSusceptible (l : ℝ) (n k : ℕ) :
    Measurable (fun u ↦ finiteSusceptible l n u k) := by
  classical
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      have hb := measurable_budgetBirth l n k (fun u ↦ finiteSusceptible l n u k) ih
      simp only [finiteSusceptible]
      exact Measurable.ite (hb (measurableSet_singleton true))
        ((measurable_of_countable (fun H : ℕ ↦ H - 1)).comp ih) ih

theorem measurable_finiteBirth (l : ℝ) (n k : ℕ) :
    Measurable (fun u ↦ finiteBirth l n u k) :=
  measurable_budgetBirth l n k _ (measurable_finiteSusceptible l n k)

theorem measurable_finiteWalk (l : ℝ) (n k : ℕ) :
    Measurable (fun u ↦ finiteWalk l n u k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [finiteWalk_succ]
      exact ih.add ((measurable_of_countable (fun b : Bool ↦ if b then (1 : ℤ) else -1)).comp
        (measurable_finiteBirth l n k))

/-- The guarded recursion agrees almost surely at every time with the source
formula, so its endpoint repair changes no uniform-sampling probability. -/
theorem finiteBirth_eq_source_ae (l : ℝ) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ u ∂uniformLaw, ∀ k, finiteBirth l n u k = decide (u k ≤ birthThreshold
      (l * (1 - (∑ i ∈ Finset.range k, if finiteBirth l n u i then (1 : ℝ) else 0) / n))) := by
  filter_upwards [uniformLaw_ae_pos] with u hu k
  exact finiteBirth_eq_source l hn u k (hu k)

/-- The rational birth threshold is one-Lipschitz on the nonnegative half-line. -/
theorem birthThreshold_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    birthThreshold b - birthThreshold a ≤ b - a := by
  have hb : 0 ≤ b := ha.trans hab
  have hda : 1 + a ≠ 0 := by positivity
  have hdb : 1 + b ≠ 0 := by positivity
  have heq : birthThreshold b - birthThreshold a = (b - a) / ((1 + b) * (1 + a)) := by
    unfold birthThreshold
    field_simp
    ring
  rw [heq]
  apply div_le_self (sub_nonneg.mpr hab)
  nlinarith

/-- A deterministic upper bound on each potential disagreement interval. -/
theorem threshold_gap_le {l : ℝ} (hl : 0 ≤ l) {n k : ℕ} (hn : 0 < n)
    (hk : k ≤ n) :
    birthThreshold l - finiteThreshold l n (n - k) ≤ l * (k : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpressure : l * ((n - k : ℕ) : ℝ) / n ≤ l := by
    apply (div_le_iff₀ hnR).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le n k) hl
  calc
    _ ≤ l - l * ((n - k : ℕ) : ℝ) / n :=
      birthThreshold_sub_le (by positivity) hpressure
    _ = _ := by
      rw [Nat.cast_sub hk]
      field_simp
      ring

/-- Deterministic envelopes for the events where the common uniforms may
separate the walks. -/
def thresholdGap (l : ℝ) (n k : ℕ) : Set (ℕ → ℝ) :=
  {u | finiteThreshold l n (n - k) < u k ∧ u k ≤ birthThreshold l}

theorem measurableSet_thresholdGap (l : ℝ) (n k : ℕ) :
    MeasurableSet (thresholdGap l n k) := by
  exact (measurableSet_lt measurable_const (measurable_pi_apply k)).inter
    (measurableSet_le (measurable_pi_apply k) measurable_const)

theorem thresholdGap_probability {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : 0 < n)
    (k : ℕ) :
    uniformLaw.real (thresholdGap l n k) =
      birthThreshold l - finiteThreshold l n (n - k) := by
  apply uniformLaw_interval_real k
  · exact birthThreshold_nonneg (by positivity)
  · exact finiteThreshold_le_local hl hn (Nat.sub_le n k)
  · exact birthThreshold_le_one hl

theorem thresholdGap_probability_le {l : ℝ} (hl : 0 ≤ l) {n k : ℕ}
    (hn : 0 < n) (hk : k ≤ n) :
    uniformLaw.real (thresholdGap l n k) ≤ l * (k : ℝ) / n := by
  rw [thresholdGap_probability hl hn]
  exact threshold_gap_le hl hn hk

/-- Any unequal prefix is contained in the union of the coordinate envelopes. -/
theorem prefix_disagreement_subset {l : ℝ} (hl : 0 ≤ l) {n K : ℕ} (hK : K ≤ n) :
    {u | ∃ k ≤ K, finiteWalk l n u k ≠ localWalk l u k} ⊆
      ⋃ i ∈ Finset.range K, thresholdGap l n i := by
  intro u hu
  by_contra h
  have hgap : ∀ i < K, ¬ (finiteThreshold l n (n - i) < u i ∧ u i ≤ birthThreshold l) := by
    intro i hi hg
    apply h
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_range.mpr hi, hg⟩⟩
  obtain ⟨k, hk, hne⟩ := hu
  exact hne (prefix_eq_of_no_threshold_gap hl hK u hgap k hk)

/-- An explicit short-prefix coupling estimate with the source normalization. -/
theorem prefix_disagreement_probability_le {l : ℝ} (hl : 0 ≤ l)
    {n K : ℕ} (hn : 0 < n) (hK : K ≤ n) :
    uniformLaw.real {u | ∃ k ≤ K, finiteWalk l n u k ≠ localWalk l u k} ≤
      l * (K : ℝ) ^ 2 / n := by
  calc
    _ ≤ uniformLaw.real (⋃ i ∈ Finset.range K, thresholdGap l n i) :=
      measureReal_mono (prefix_disagreement_subset hl hK) (measure_ne_top _ _)
    _ ≤ ∑ i ∈ Finset.range K, uniformLaw.real (thresholdGap l n i) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range K, l * (K : ℝ) / n := by
      apply Finset.sum_le_sum
      intro i hi
      have hiK : i ≤ K := (Finset.mem_range.mp hi).le
      exact (thresholdGap_probability_le hl hn (hiK.trans hK)).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hiK) hl)
          (Nat.cast_nonneg n))
    _ = _ := by simp [pow_two]; ring

/-- Parameter-uniform version: the bound contains the fixed upper endpoint,
not a constant chosen after fixing the infection parameter. -/
theorem prefix_disagreement_probability_le_uniform {L : ℝ} {n K : ℕ}
    (hn : 0 < n) (hK : K ≤ n) :
    ∀ l ∈ Icc (0 : ℝ) L,
      uniformLaw.real {u | ∃ k ≤ K, finiteWalk l n u k ≠ localWalk l u k} ≤
        L * (K : ℝ) ^ 2 / n := by
  intro l hl
  exact (prefix_disagreement_probability_le hl.1 hn hK).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl.2 (sq_nonneg _))
      (Nat.cast_nonneg n))

/-- The guarded infection draw has exactly the epidemic event law, including
the exhausted-budget case. -/
theorem uniformLaw_map_budgetBirth (l : ℝ≥0) (n H k : ℕ) :
    uniformLaw.map (fun u ↦ budgetBirth l n H (u k)) =
      (HeightPaper.Model.eventChoice (l / n) H).toMeasure := by
  have hm : Measurable (fun u : ℕ → ℝ ↦ budgetBirth l n H (u k)) := by
    by_cases hH : 0 < H
    · simpa [budgetBirth, hH, localBirth, finiteThreshold] using
        measurable_localBirth ((l : ℝ) * H / n) k
    · simp [budgetBirth, hH]
  have hA : MeasurableSet {u : ℕ → ℝ | budgetBirth l n H (u k) = true} :=
    hm (measurableSet_singleton true)
  have hp : uniformLaw {u | budgetBirth l n H (u k) = true} =
      (HeightPaper.Model.infectionProbability (l / n) H : ENNReal) := by
    by_cases hH : 0 < H
    · have ht : 0 ≤ finiteThreshold l n H := birthThreshold_nonneg (by positivity)
      have ht' : finiteThreshold l n H ≤ 1 := birthThreshold_le_one (by positivity)
      simp only [budgetBirth, hH, true_and, decide_eq_true_eq]
      rw [uniformLaw_le k ht ht', finiteThreshold_eq_infectionProbability,
        ENNReal.ofReal_coe_nnreal]
    · have hz : H = 0 := by omega
      simp [hz]
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply hm (measurableSet_singleton b),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
  cases b with
  | true => exact hp
  | false =>
      have heq : (fun u : ℕ → ℝ ↦ budgetBirth l n H (u k)) ⁻¹' {false} =
          {u | budgetBirth l n H (u k) = true}ᶜ := by
        ext u
        simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_ofPred_eq]
        cases budgetBirth l n H (u k) <;> simp
      rw [heq, measure_compl hA (measure_ne_top _ _), measure_univ, hp]
      rfl

/-- One update of the uniform construction has exactly the count marginal of
the original epidemic state kernel. This includes absorption and exhaustion.
Identification of full path laws additionally uses independence from the past. -/
theorem uniformCountUpdate_law (l : ℝ≥0) (n k : ℕ) (s : HeightPaper.Model.State) :
    uniformLaw.map (fun u ↦ uniformCountUpdate l n (u k) (HeightPaper.Model.counts s)) =
      ((HeightPaper.Model.step (l / n) s).map HeightPaper.Model.counts).toMeasure := by
  let f : Bool → ℕ × ℕ := fun b ↦
    if b = true ∧ 0 < s.susceptible then
      (s.susceptible - 1, HeightPaper.Model.infectious s + 1)
    else (s.susceptible, HeightPaper.Model.infectious s - 1)
  by_cases ha : s.active.Nonempty
  · have hi : HeightPaper.Model.infectious s ≠ 0 := by
      exact ne_of_gt ha.card_pos
    have heq : (fun u : ℕ → ℝ ↦ uniformCountUpdate l n (u k) (HeightPaper.Model.counts s)) =
        f ∘ (fun u ↦ budgetBirth l n s.susceptible (u k)) := by
      funext u
      simp only [uniformCountUpdate, HeightPaper.Model.counts, hi, ↓reduceIte,
        Function.comp_apply, f]
      by_cases hH : 0 < s.susceptible <;> simp [budgetBirth, hH]
    rw [heq, ← Measure.map_map (measurable_of_countable f)
        (measurable_budgetBirth l n k (fun _ ↦ s.susceptible) measurable_const),
      uniformLaw_map_budgetBirth, PMF.toMeasure_map _ _ (measurable_of_countable f),
      HeightPaper.Model.step_counts (l / n) s ha]
  · have hs : s.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have hi : HeightPaper.Model.infectious s = 0 := by
      simp [HeightPaper.Model.infectious, hs]
    rw [HeightPaper.Model.step_absorbed (l / n) hs, PMF.pure_map, PMF.toMeasure_pure]
    simp [uniformCountUpdate, HeightPaper.Model.counts, hi]

end HeightPaper.CountCoupling
