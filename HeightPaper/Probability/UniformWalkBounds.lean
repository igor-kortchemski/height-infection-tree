module

public import HeightPaper.Probability.UniformWalk

/-!
# Uniform lower tails and eventual lower bounds for the local walk

The lower endpoint of a parameter interval controls every larger parameter on
the common uniform probability space. Concentration is derived from bounded
independent increments; the eventual bounds use the strong law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace HeightPaper.CountCoupling

theorem localStep_independent (l : ℝ) : iIndepFun (localStep l) uniformLaw :=
  (localBirth_independent l).comp (fun _ b ↦ if b then (1 : ℝ) else -1)
    (fun _ ↦ measurable_of_countable _)

theorem localStep_identDistrib (l : ℝ) (i j : ℕ) :
    IdentDistrib (localStep l i) (localStep l j) uniformLaw uniformLaw := by
  have h : IdentDistrib (fun u : ℕ → ℝ ↦ u i) (fun u ↦ u j) uniformLaw uniformLaw :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply j).aemeasurable,
      by rw [uniformLaw_map_eval, uniformLaw_map_eval]⟩
  have hm : Measurable (fun x : ℝ ↦ if x ≤ birthThreshold l then (1 : ℝ) else -1) :=
    measurable_const.ite measurableSet_Iic measurable_const
  convert h.comp hm using 1 <;> funext u <;>
    simp [localStep, localBirth]

theorem localStep_subgaussian {l : ℝ} (hl : 0 ≤ l) (k : ℕ) :
    HasSubgaussianMGF (fun u ↦ localStep l k u - localDrift l) 1 uniformLaw := by
  have h := hasSubgaussianMGF_of_mem_Icc (μ := uniformLaw)
    (measurable_localStep l k).aemeasurable
    (Filter.Eventually.of_forall (localStep_mem_Icc l k))
  have hp : ((‖(1 : ℝ) - -1‖₊ / 2) ^ 2 : ℝ≥0) = 1 := by
    apply NNReal.coe_injective
    norm_num [Real.norm_eq_abs]
  simpa only [integral_localStep hl k, hp] using h

theorem localWalk_mono {l₀ l : ℝ} (hl₀ : 0 ≤ l₀) (hl : l₀ ≤ l)
    (u : ℕ → ℝ) (k : ℕ) : localWalk l₀ u k ≤ localWalk l u k := by
  unfold localWalk
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : u i ≤ birthThreshold l₀
  · have hi' := hi.trans (birthThreshold_mono hl₀ hl)
    simp [localBirth, hi, hi']
  · by_cases hi' : u i ≤ birthThreshold l <;> simp [localBirth, hi, hi']

theorem measurable_localWalk (l : ℝ) (k : ℕ) : Measurable (fun u ↦ localWalk l u k) := by
  unfold localWalk
  apply Measurable.const_add
  apply Finset.measurable_sum
  intro i _
  exact (measurable_of_countable (fun b : Bool ↦ if b then (1 : ℤ) else -1)).comp
    (measurable_localBirth l i)

theorem measurable_localWalk_real (l : ℝ) (k : ℕ) :
    Measurable (fun u ↦ (localWalk l u k : ℝ)) := by
  exact (measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp (measurable_localWalk l k)

/-- Hoeffding's lower-tail inequality, with no concentration assumption. -/
theorem localWalk_lower_tail {l : ℝ} (hl : 0 ≤ l) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    uniformLaw.real {u | (localWalk l u k : ℝ) ≤ 1 + k * localDrift l - ε} ≤
      Real.exp (-ε ^ 2 / (2 * k)) := by
  have hi := (localStep_independent l).comp (fun _ x ↦ localDrift l - x)
    (fun _ ↦ measurable_const.sub measurable_id)
  have hs (i : ℕ) : HasSubgaussianMGF (fun u ↦ localDrift l - localStep l i u) 1 uniformLaw := by
    convert (localStep_subgaussian hl i).neg using 1
    funext u
    simp
  have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hi
    (n := k) (fun i _ ↦ hs i) hε
  have heq : {u | ε ≤ ∑ i ∈ Finset.range k, (localDrift l - localStep l i u)} =
      {u | (localWalk l u k : ℝ) ≤ 1 + k * localDrift l - ε} := by
    ext u
    simp only [mem_ofPred_eq, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, localWalk_cast]
    constructor <;> intro hu <;> linarith
  simpa only [Function.comp_def, heq, NNReal.coe_one, mul_one] using h

theorem localDrift_pos {l : ℝ} (hl : 1 < l) : 0 < localDrift l :=
  div_pos (by linarith) (by linarith)

/-- A single bound valid for every parameter above a fixed supercritical value. -/
theorem localWalk_lower_tail_uniform {l₀ l : ℝ} (hl₀ : 1 < l₀) (hl : l₀ ≤ l)
    (k : ℕ) :
    uniformLaw.real {u | (localWalk l u k : ℝ) ≤ 1 + k * localDrift l₀ / 2} ≤
      Real.exp (-(k * localDrift l₀ / 2) ^ 2 / (2 * k)) := by
  have hε : 0 ≤ (k : ℝ) * localDrift l₀ / 2 := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg k) (localDrift_pos hl₀).le) (by norm_num)
  calc
    _ ≤ uniformLaw.real {u | (localWalk l₀ u k : ℝ) ≤
        1 + k * localDrift l₀ - k * localDrift l₀ / 2} := by
      apply measureReal_mono (μ := uniformLaw) ?_ (measure_ne_top _ _)
      intro u hu
      have hm : (localWalk l₀ u k : ℝ) ≤ localWalk l u k :=
        Int.cast_le.mpr (localWalk_mono (by linarith) hl u k)
      change (localWalk l u k : ℝ) ≤ 1 + k * localDrift l₀ / 2 at hu
      change (localWalk l₀ u k : ℝ) ≤ 1 + k * localDrift l₀ - k * localDrift l₀ / 2
      linarith
    _ ≤ _ := localWalk_lower_tail (by linarith) k hε

/-- Almost-sure drift for the unabsorbed integer walk. -/
theorem localWalk_strongLaw {l : ℝ} (hl : 0 ≤ l) :
    ∀ᵐ u ∂uniformLaw, Tendsto (fun k : ℕ ↦ (localWalk l u k : ℝ) / k)
      atTop (𝓝 (localDrift l)) := by
  have h := strong_law_ae_real (localStep l) (integrable_localStep l 0)
    (fun i j hij ↦ (localStep_independent l).indepFun hij)
    (fun i ↦ localStep_identDistrib l i 0)
  rw [integral_localStep hl 0] at h
  filter_upwards [h] with u hu
  have hc := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).add hu
  simpa only [localWalk_cast, add_div, zero_add] using hc

/-- The lower endpoint gives an eventual linear bound simultaneously in all
larger parameters, including an uncountable family of parameters. -/
theorem localWalk_ae_eventually_uniform_lower {l₀ : ℝ} (hl₀ : 1 < l₀) :
    ∀ᵐ u ∂uniformLaw, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ l₀,
      localDrift l₀ / 2 * k ≤ (localWalk l u k : ℝ) := by
  filter_upwards [localWalk_strongLaw (show 0 ≤ l₀ by linarith)] with u hu
  have he := hu.eventually (Ioi_mem_nhds (show localDrift l₀ / 2 < localDrift l₀ by
    linarith [localDrift_pos hl₀]))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (he.and (eventually_gt_atTop 0))
  refine ⟨N, fun k hk l hl ↦ ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (hN k hk).2
  have hh := ((lt_div_iff₀ hk0).mp (hN k hk).1).le
  exact hh.trans (Int.cast_le.mpr (localWalk_mono (by linarith) hl u k))

/-- Failure of the eventual linear lower bound after a deterministic cutoff. -/
def lateLowerFailure (l : ℝ) (N : ℕ) : Set (ℕ → ℝ) :=
  {u | ∃ k, N ≤ k ∧ (localWalk l u k : ℝ) < localDrift l / 2 * k}

theorem measurableSet_lateLowerFailure (l : ℝ) (N : ℕ) :
    MeasurableSet (lateLowerFailure l N) := by
  simp only [lateLowerFailure, ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  by_cases hk : N ≤ k
  · simpa only [hk, true_and] using
      (measurableSet_lt (measurable_localWalk_real l k)
        (measurable_const : Measurable (fun _ : ℕ → ℝ ↦ localDrift l / 2 * k)))
  · simp [hk]

/-- The probability of any late lower-bound failure tends to zero. -/
theorem lateLowerFailure_tendsto {l : ℝ} (hl : 1 < l) :
    Tendsto (fun N ↦ uniformLaw.real (lateLowerFailure l N)) atTop (𝓝 0) := by
  have hanti : Antitone (lateLowerFailure l) := by
    intro N M hNM u hu
    obtain ⟨k, hk, hbad⟩ := hu
    exact ⟨k, hNM.trans hk, hbad⟩
  have hz : uniformLaw (⋂ N, lateLowerFailure l N) = 0 := by
    have hnull : ∀ᵐ u ∂uniformLaw, u ∉ ⋂ N, lateLowerFailure l N := by
      filter_upwards [localWalk_ae_eventually_uniform_lower hl] with u ⟨N, hN⟩
      intro hu
      obtain ⟨k, hk, hbad⟩ := mem_iInter.mp hu N
      exact (not_lt_of_ge (hN k hk l le_rfl)) hbad
    have he : {u : ℕ → ℝ | ¬u ∉ ⋂ N, lateLowerFailure l N} =
        ⋂ N, lateLowerFailure l N := by
      ext u
      simp only [mem_ofPred_eq, not_not]
    exact he ▸ ae_iff.mp hnull
  have ht := tendsto_measure_iInter_atTop (μ := uniformLaw)
    (fun N ↦ (measurableSet_lateLowerFailure l N).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hz] at ht
  simpa only [Function.comp_def, Measure.real, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht

/-- The positive reciprocal in the definition of the manuscript's `M`. -/
noncomputable def positiveReciprocal (l : ℝ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  if 0 < localWalk l u k then (k : ℝ) / localWalk l u k else 0

theorem positiveReciprocal_nonneg (l : ℝ) (u : ℕ → ℝ) (k : ℕ) :
    0 ≤ positiveReciprocal l u k := by
  unfold positiveReciprocal
  split_ifs with h
  · exact div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast h.le)
  · exact le_rfl

theorem positiveReciprocal_le_time (l : ℝ) (u : ℕ → ℝ) (k : ℕ) :
    positiveReciprocal l u k ≤ k := by
  unfold positiveReciprocal
  split_ifs with h
  · have hS : (1 : ℝ) ≤ localWalk l u k := by
      exact_mod_cast (show (1 : ℤ) ≤ localWalk l u k by omega)
    have hSpos : (0 : ℝ) < localWalk l u k := by exact_mod_cast h
    apply (div_le_iff₀ hSpos).mpr
    nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  · exact Nat.cast_nonneg k

theorem positiveReciprocal_le_of_lower {l c : ℝ} (hc : 0 < c)
    (u : ℕ → ℝ) (N : ℕ)
    (h : ∀ k ≥ N, c * k ≤ (localWalk l u k : ℝ)) (k : ℕ) :
    positiveReciprocal l u k ≤ max (N : ℝ) (1 / c) := by
  by_cases hk : k < N
  · exact (positiveReciprocal_le_time l u k).trans
      ((Nat.cast_le.mpr hk.le).trans (le_max_left _ _))
  · have hkN : N ≤ k := by omega
    by_cases hk0 : k = 0
    · simp [positiveReciprocal, hk0]
    · have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
      have hSk := h k hkN
      have hSpos : (0 : ℝ) < localWalk l u k := (mul_pos hc hkpos).trans_le hSk
      have hSI : (0 : ℤ) < localWalk l u k := by exact_mod_cast hSpos
      rw [positiveReciprocal, ite_eq_left hSI]
      apply le_trans _ (le_max_right _ _)
      apply (div_le_iff₀ hSpos).mpr
      rw [one_div_mul_eq_div]
      exact (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hSk)

/-- Almost surely, one finite bound controls every positive reciprocal and
every parameter in the whole half-line above `l₀`. -/
theorem positiveReciprocal_ae_uniform_bounded {l₀ : ℝ} (hl₀ : 1 < l₀) :
    ∀ᵐ u ∂uniformLaw, ∃ R : ℝ, ∀ l ≥ l₀, ∀ k,
      positiveReciprocal l u k ≤ R := by
  filter_upwards [localWalk_ae_eventually_uniform_lower hl₀] with u ⟨N, hN⟩
  refine ⟨max (N : ℝ) (1 / (localDrift l₀ / 2)), fun l hl k ↦ ?_⟩
  exact positiveReciprocal_le_of_lower (half_pos (localDrift_pos hl₀)) u N
    (fun j hj ↦ hN j hj l hl) k

/-- Tightness of all positive reciprocal maxima, uniformly over parameters.
Writing the event with `∃ k` avoids any convention for a supremum on exceptional
null paths; it is exactly the upper-tail event of the supremum on bounded paths. -/
theorem positiveReciprocal_uniform_tight {l₀ : ℝ} (hl₀ : 1 < l₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ l ≥ l₀,
      uniformLaw.real {u | ∃ k, R < positiveReciprocal l u k} ≤ ε := by
  obtain ⟨N, hN⟩ := ((lateLowerFailure_tendsto hl₀).eventually (Iio_mem_nhds hε)).exists
  refine ⟨max (N : ℝ) (1 / (localDrift l₀ / 2)),
    (Nat.cast_nonneg N).trans (le_max_left _ _), fun l hl ↦ ?_⟩
  apply (measureReal_mono (μ := uniformLaw) (s₂ := lateLowerFailure l₀ N) ?_).trans hN.le
  intro u hu
  by_contra hgood
  have hh : ∀ k ≥ N, localDrift l₀ / 2 * k ≤ (localWalk l u k : ℝ) := by
    intro k hk
    have hbase : localDrift l₀ / 2 * k ≤ (localWalk l₀ u k : ℝ) := by
      by_contra hbad
      exact hgood ⟨k, hk, lt_of_not_ge hbad⟩
    exact hbase.trans (Int.cast_le.mpr (localWalk_mono (by linarith) hl u k))
  obtain ⟨k, hk⟩ := hu
  exact (not_lt_of_ge (positiveReciprocal_le_of_lower
    (half_pos (localDrift_pos hl₀)) u N hh k)) hk

end HeightPaper.CountCoupling
