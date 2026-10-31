module

public import HeightPaper.Probability.UrnProducts
public import HeightPaper.Probability.KernelTrajectory
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The urn proportion limit and the product criterion

The infinite law below is constructed from the two-colour transition kernel.
The fraction is a bounded martingale on its full-history filtration. Its
limiting mixed-colour moment is the finite-product limit from the appendix.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators

namespace HeightPaper.Urn

noncomputable def transition (D : Schedule) (k : ℕ) : ℤ → PMF ℤ :=
  step (D.total k) (D.increment k) (D.positive k)

theorem measurable_transition (D : Schedule) (k : ℕ) :
    Measurable (fun r ↦ (transition D k r).toMeasure) := measurable_of_countable _

theorem finite_support_transition (D : Schedule) (k : ℕ) (r : ℤ) :
    (transition D k r).support.Finite := finite_support_step _ _ _ _

/-- One probability space carrying the entire actual red-count trajectory. -/
noncomputable def pathMeasure (D : Schedule) (r₀ : ℤ) : Measure (ℕ → ℤ) :=
  FinitePMF.kernelTrajectoryMeasure (transition D) (measurable_transition D) r₀

instance (D : Schedule) (r₀ : ℤ) : IsProbabilityMeasure (pathMeasure D r₀) := by
  unfold pathMeasure
  infer_instance

theorem pathMeasure_map_eval (D : Schedule) (r₀ : ℤ) (k : ℕ) :
    (pathMeasure D r₀).map (fun ω ↦ ω k) = (law D r₀ k).toMeasure :=
  FinitePMF.kernelTrajectoryMeasure_map_eval (transition D) (measurable_transition D) r₀ k

noncomputable def fraction (D : Schedule) (k : ℕ) (ω : ℕ → ℤ) : ℝ :=
  proportion (D.total k) (ω k)

theorem measurable_fraction (D : Schedule) (k : ℕ) : Measurable (fraction D k) :=
  (measurable_of_countable (proportion (D.total k))).comp (measurable_pi_apply k)

theorem ae_fraction_bounds (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) (k : ℕ) :
    ∀ᵐ ω ∂pathMeasure D r₀, 0 ≤ fraction D k ω ∧ fraction D k ω ≤ 1 := by
  filter_upwards [FinitePMF.kernelTrajectory_ae_support_eval (transition D)
    (measurable_transition D) r₀ k] with ω hω
  have h := law_support_valid D r₀ hr₀ hr₀s k (ω k) hω
  have hs : (0 : ℝ) < D.total k := Int.cast_pos.mpr (D.positive k)
  exact ⟨div_nonneg (Int.cast_nonneg h.1) hs.le,
    (div_le_one hs).mpr (Int.cast_le.mpr h.2)⟩

/-- The bounded martingale asserted at the start of the urn appendix. -/
theorem fraction_martingale (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) :
    Martingale (fraction D) Filtration.piLE (pathMeasure D r₀) := by
  apply FinitePMF.kernelTrajectory_martingale (transition D) (measurable_transition D)
    (finite_support_transition D) r₀ (fun k ↦ proportion (D.total k))
    (fun _ ↦ measurable_of_countable _)
  intro k r hr
  obtain ⟨hr0, hrs⟩ := law_support_valid D r₀ hr₀ hr₀s k r hr
  change (∫ q, proportion (D.total (k + 1)) q
    ∂(step (D.total k) (D.increment k) (D.positive k) r).toMeasure) = _
  rw [D.next]
  exact integral_proportion_step _ _ _ (D.positive k)
    (by rw [← D.next]; exact D.positive _) hr0 hrs

/-- The martingale's limit, whose existence is established below. -/
noncomputable def limit (D : Schedule) (r₀ : ℤ) : (ℕ → ℤ) → ℝ :=
  Filtration.piLE.limitProcess (fraction D) (pathMeasure D r₀)

theorem stronglyMeasurable_limit (D : Schedule) (r₀ : ℤ) :
    StronglyMeasurable (limit D r₀) := Filtration.stronglyMeasurable_limit_process'

/-- Almost-sure convergence of the actual urn fraction, with no convergence assumption. -/
theorem ae_fraction_tendsto (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) :
    ∀ᵐ ω ∂pathMeasure D r₀,
      Tendsto (fun k ↦ fraction D k ω) atTop (𝓝 (limit D r₀ ω)) := by
  apply (fraction_martingale D r₀ hr₀ hr₀s).submartingale.ae_tendsto_limitProcess (R := 1)
  intro k
  have hb : ∀ᵐ ω ∂pathMeasure D r₀, ‖fraction D k ω‖ ≤ 1 := by
    filter_upwards [ae_fraction_bounds D r₀ hr₀ hr₀s k] with ω h
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  simpa using eLpNorm_le_of_ae_bound (μ := pathMeasure D r₀) (p := 1)
    (measurable_fraction D k).aestronglyMeasurable hb

theorem ae_limit_bounds (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) :
    ∀ᵐ ω ∂pathMeasure D r₀, 0 ≤ limit D r₀ ω ∧ limit D r₀ ω ≤ 1 := by
  filter_upwards [ae_fraction_tendsto D r₀ hr₀ hr₀s,
    ae_all_iff.mpr (ae_fraction_bounds D r₀ hr₀ hr₀s)] with ω ht hb
  exact ⟨ge_of_tendsto ht (Eventually.of_forall fun n ↦ (hb n).1),
    le_of_tendsto ht (Eventually.of_forall fun n ↦ (hb n).2)⟩

theorem integral_path_eval (D : Schedule) (r₀ : ℤ) (k : ℕ) (f : ℤ → ℝ) :
    (∫ ω, f (ω k) ∂pathMeasure D r₀) = ∫ r, f r ∂(law D r₀ k).toMeasure := by
  rw [← integral_map (measurable_pi_apply k).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable, pathMeasure_map_eval]

/-- The limit retains the initial mean, by bounded convergence. -/
theorem integral_limit (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) :
    (∫ ω, limit D r₀ ω ∂pathMeasure D r₀) = proportion (D.total 0) r₀ := by
  have ht := tendsto_integral_of_dominated_convergence (μ := pathMeasure D r₀)
    (fun _ ↦ (1 : ℝ)) (fun n ↦ (measurable_fraction D n).aestronglyMeasurable)
    (integrable_const _) (fun n ↦ ?_) (ae_fraction_tendsto D r₀ hr₀ hr₀s)
  · have hc : Tendsto (fun n ↦ ∫ ω, fraction D n ω ∂pathMeasure D r₀)
        atTop (𝓝 (proportion (D.total 0) r₀)) := by
      simpa only [fraction, integral_path_eval, integral_proportion_law D r₀ hr₀ hr₀s] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ proportion (D.total 0) r₀)
          atTop (𝓝 (proportion (D.total 0) r₀)))
    exact tendsto_nhds_unique ht hc
  · filter_upwards [ae_fraction_bounds D r₀ hr₀ hr₀s n] with ω h
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

/-- The mixed-colour moment of the almost-sure limit is the source's product formula. -/
theorem integral_mixed_limit (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) :
    (∫ ω, limit D r₀ ω * (1 - limit D r₀ ω) ∂pathMeasure D r₀) =
      proportion (D.total 0) r₀ * (1 - proportion (D.total 0) r₀) * retentionLimit D := by
  have ht := tendsto_integral_of_dominated_convergence (μ := pathMeasure D r₀)
    (F := fun n ω ↦ fraction D n ω * (1 - fraction D n ω))
    (f := fun ω ↦ limit D r₀ ω * (1 - limit D r₀ ω)) (fun _ ↦ (1 : ℝ))
    (fun n ↦ ((measurable_fraction D n).mul
      (measurable_const.sub (measurable_fraction D n))).aestronglyMeasurable)
    (integrable_const _) (fun n ↦ ?_) ?_
  · have hc : Tendsto (fun n ↦ ∫ ω, fraction D n ω * (1 - fraction D n ω)
        ∂pathMeasure D r₀) atTop
        (𝓝 (proportion (D.total 0) r₀ * (1 - proportion (D.total 0) r₀) * retentionLimit D)) := by
      apply (integral_mixed_law_tendsto D r₀ hr₀ hr₀s).congr
      intro n
      exact (integral_path_eval D r₀ n
        (fun r ↦ proportion (D.total n) r * (1 - proportion (D.total n) r))).symm
    exact tendsto_nhds_unique ht hc
  · filter_upwards [ae_fraction_bounds D r₀ hr₀ hr₀s n] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h.1 (sub_nonneg.mpr h.2))]
    nlinarith
  · filter_upwards [ae_fraction_tendsto D r₀ hr₀ hr₀s] with ω h
    exact h.mul (tendsto_const_nhds.sub h)

/-- The first assertion of the source urn proposition, expressed as positive interior mass. -/
theorem interior_probability_pos_iff_product_pos (D : Schedule) (r₀ : ℤ)
    (hr₀ : 0 < r₀) (hr₀s : r₀ < D.total 0) :
    0 < pathMeasure D r₀ {ω | 0 < limit D r₀ ω ∧ limit D r₀ ω < 1} ↔
      0 < retentionLimit D := by
  rw [← integral_mixed_pos_iff _ _ (stronglyMeasurable_limit D r₀).aestronglyMeasurable
      (ae_limit_bounds D r₀ hr₀.le hr₀s.le), integral_mixed_limit D r₀ hr₀.le hr₀s.le]
  have hs : (0 : ℝ) < D.total 0 := Int.cast_pos.mpr (D.positive 0)
  have hp : 0 < proportion (D.total 0) r₀ := div_pos (Int.cast_pos.mpr hr₀) hs
  have hq : proportion (D.total 0) r₀ < 1 :=
    (div_lt_one hs).mpr (Int.cast_lt.mpr hr₀s)
  exact mul_pos_iff_of_pos_left (mul_pos hp (sub_pos.mpr hq))

/-- The equivalent criterion in `prop urnes`, proved for the constructed urn law. -/
theorem interior_probability_pos_iff (D : Schedule) (r₀ : ℤ)
    (hr₀ : 0 < r₀) (hr₀s : r₀ < D.total 0) :
    0 < pathMeasure D r₀ {ω | 0 < limit D r₀ ω ∧ limit D r₀ ω < 1} ↔
      (∀ k, 2 ≤ D.total k) ∧ Summable (relativeSquare D) := by
  rw [interior_probability_pos_iff_product_pos D r₀ hr₀ hr₀s,
    retentionLimit_pos_iff D (by omega)]


/-- Vanishing of the product forces the limit to take only the two endpoint values. -/
theorem ae_limit_endpoints_of_product_zero (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) (hprod : retentionLimit D = 0) :
    ∀ᵐ ω ∂pathMeasure D r₀, limit D r₀ ω = 0 ∨ limit D r₀ ω = 1 := by
  have hm : AEStronglyMeasurable (limit D r₀) (pathMeasure D r₀) :=
    (stronglyMeasurable_limit D r₀).aestronglyMeasurable
  have hb := ae_limit_bounds D r₀ hr₀ hr₀s
  have hn : ∀ᵐ ω ∂pathMeasure D r₀, 0 ≤ limit D r₀ ω * (1 - limit D r₀ ω) :=
    hb.mono fun _ h ↦ mul_nonneg h.1 (sub_nonneg.mpr h.2)
  have hi : Integrable (fun ω ↦ limit D r₀ ω * (1 - limit D r₀ ω)) (pathMeasure D r₀) := by
    refine (integrable_const (1 : ℝ)).mono' (hm.mul (aestronglyMeasurable_const.sub hm)) ?_
    filter_upwards [hb, hn] with ω h hnonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    nlinarith
  have he : (∫ ω, limit D r₀ ω * (1 - limit D r₀ ω) ∂pathMeasure D r₀) = 0 := by
    rw [integral_mixed_limit D r₀ hr₀ hr₀s, hprod, mul_zero]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp he
  filter_upwards [hae] with ω hω
  rcases mul_eq_zero.mp hω with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h).symm

/-- The Bernoulli parameter is the actual initial red fraction. -/
noncomputable def initialParameter (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) : Set.Icc (0 : ℝ) 1 :=
  ⟨proportion (D.total 0) r₀,
    div_nonneg (Int.cast_nonneg hr₀) (Int.cast_nonneg (D.positive 0).le),
    (div_le_one (Int.cast_pos.mpr (D.positive 0))).mpr (Int.cast_le.mpr hr₀s)⟩

/-- The vanishing-product direction produces the precise Bernoulli law. -/
theorem hasLaw_limit_bernoulli_of_product_zero (D : Schedule) (r₀ : ℤ) (hr₀ : 0 ≤ r₀)
    (hr₀s : r₀ ≤ D.total 0) (hprod : retentionLimit D = 0) :
    HasLaw (limit D r₀) (bernoulliMeasure (1 : ℝ) 0 (initialParameter D r₀ hr₀ hr₀s))
      (pathMeasure D r₀) := by
  let A : Set (ℕ → ℤ) := {ω | limit D r₀ ω = 1}
  have hA : MeasurableSet A := measurableSet_eq_fun
    (stronglyMeasurable_limit D r₀).measurable measurable_const
  have heq : limit D r₀ =ᵐ[pathMeasure D r₀] A.indicator (1 : (ℕ → ℤ) → ℝ) := by
    filter_upwards [ae_limit_endpoints_of_product_zero D r₀ hr₀ hr₀s hprod] with ω hω
    rcases hω with h | h <;> simp [A, h]
  have hp : (pathMeasure D r₀).real A = proportion (D.total 0) r₀ := by
    rw [← integral_indicator_one hA, ← integral_congr_ae heq]
    exact integral_limit D r₀ hr₀ hr₀s
  have h := (hasLaw_indicator_one_bernoulliMeasure (M := ℝ) hA.nullMeasurableSet).congr heq
  have hparam : (⟨(pathMeasure D r₀).real A, by simp⟩ : Set.Icc (0 : ℝ) 1) =
      initialParameter D r₀ hr₀ hr₀s := Subtype.ext hp
  simpa only [hparam] using h

/-- The first formulation of `prop urnes`: the actual almost-sure limit is
Bernoulli exactly when the infinite product vanishes. Both colours are initially present. -/
theorem hasLaw_limit_bernoulli_iff (D : Schedule) (r₀ : ℤ)
    (hr₀ : 0 < r₀) (hr₀s : r₀ < D.total 0) :
    HasLaw (limit D r₀) (bernoulliMeasure (1 : ℝ) 0 (initialParameter D r₀ hr₀.le hr₀s.le))
      (pathMeasure D r₀) ↔ retentionLimit D = 0 := by
  constructor
  · intro hlaw
    have he := hlaw.integral_comp
      (f := fun z : ℝ ↦ z * (1 - z))
      (measurable_id.mul (measurable_const.sub measurable_id)).aestronglyMeasurable
    have hz : (∫ ω, limit D r₀ ω * (1 - limit D r₀ ω) ∂pathMeasure D r₀) = 0 := by
      simpa [Function.comp_def, integral_bernoulliMeasure] using he
    rw [integral_mixed_limit D r₀ hr₀.le hr₀s.le] at hz
    have hs : (0 : ℝ) < D.total 0 := Int.cast_pos.mpr (D.positive 0)
    have hp : 0 < proportion (D.total 0) r₀ := div_pos (Int.cast_pos.mpr hr₀) hs
    have hq : proportion (D.total 0) r₀ < 1 :=
      (div_lt_one hs).mpr (Int.cast_lt.mpr hr₀s)
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (mul_pos hp (sub_pos.mpr hq)))
  · exact hasLaw_limit_bernoulli_of_product_zero D r₀ hr₀.le hr₀s.le

end HeightPaper.Urn
