module

public import HeightPaper.Probability.UrnLimits
public import HeightPaper.Probability.MartingaleStrongLaw

/-!
# Recorded colours and the urn draw frequency

The state records both the red count and the latest colour drawn. Consequently
zero increments do not erase draws. The count projection is exactly the original
urn kernel, and both proportions and recorded frequencies converge to one limit.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace HeightPaper.Urn

/-- Unlike the red count alone, the extra Boolean retains draws when `x = 0`. -/
noncomputable def recordedStep (s x : ℤ) (hs : 0 < s) (q : ℤ × Bool) : PMF (ℤ × Bool) :=
  if h : 0 ≤ q.1 ∧ q.1 ≤ s then
    (draw (redProbability s q.1 hs h.1) (redProbability_le_one s q.1 hs h.1 h.2)).map
      (fun b ↦ (if b then q.1 + x else q.1, b))
  else PMF.pure (q.1, false)

theorem recordedStep_map_fst (s x : ℤ) (hs : 0 < s) (q : ℤ × Bool) :
    (recordedStep s x hs q).map Prod.fst = step s x hs q.1 := by
  unfold recordedStep step
  split
  · rw [PMF.map_comp]
    rfl
  · rw [PMF.pure_map]

theorem finite_support_recordedStep (s x : ℤ) (hs : 0 < s) (q : ℤ × Bool) :
    (recordedStep s x hs q).support.Finite := by
  unfold recordedStep
  split
  · exact FinitePMF.finite_support_map _ (Set.toFinite _) _
  · simp only [PMF.support_pure]
    exact Set.finite_singleton _

theorem integral_recordedStep (s x : ℤ) (hs : 0 < s) (q : ℤ × Bool)
    (hr : 0 ≤ q.1) (hrs : q.1 ≤ s) (f : ℤ × Bool → ℝ) :
    (∫ z, f z ∂(recordedStep s x hs q).toMeasure) =
      proportion s q.1 * f (q.1 + x, true) + (1 - proportion s q.1) * f (q.1, false) := by
  rw [recordedStep, dite_eq_left ⟨hr, hrs⟩,
    ← PMF.toMeasure_map _ _ (measurable_of_countable _),
    integral_map_of_stronglyMeasurable (measurable_of_countable _)
      (measurable_of_countable f).stronglyMeasurable, integral_draw]
  rfl

noncomputable def recordedTransition (D : Schedule) (k : ℕ) : (ℤ × Bool) → PMF (ℤ × Bool) :=
  recordedStep (D.total k) (D.increment k) (D.positive k)

theorem measurable_recordedTransition (D : Schedule) (k : ℕ) :
    Measurable (fun q ↦ (recordedTransition D k q).toMeasure) := measurable_of_countable _

theorem finite_support_recordedTransition (D : Schedule) (k : ℕ) (q : ℤ × Bool) :
    (recordedTransition D k q).support.Finite := finite_support_recordedStep _ _ _ _

noncomputable def recordedLaw (D : Schedule) (r₀ : ℤ) (k : ℕ) : PMF (ℤ × Bool) :=
  FinitePMF.kernelEvolve (PMF.pure (r₀, false)) (recordedTransition D) k

/-- The complete red-count marginal is unchanged, including zero-increment steps. -/
theorem recordedLaw_map_fst (D : Schedule) (r₀ : ℤ) (k : ℕ) :
    (recordedLaw D r₀ k).map Prod.fst = law D r₀ k := by
  induction k with
  | zero => exact PMF.pure_map _ _
  | succ k ih =>
      change ((recordedLaw D r₀ k).bind (recordedTransition D k)).map Prod.fst = _
      rw [PMF.map_bind]
      change (recordedLaw D r₀ k).bind (fun q ↦ (recordedTransition D k q).map Prod.fst) = _
      simp_rw [recordedTransition, recordedStep_map_fst]
      change (recordedLaw D r₀ k).bind
        ((step (D.total k) (D.increment k) (D.positive k)) ∘ Prod.fst) = _
      rw [← PMF.bind_map]
      rw [ih]
      rfl

noncomputable def recordedPathMeasure (D : Schedule) (r₀ : ℤ) : Measure (ℕ → ℤ × Bool) :=
  FinitePMF.kernelTrajectoryMeasure (recordedTransition D) (measurable_recordedTransition D)
    (r₀, false)

instance (D : Schedule) (r₀ : ℤ) : IsProbabilityMeasure (recordedPathMeasure D r₀) := by
  unfold recordedPathMeasure
  infer_instance

theorem recordedLaw_support_valid (D : Schedule) (r₀ : ℤ)
    (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ D.total 0) (k : ℕ) (q : ℤ × Bool)
    (hq : q ∈ (recordedLaw D r₀ k).support) : 0 ≤ q.1 ∧ q.1 ≤ D.total k := by
  apply law_support_valid D r₀ hr₀ hr₀s k q.1
  rw [← recordedLaw_map_fst, PMF.mem_support_map_iff]
  exact ⟨q, hq, rfl⟩

noncomputable def recordedFraction (D : Schedule) (k : ℕ) (ω : ℕ → ℤ × Bool) : ℝ :=
  proportion (D.total k) (ω k).1

theorem recordedFraction_martingale (D : Schedule) (r₀ : ℤ)
    (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ D.total 0) :
    Martingale (recordedFraction D) Filtration.piLE (recordedPathMeasure D r₀) := by
  apply FinitePMF.kernelTrajectory_martingale (recordedTransition D)
    (measurable_recordedTransition D) (finite_support_recordedTransition D) (r₀, false)
    (fun k q ↦ proportion (D.total k) q.1) (fun _ ↦ measurable_of_countable _)
  intro k q hq
  have hq' := recordedLaw_support_valid D r₀ hr₀ hr₀s k q hq
  change (∫ z, proportion (D.total (k + 1)) z.1
    ∂(recordedStep (D.total k) (D.increment k) (D.positive k) q).toMeasure) = _
  rw [integral_recordedStep _ _ _ _ hq'.1 hq'.2]
  have h := integral_proportion_step (D.total k) (D.increment k) q.1 (D.positive k)
    (by rw [← D.next]; exact D.positive _) hq'.1 hq'.2
  rw [integral_step _ _ _ _ hq'.1 hq'.2] at h
  rw [D.next]
  exact h


theorem recordedPathMeasure_map_count_eval (D : Schedule) (r₀ : ℤ) (k : ℕ) :
    (recordedPathMeasure D r₀).map (fun ω ↦ (ω k).1) = (law D r₀ k).toMeasure := by
  rw [show (fun ω : ℕ → ℤ × Bool ↦ (ω k).1) = Prod.fst ∘ (fun ω ↦ ω k) from rfl,
    ← Measure.map_map measurable_fst (measurable_pi_apply _)]
  change ((FinitePMF.kernelTrajectoryMeasure (recordedTransition D)
    (measurable_recordedTransition D) (r₀, false)).map (fun ω ↦ ω k)).map Prod.fst = _
  rw [FinitePMF.kernelTrajectoryMeasure_map_eval, PMF.toMeasure_map,
    show FinitePMF.kernelEvolve (PMF.pure (r₀, false)) (recordedTransition D) k =
      recordedLaw D r₀ k from rfl, recordedLaw_map_fst]
  exact measurable_fst

theorem ae_recordedFraction_bounds (D : Schedule) (r₀ : ℤ)
    (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ D.total 0) (k : ℕ) :
    ∀ᵐ ω ∂recordedPathMeasure D r₀,
      0 ≤ recordedFraction D k ω ∧ recordedFraction D k ω ≤ 1 := by
  filter_upwards [FinitePMF.kernelTrajectory_ae_support_eval (recordedTransition D)
    (measurable_recordedTransition D) (r₀, false) k] with ω hω
  have h := recordedLaw_support_valid D r₀ hr₀ hr₀s k (ω k) hω
  have hs : (0 : ℝ) < D.total k := Int.cast_pos.mpr (D.positive k)
  exact ⟨div_nonneg (Int.cast_nonneg h.1) hs.le,
    (div_le_one hs).mpr (Int.cast_le.mpr h.2)⟩

noncomputable def recordedLimit (D : Schedule) (r₀ : ℤ) : (ℕ → ℤ × Bool) → ℝ :=
  Filtration.piLE.limitProcess (recordedFraction D) (recordedPathMeasure D r₀)

theorem ae_recordedFraction_tendsto (D : Schedule) (r₀ : ℤ)
    (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ D.total 0) :
    ∀ᵐ ω ∂recordedPathMeasure D r₀,
      Tendsto (fun k ↦ recordedFraction D k ω) atTop (𝓝 (recordedLimit D r₀ ω)) := by
  apply (recordedFraction_martingale D r₀ hr₀ hr₀s).submartingale.ae_tendsto_limitProcess (R := 1)
  intro k
  have hb : ∀ᵐ ω ∂recordedPathMeasure D r₀, ‖recordedFraction D k ω‖ ≤ 1 := by
    filter_upwards [ae_recordedFraction_bounds D r₀ hr₀ hr₀s k] with ω h
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have hm : Measurable (recordedFraction D k) :=
    (measurable_of_countable (fun q : ℤ × Bool ↦ proportion (D.total k) q.1)).comp
      (measurable_pi_apply k)
  simpa using eLpNorm_le_of_ae_bound (μ := recordedPathMeasure D r₀) (p := 1)
    (f := recordedFraction D k) hm.aestronglyMeasurable hb

/-- The red indicator of a recorded state. The state at time `k + 1` records draw `k + 1`. -/
def drawIndicator (q : ℤ × Bool) : ℝ := if q.2 then 1 else 0

noncomputable def drawDeviation (D : Schedule) (k : ℕ) (ω : ℕ → ℤ × Bool) : ℝ :=
  drawIndicator (ω (k + 1)) - recordedFraction D k ω

theorem drawDeviation_stronglyMeasurable (D : Schedule) (k : ℕ) :
    StronglyMeasurable[Filtration.piLE (k + 1)] (drawDeviation D k) := by
  exact ((measurable_of_countable drawIndicator).comp
    (FinitePMF.measurable_piLE_eval (k + 1))).stronglyMeasurable.sub
    ((((measurable_of_countable (fun q : ℤ × Bool ↦ proportion (D.total k) q.1)).comp
      (FinitePMF.measurable_piLE_eval k)).stronglyMeasurable).mono
        (Filtration.piLE.mono (Nat.le_succ k)))

theorem ae_drawDeviation_norm_le (D : Schedule) (r₀ : ℤ)
    (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ D.total 0) (k : ℕ) :
    ∀ᵐ ω ∂recordedPathMeasure D r₀, ‖drawDeviation D k ω‖ ≤ 1 := by
  filter_upwards [ae_recordedFraction_bounds D r₀ hr₀ hr₀s k] with ω h
  simp only [drawDeviation, drawIndicator, Real.norm_eq_abs]
  split <;> apply abs_le.mpr <;> constructor <;> linarith [h.1, h.2]

theorem condExp_drawIndicator (D : Schedule) (r₀ : ℤ)
    (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ D.total 0) (k : ℕ) :
    (recordedPathMeasure D r₀)[(fun ω ↦ drawIndicator (ω (k + 1))) | Filtration.piLE k]
      =ᵐ[recordedPathMeasure D r₀] recordedFraction D k := by
  apply (FinitePMF.kernelTrajectory_condExp (recordedTransition D)
    (measurable_recordedTransition D) (finite_support_recordedTransition D) (r₀, false)
    k drawIndicator (measurable_of_countable _)).trans
  filter_upwards [FinitePMF.kernelTrajectory_ae_support_eval (recordedTransition D)
    (measurable_recordedTransition D) (r₀, false) k] with ω hω
  have h := recordedLaw_support_valid D r₀ hr₀ hr₀s k (ω k) hω
  change (∫ q, drawIndicator q ∂(recordedStep (D.total k) (D.increment k)
    (D.positive k) (ω k)).toMeasure) = _
  rw [integral_recordedStep _ _ _ _ h.1 h.2]
  simp [drawIndicator, recordedFraction]

theorem condExp_drawDeviation (D : Schedule) (r₀ : ℤ)
    (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ D.total 0) (k : ℕ) :
    (recordedPathMeasure D r₀)[drawDeviation D k | Filtration.piLE k]
      =ᵐ[recordedPathMeasure D r₀] 0 := by
  have hm := recordedFraction_martingale D r₀ hr₀ hr₀s
  have hi := FinitePMF.kernelTrajectory_integrable_eval (recordedTransition D)
    (measurable_recordedTransition D) (finite_support_recordedTransition D)
    (r₀, false) (k + 1) drawIndicator
  have hs := condExp_sub (μ := recordedPathMeasure D r₀) hi (hm.integrable k) (Filtration.piLE k)
  have he := condExp_of_stronglyMeasurable (Filtration.piLE.le k)
    (hm.stronglyAdapted k) (hm.integrable k)
  filter_upwards [hs, condExp_drawIndicator D r₀ hr₀ hr₀s k] with ω hs hd
  change ((recordedPathMeasure D r₀)[(fun ω ↦ drawIndicator (ω (k + 1))) -
    recordedFraction D k | Filtration.piLE k]) ω = 0
  simpa only [Pi.sub_apply, he, hd, sub_self] using hs


theorem ae_recordedLimit_bounds (D : Schedule) (r₀ : ℤ)
    (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ D.total 0) :
    ∀ᵐ ω ∂recordedPathMeasure D r₀,
      0 ≤ recordedLimit D r₀ ω ∧ recordedLimit D r₀ ω ≤ 1 := by
  filter_upwards [ae_recordedFraction_tendsto D r₀ hr₀ hr₀s,
    ae_all_iff.mpr (ae_recordedFraction_bounds D r₀ hr₀ hr₀s)] with ω ht hb
  exact ⟨ge_of_tendsto ht (Eventually.of_forall fun n ↦ (hb n).1),
    le_of_tendsto ht (Eventually.of_forall fun n ↦ (hb n).2)⟩


/-- The empirical fraction of actual red draws, with the source indexing `1, …, n`. -/
noncomputable def recordedDrawFrequency (n : ℕ) (ω : ℕ → ℤ × Bool) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, drawIndicator (ω (i + 1))

/-- The second convergence of `lem:convergence proportion urn`. The proof uses
bounded martingale differences and Cesàro convergence, in place of the cited
conditional Borel–Cantelli ratio theorem. -/
theorem ae_recordedDrawFrequency_tendsto (D : Schedule) (r₀ : ℤ)
    (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ D.total 0) :
    ∀ᵐ ω ∂recordedPathMeasure D r₀,
      Tendsto (fun n ↦ recordedDrawFrequency n ω) atTop (𝓝 (recordedLimit D r₀ ω)) := by
  have hd := bounded_martingale_difference_strongLaw (recordedPathMeasure D r₀)
    Filtration.piLE (drawDeviation D) (drawDeviation_stronglyMeasurable D)
    (ae_drawDeviation_norm_le D r₀ hr₀ hr₀s) (condExp_drawDeviation D r₀ hr₀ hr₀s)
  filter_upwards [hd, ae_recordedFraction_tendsto D r₀ hr₀ hr₀s] with ω hd hp
  have ht := hd.add hp.cesaro
  simp only [zero_add] at ht
  apply ht.congr
  intro n
  simp only [drawDeviation, Finset.sum_sub_distrib, recordedDrawFrequency]
  ring

/-- Both convergences in the source urn lemma, under one concrete probability
law and towards the same measurable random variable in `[0,1]`. -/
theorem ae_convergence_proportion_and_draws (D : Schedule) (r₀ : ℤ)
    (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ D.total 0) :
    ∃ Z : (ℕ → ℤ × Bool) → ℝ, StronglyMeasurable Z ∧
      ∀ᵐ ω ∂recordedPathMeasure D r₀,
        Z ω ∈ Set.Icc (0 : ℝ) 1 ∧
        Tendsto (fun k ↦ ((ω k).1 : ℝ) / D.total k) atTop (𝓝 (Z ω)) ∧
        Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ *
          ∑ i ∈ Finset.range n, if (ω (i + 1)).2 then (1 : ℝ) else 0) atTop (𝓝 (Z ω)) := by
  refine ⟨recordedLimit D r₀, Filtration.stronglyMeasurable_limit_process', ?_⟩
  filter_upwards [ae_recordedLimit_bounds D r₀ hr₀ hr₀s,
    ae_recordedFraction_tendsto D r₀ hr₀ hr₀s,
    ae_recordedDrawFrequency_tendsto D r₀ hr₀ hr₀s] with ω hb hp hd
  simpa only [Set.mem_Icc, recordedFraction, proportion, recordedDrawFrequency, drawIndicator]
    using And.intro hb (And.intro hp hd)

end HeightPaper.Urn
