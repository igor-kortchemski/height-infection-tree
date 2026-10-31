module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Stability of weak convergence for varying probability spaces

The finite epidemic path spaces change with the population size. This version
of the usual small-perturbation lemma allows the source space to depend on the
index. It is proved through bounded Lipschitz test functions.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology ENNReal

namespace HeightPaper

variable {ι E Ω' : Type*} {Ω : ι → Type*}
  [∀ i, MeasurableSpace (Ω i)] [MeasurableSpace Ω']
  [MeasurableSpace E] [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {L : Filter ι}
  [L.IsCountablyGenerated]

theorem tendstoInDistribution_of_dist_probability_zero_varying
    {X Y : (i : ι) → Ω i → E} {Z : Ω' → E}
    (hXZ : TendstoInDistribution X L Z μ μ')
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXY : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun i ↦ (μ i).real {ω | ε ≤ dist (Y i ω) (X i ω)}) L (𝓝 0)) :
    TendstoInDistribution Y L Z μ μ' := by
  have hZ : AEMeasurable Z μ' := hXZ.aemeasurable_limit
  rcases isEmpty_or_nonempty E with hE | hE
  · simp
  let x₀ : E := hE.some
  refine ⟨fun i ↦ (hY i).aemeasurable, hZ, ?_⟩
  suffices ∀ (F : E → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y,
      dist (F x) (F y) ≤ C) (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n ↦ ∫ ω, F ω ∂(μ n).map (Y n)) L
        (𝓝 (∫ ω, F ω ∂(μ'.map Z))) by
    apply (tendsto_iff_forall_lipschitz_integral_tendsto).mpr
    exact this
  rintro F ⟨M, hF_bounded⟩ ⟨C, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  obtain rfl | hC := eq_zero_or_pos C
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul]
    simpa using! tendsto_const_nhds
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in L,
      |∫ ω, F ω ∂(μ n).map (Y n) - ∫ ω, F ω ∂(μ'.map Z)| < C * ε by
    intro ε hε
    convert! this (ε / C) (by positivity)
    field_simp
  intro ε hε
  have h_le n :
      |∫ ω, F ω ∂(μ n).map (Y n) - ∫ ω, F ω ∂(μ'.map Z)| ≤
      C * (ε / 2) + M * (μ n).real
        {ω | ε / 2 ≤ dist (Y n ω) (X n ω)} +
      |∫ ω, F ω ∂(μ n).map (X n) - ∫ ω, F ω ∂(μ'.map Z)| := by
    refine (abs_sub_le (∫ ω, F ω ∂(μ n).map (Y n))
      (∫ ω, F ω ∂(μ n).map (X n))
      (∫ ω, F ω ∂(μ'.map Z))).trans ?_
    gcongr
    have h_int_Y : Integrable (fun x ↦ F (Y n x)) (μ n) := by
      refine Integrable.of_bound (hF_cont.measurable.comp (hY n)).aestronglyMeasurable
        (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Y n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans hF_bounded
    have h_int_X : Integrable (fun x ↦ F (X n x)) (μ n) := by
      refine Integrable.of_bound (hF_cont.measurable.comp (hX n)).aestronglyMeasurable
        (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (X n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable
        (fun a ↦ ‖F (Y n a) - F (X n a)‖) (μ n) := by
      simpa only [Pi.sub_apply] using (h_int_Y.sub h_int_X).norm
    have h_dist : Measurable (fun a ↦ dist (Y n a) (X n a)) :=
      (hY n).dist (hX n)
    rw [integral_map (hY n).aemeasurable hF_cont.aestronglyMeasurable,
      integral_map (hX n).aemeasurable hF_cont.aestronglyMeasurable,
      ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc ‖∫ a, F (Y n a) - F (X n a) ∂(μ n)‖
      _ ≤ ∫ a, ‖F (Y n a) - F (X n a)‖ ∂(μ n) :=
          norm_integral_le_integral_norm _
      _ = ∫ a in {x | dist (Y n x) (X n x) < ε / 2},
            ‖F (Y n a) - F (X n a)‖ ∂(μ n) +
          ∫ a in {x | ε / 2 ≤ dist (Y n x) (X n x)},
            ‖F (Y n a) - F (X n a)‖ ∂(μ n) := by
          symm
          simp_rw [← not_lt]
          refine integral_add_compl₀ ?_ h_int_sub
          exact nullMeasurableSet_lt h_dist.aemeasurable (by fun_prop)
      _ ≤ ∫ a in {x | dist (Y n x) (X n x) < ε / 2}, C * (ε / 2) ∂(μ n) +
          ∫ a in {x | ε / 2 ≤ dist (Y n x) (X n x)}, M ∂(μ n) := by
          gcongr ?_ + ?_
          · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
            · exact nullMeasurableSet_lt h_dist.aemeasurable (by fun_prop)
            · intro x hx
              simpa only [Real.norm_eq_abs, Real.dist_eq] using
                (hF_lip.dist_le_mul (Y n x) (X n x)).trans
                  (mul_le_mul_of_nonneg_left hx.le C.coe_nonneg)
          · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
            rw [← dist_eq_norm]
            convert hF_bounded _ _
      _ = C * (ε / 2) * (μ n).real
            {x | dist (Y n x) (X n x) < ε / 2} +
          M * (μ n).real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)} := by
          simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
            Set.univ_inter, smul_eq_mul]
          ring
      _ ≤ C * (ε / 2) + M * (μ n).real
            {ω | ε / 2 ≤ dist (Y n ω) (X n ω)} := by
          rw [mul_assoc]
          gcongr
          grw [measureReal_le_one, mul_one]
  have h_tendsto : Tendsto (fun n ↦
      C * (ε / 2) + M * (μ n).real
        {ω | ε / 2 ≤ dist (Y n ω) (X n ω)} +
      |∫ ω, F ω ∂(μ n).map (X n) - ∫ ω, F ω ∂(μ'.map Z)|)
      L (𝓝 (C * (ε / 2))) := by
    suffices Tendsto (fun n ↦
        C * (ε / 2) + M * (μ n).real
          {ω | ε / 2 ≤ dist (Y n ω) (X n ω)} +
        |∫ ω, F ω ∂(μ n).map (X n) - ∫ ω, F ω ∂(μ'.map Z)|)
        L (𝓝 (C * (ε / 2) + M * 0 + 0)) by simpa using this
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · exact tendsto_const_nhds
    · exact hXY (ε / 2) (by positivity)
    · have hconv := (tendsto_iff_forall_lipschitz_integral_tendsto).mp
        hXZ.tendsto F ⟨M, hF_bounded⟩ ⟨C, hF_lip⟩
      have hdist := tendsto_iff_dist_tendsto_zero.mp hconv
      simpa only [Real.dist_eq, ProbabilityMeasure.coe_mk] using hdist
  have h_lt : (C : ℝ) * (ε / 2) < C * ε :=
    mul_lt_mul_of_pos_left (half_lt_self hε) (by exact_mod_cast hC)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using
    (h_le n).trans_lt hn

end HeightPaper
