/-
The proof of the varying-space perturbation lemma below adapts Mathlib's
`MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`.
Copyright (c) 2025 Rémy Degenne. Released under Apache 2.0 license.
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Probability reductions for the infection-tree height

The epidemic for each population size may live on a different probability
space. This file supplies the perturbation step of the main proof without
assuming a common coupling. Its hypotheses are explicit intermediate estimates,
not a proof of the epidemic estimates themselves.
-/

public section

open Filter ProbabilityTheory MeasureTheory BoundedContinuousFunction
open scoped Topology

namespace HeightPaper

variable {ι E Ω' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mE : MeasurableSpace E} [SeminormedAddCommGroup E]
  [SecondCountableTopology E] [BorelSpace E]
  {X Y : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filter ι}

set_option backward.isDefEq.respectTransparency.types false in
/-- Convergence in law from approximants chosen separately at each error scale.
This permits the epidemic cutoff to depend on the requested tolerance. -/
theorem tendstoInDistribution_of_varying_approximants
    [l.IsCountablyGenerated]
    (hZ : AEMeasurable Z μ')
    (hY : ∀ i, AEMeasurable (Y i) (μ i))
    (happrox : ∀ ε > (0 : ℝ), ∃ X : (i : ι) → Ω i → E,
      TendstoInDistribution X l Z μ μ' ∧
      Tendsto (fun i ↦ (μ i).real {ω | ε ≤ ‖Y i ω - X i ω‖}) l (𝓝 0)) :
    TendstoInDistribution Y l Z μ μ' := by
  rcases isEmpty_or_nonempty E with hE | hE
  · simp
  let x₀ : E := hE.some
  refine ⟨hY, hZ, ?_⟩
  -- We show convergence in distribution by verifying the convergence of integrals of any bounded
  -- Lipschitz function `F`
  suffices ∀ (F : E → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n ↦ ∫ ω, F ω ∂((μ n).map (Y n))) l (𝓝 (∫ ω, F ω ∂(μ'.map Z))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  -- If `F` is 0-Lipschitz, then it is constant, and all integrals are equal to that constant
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul]
    simpa using! tendsto_const_nhds
  -- now `F` is `L`-Lipschitz with `L > 0`
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in l, |∫ ω, F ω ∂((μ n).map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)| < L * ε by
    intro ε hε
    convert! this (ε / L) (by positivity)
    field_simp
  intro ε hε
  obtain ⟨X, hXZ, hXY⟩ := happrox (ε / 2) (by positivity)
  have hX : ∀ i, AEMeasurable (X i) (μ i) := hXZ.forall_aemeasurable
  -- We cut the difference into three pieces, two of which are small by the convergence assumptions
  have h_le n : |∫ ω, F ω ∂((μ n).map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)|
      ≤ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂((μ n).map (X n)) - ∫ ω, F ω ∂(μ'.map Z)| := by
    refine (abs_sub_le (∫ ω, F ω ∂((μ n).map (Y n))) (∫ ω, F ω ∂((μ n).map (X n)))
      (∫ ω, F ω ∂(μ'.map Z))).trans ?_
    gcongr
    -- `⊢ |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ.map (X n))|`
    -- `    ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}`
    -- We prove integrability of the functions involved to be able to manipulate the integrals.
    have h_int_Y : Integrable (fun x ↦ F (Y n x)) (μ n) := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Y n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans hF_bounded
    have h_int_X : Integrable (fun x ↦ F (X n x)) (μ n) := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (X n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable (fun a ↦ ‖F (Y n a) - F (X n a)‖) (μ n) := by
      rw [integrable_norm_iff (by fun_prop)]
      exact h_int_Y.sub h_int_X
    -- Now we prove the inequality
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
      ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc ‖∫ a, F (Y n a) - F (X n a) ∂(μ n)‖
    _ ≤ ∫ a, ‖F (Y n a) - F (X n a)‖ ∂(μ n) := norm_integral_le_integral_norm _
    -- Either `‖Y n x - X n x‖` is smaller than `ε / 2`, or it is not
    _ = ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, ‖F (Y n a) - F (X n a)‖ ∂(μ n)
        + ∫ a in {x | ε / 2 ≤ ‖Y n x - X n x‖}, ‖F (Y n a) - F (X n a)‖ ∂(μ n) := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ h_int_sub
      exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
    -- If it is smaller, we use the Lipschitz property of `F`
    -- If not, we use the boundedness of `F`.
    _ ≤ ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, L * (ε / 2) ∂(μ n)
        + ∫ a in {x | ε / 2 ≤ ‖Y n x - X n x‖}, M ∂(μ n) := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        · exact fun x hx ↦ hF_lip.norm_sub_le_of_le hx.le
      · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
        rw [← dist_eq_norm]
        convert hF_bounded _ _
    -- The goal is now a simple computation
    _ = L * (ε / 2) * (μ n).real {x | ‖Y n x - X n x‖ < ε / 2}
        + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul]
      ring
    _ ≤ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖} := by
      rw [mul_assoc]
      gcongr
      grw [measureReal_le_one, mul_one]
  -- We finally show that the right-hand side tends to `L * ε / 2`, which is smaller than `L * ε`
  have h_tendsto :
      Tendsto (fun n ↦ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂((μ n).map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n ↦ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂((μ n).map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · exact hXY
    · replace hXZ := hXZ.tendsto
      simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hXZ
      simpa [tendsto_iff_dist_tendsto_zero] using! hXZ F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn


/-- A perturbation that vanishes in probability preserves convergence in law,
even when the underlying probability spaces vary with the index. -/
theorem tendstoInDistribution_of_varying_error
    [l.IsCountablyGenerated]
    (hXZ : TendstoInDistribution X l Z μ μ')
    (hXY : ∀ ε > (0 : ℝ),
      Tendsto (fun i ↦ (μ i).real {ω | ε ≤ ‖Y i ω - X i ω‖}) l (𝓝 0))
    (hY : ∀ i, AEMeasurable (Y i) (μ i)) :
    TendstoInDistribution Y l Z μ μ' :=
  tendstoInDistribution_of_varying_approximants hXZ.aemeasurable_limit hY
    (fun ε hε ↦ ⟨X, hXZ, hXY ε hε⟩)


section BernoulliLimit

variable (s : (i : ι) → Set (Ω i)) (κ : ℝ) (p : unitInterval)

/-- Convergence of survival probabilities gives convergence of the scaled
survival indicators to the corresponding two-point law. -/
theorem tendstoInDistribution_indicator
    (hs : ∀ i, MeasurableSet (s i))
    (hp : Tendsto (fun i ↦ (μ i).real (s i)) l (𝓝 (p : ℝ))) :
    TendstoInDistribution (fun i ↦ (s i).indicator (fun _ ↦ κ)) l
      id μ (bernoulliMeasure κ 0 p) := by
  apply (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (fun i ↦ (measurable_const.indicator (hs i)).aemeasurable)
    measurable_id.aemeasurable).mpr
  intro f
  have hi (i) : ∫ ω, f ((s i).indicator (fun _ ↦ κ) ω) ∂μ i =
      (μ i).real (s i) * f κ + (1 - (μ i).real (s i)) * f 0 := by
    have h := hasLaw_indicator_bernoulliMeasure (P := μ i) κ (hs i).nullMeasurableSet
    rw [← Function.comp_def, h.integral_comp (by fun_prop), integral_bernoulliMeasure]
    rfl
  simp_rw [hi]
  simpa only [id_eq, integral_bernoulliMeasure, smul_eq_mul] using
    (hp.mul_const (f κ)).add ((tendsto_const_nhds.sub hp).mul_const (f 0))

/-- The probabilistic reduction at the start of the proof of `thm:main`.
The survival and extinction error estimates remain explicit hypotheses. -/
theorem tendstoInDistribution_of_survival_estimates
    [l.IsCountablyGenerated]
    {H : (i : ι) → Ω i → ℝ}
    (hH : ∀ i, AEMeasurable (H i) (μ i))
    (hs : ∀ i, MeasurableSet (s i))
    (hp : Tendsto (fun i ↦ (μ i).real (s i)) l (𝓝 (p : ℝ)))
    (hSurvival : ∀ ε > (0 : ℝ), Tendsto
      (fun i ↦ (μ i).real {ω | ω ∈ s i ∧ ε ≤ |H i ω - κ|}) l (𝓝 0))
    (hExtinction : ∀ ε > (0 : ℝ), Tendsto
      (fun i ↦ (μ i).real {ω | ω ∉ s i ∧ ε ≤ |H i ω|}) l (𝓝 0)) :
    TendstoInDistribution H l id μ (bernoulliMeasure κ 0 p) := by
  classical
  apply tendstoInDistribution_of_varying_error
    (tendstoInDistribution_indicator s κ p hs hp) _ hH
  intro ε hε
  have hbound (i) :
      (μ i).real {ω | ε ≤ ‖H i ω - (s i).indicator (fun _ ↦ κ) ω‖} ≤
        (μ i).real {ω | ω ∈ s i ∧ ε ≤ |H i ω - κ|} +
        (μ i).real {ω | ω ∉ s i ∧ ε ≤ |H i ω|} := by
    apply (measureReal_mono (μ := μ i) (s₂ :=
      {ω | ω ∈ s i ∧ ε ≤ |H i ω - κ|} ∪
      {ω | ω ∉ s i ∧ ε ≤ |H i ω|}) ?_).trans
      (measureReal_union_le _ _)
    intro ω hω
    by_cases hmem : ω ∈ s i
    · exact Or.inl ⟨hmem, by simpa [Set.indicator_of_mem hmem] using hω⟩
    · exact Or.inr ⟨hmem, by simpa [Set.indicator_of_notMem hmem] using hω⟩
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) hbound
  simpa using (hSurvival ε hε).add (hExtinction ε hε)

/-- The cutoff in the paper can depend on the error tolerance. This version
keeps that quantifier order, rather than requiring one cutoff to work at every
scale. The three epidemic estimates are still explicit proof obligations. -/
theorem tendstoInDistribution_of_survival_estimates_at_each_scale
    [l.IsCountablyGenerated]
    {H : (i : ι) → Ω i → ℝ}
    (hH : ∀ i, AEMeasurable (H i) (μ i))
    (happrox : ∀ ε > (0 : ℝ), ∃ s : (i : ι) → Set (Ω i),
      (∀ i, MeasurableSet (s i)) ∧
      Tendsto (fun i ↦ (μ i).real (s i)) l (𝓝 (p : ℝ)) ∧
      Tendsto (fun i ↦ (μ i).real {ω | ω ∈ s i ∧ ε ≤ |H i ω - κ|}) l (𝓝 0) ∧
      Tendsto (fun i ↦ (μ i).real {ω | ω ∉ s i ∧ ε ≤ |H i ω|}) l (𝓝 0)) :
    TendstoInDistribution H l id μ (bernoulliMeasure κ 0 p) := by
  classical
  apply tendstoInDistribution_of_varying_approximants measurable_id.aemeasurable hH
  intro ε hε
  obtain ⟨s, hs, hp, hSurvival, hExtinction⟩ := happrox ε hε
  refine ⟨fun i ↦ (s i).indicator (fun _ ↦ κ),
    tendstoInDistribution_indicator s κ p hs hp, ?_⟩
  have hbound (i) :
      (μ i).real {ω | ε ≤ ‖H i ω - (s i).indicator (fun _ ↦ κ) ω‖} ≤
        (μ i).real {ω | ω ∈ s i ∧ ε ≤ |H i ω - κ|} +
        (μ i).real {ω | ω ∉ s i ∧ ε ≤ |H i ω|} := by
    apply (measureReal_mono (μ := μ i) (s₂ :=
      {ω | ω ∈ s i ∧ ε ≤ |H i ω - κ|} ∪
      {ω | ω ∉ s i ∧ ε ≤ |H i ω|}) ?_).trans
      (measureReal_union_le _ _)
    intro ω hω
    by_cases hmem : ω ∈ s i
    · exact Or.inl ⟨hmem, by simpa [Set.indicator_of_mem hmem] using hω⟩
    · exact Or.inr ⟨hmem, by simpa [Set.indicator_of_notMem hmem] using hω⟩
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) hbound
  simpa using hSurvival.add hExtinction

end BernoulliLimit

end HeightPaper
