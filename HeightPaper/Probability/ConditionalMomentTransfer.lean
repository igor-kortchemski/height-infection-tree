module

public import HeightPaper.Probability.ConditionalProductBound
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Truncation estimate for conditional profile moments

A higher moment and a small tail probability control a lower moment.  This
elementary estimate is the quantitative uniform-integrability step needed to
pass from joint convergence in probability to conditional moment convergence.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace HeightPaper.CountCoupling

/-- A strict gap between moment orders permits a common truncation scale.
The higher-moment constant is chosen before these parameters. -/
theorem exists_conditional_moment_truncation
    {p q C ε : ℝ} (hp : 0 < p) (hpq : p < q)
    (hε : 0 < ε) :
    ∃ a R δ : ℝ, 0 < a ∧ a ≤ R ∧ 0 < δ ∧
      a ^ p + R ^ p * δ + R ^ (p - q) * C ≤ ε := by
  have hsmall : Tendsto (fun R : ℝ ↦ (R⁻¹) ^ p) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.rpow_const_nhds_zero hp
  have hlarge : Tendsto (fun R : ℝ ↦ R ^ (p - q) * C) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (show 0 < q - p by linarith)).mul_const C
    simpa only [neg_sub, zero_mul] using hh
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨R, hR1, hs, hl⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and
      ((hsmall.eventually (Iio_mem_nhds hthird)).and
        (hlarge.eventually (Iio_mem_nhds hthird)))).exists
  let a : ℝ := R⁻¹
  have hR : 0 < R := by linarith
  have ha : 0 < a := inv_pos.mpr hR
  have haR : a ≤ R := by
    calc
      a ≤ 1 := (inv_le_one₀ hR).mpr hR1
      _ ≤ R := hR1
  let δ : ℝ := ε / (3 * R ^ p)
  have hpow : 0 < R ^ p := Real.rpow_pos_of_pos hR _
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨a, R, δ, ha, haR, hδ, ?_⟩
  have hmiddle : R ^ p * δ = ε / 3 := by
    dsimp [δ]
    field_simp
  rw [hmiddle]
  linarith

/-- Pointwise three-range truncation: below `a`, between `a` and `R`, and
above `R`. -/
theorem rpow_le_small_add_tail_add_high (x a R p q : ℝ)
    (hx : 0 ≤ x) (ha : 0 < a) (haR : a ≤ R)
    (hp : 0 ≤ p) (hpq : p < q) :
    x ^ p ≤ a ^ p + R ^ p * (if a < x then 1 else 0) + R ^ (p - q) * x ^ q := by
  have hR : 0 < R := ha.trans_le haR
  by_cases hax : a < x
  · simp only [ite_eq_left hax, mul_one]
    by_cases hxR : x ≤ R
    · have hpow := Real.rpow_le_rpow hx hxR hp
      nlinarith [Real.rpow_nonneg ha.le p,
        mul_nonneg (Real.rpow_nonneg hR.le (p - q)) (Real.rpow_nonneg hx q)]
    · have hRx : R ≤ x := le_of_not_ge hxR
      have hx0 : 0 < x := hR.trans_le hRx
      have hneg : p - q ≤ 0 := by linarith
      have hpow := Real.rpow_le_rpow_of_nonpos hR hRx hneg
      have hmul : x ^ q * x ^ (p - q) ≤ x ^ q * R ^ (p - q) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx q)
      rw [← Real.rpow_add hx0] at hmul
      have he : q + (p - q) = p := by ring
      rw [he] at hmul
      nlinarith [Real.rpow_nonneg ha.le p, Real.rpow_nonneg hR.le p]
  · simp only [ite_eq_right hax, mul_zero]
    have hxa : x ≤ a := le_of_not_gt hax
    have hpow := Real.rpow_le_rpow hx hxa hp
    nlinarith [mul_nonneg (Real.rpow_nonneg hR.le (p - q))
      (Real.rpow_nonneg hx q)]

/-- The lower moment is bounded by a small-value term, a bounded-tail
probability, and a scaled higher moment. -/
theorem integral_rpow_le_small_add_tail_add_high
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (a R p q : ℝ) (ha : 0 < a) (haR : a ≤ R)
    (hp : 0 ≤ p) (hpq : p < q)
    (hfp : Integrable (fun x ↦ f x ^ p) μ)
    (hfq : Integrable (fun x ↦ f x ^ q) μ) :
    (∫ x, f x ^ p ∂μ) ≤
      a ^ p + R ^ p * μ.real {x | a < f x} +
        R ^ (p - q) * (∫ x, f x ^ q ∂μ) := by
  let E : Set Ω := {x | a < f x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hf
  have hindicator : Integrable (E.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ) : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ).indicator hE
  have hbound : (∫ x, f x ^ p ∂μ) ≤
      ∫ x, a ^ p + R ^ p * E.indicator (fun _ ↦ (1 : ℝ)) x +
        R ^ (p - q) * f x ^ q ∂μ := by
    apply integral_mono hfp
    · exact ((integrable_const (a ^ p) : Integrable (fun _ : Ω ↦ a ^ p) μ).add
        (hindicator.const_mul _)).add (hfq.const_mul _)
    intro x
    simpa only [E, indicator_apply, mem_ofPred_eq] using
      rpow_le_small_add_tail_add_high (f x) a R p q (hfn x) ha haR hp hpq
  have hmeasure : (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x ∂μ) = μ.real E := by
    rw [integral_indicator hE]
    simp [Measure.real]
  calc
    _ ≤ ∫ x, a ^ p + R ^ p * E.indicator (fun _ ↦ (1 : ℝ)) x +
        R ^ (p - q) * f x ^ q ∂μ := hbound
    _ = _ := by
      let A : Ω → ℝ := fun _ ↦ a ^ p
      let B : Ω → ℝ := fun x ↦ R ^ p * E.indicator (fun _ ↦ (1 : ℝ)) x
      let D : Ω → ℝ := fun x ↦ R ^ (p - q) * f x ^ q
      have hA : Integrable (fun _ : Ω ↦ a ^ p) μ := integrable_const _
      have hB : Integrable (fun x ↦ R ^ p * E.indicator (fun _ ↦ (1 : ℝ)) x) μ :=
        hindicator.const_mul _
      have hD : Integrable (fun x ↦ R ^ (p - q) * f x ^ q) μ := hfq.const_mul _
      change (∫ x, (A + B + D) x ∂μ) = _
      simp only [Pi.add_apply]
      have hsplit₁ : (∫ x, A x + B x + D x ∂μ) =
          (∫ x, A x + B x ∂μ) + ∫ x, D x ∂μ := by
        simpa only [Pi.add_apply] using
          (integral_add (hA.add hB) hD)
      have hsplit₂ : (∫ x, A x + B x ∂μ) =
          (∫ x, A x ∂μ) + ∫ x, B x ∂μ := by
        simpa only [Pi.add_apply] using (integral_add hA hB)
      rw [hsplit₁, hsplit₂]
      dsimp only [A, B, D]
      simp only [integral_const_mul, integral_const, hmeasure, smul_eq_mul]
      simp [E]

/-- A numerical conditional tail and a higher-moment bound give the
corresponding lower-moment bound. -/
theorem integral_rpow_le_of_tail_and_high_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (a R p q C δ : ℝ) (ha : 0 < a) (haR : a ≤ R)
    (hp : 0 ≤ p) (hpq : p < q)
    (hfp : Integrable (fun x ↦ f x ^ p) μ)
    (hfq : Integrable (fun x ↦ f x ^ q) μ)
    (htail : μ.real {x | a < f x} ≤ δ)
    (hhigh : (∫ x, f x ^ q ∂μ) ≤ C) :
    (∫ x, f x ^ p ∂μ) ≤
      a ^ p + R ^ p * δ + R ^ (p - q) * C := by
  have hR : 0 ≤ R := (ha.trans_le haR).le
  have hpowp : 0 ≤ R ^ p := Real.rpow_nonneg hR _
  have hpowdiff : 0 ≤ R ^ (p - q) := Real.rpow_nonneg hR _
  exact (integral_rpow_le_small_add_tail_add_high μ f hf hfn a R p q ha haR hp hpq
    hfp hfq).trans (by gcongr)

end HeightPaper.CountCoupling

namespace MeasureTheory.Measure

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

/-- The average conditional probability of a measurable product event is
its joint probability. -/
theorem integral_real_section_eq_prod_real (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set (Ω × Ξ)} (hE : MeasurableSet E) :
    (∫ u, ν.real (Prod.mk u ⁻¹' E) ∂μ) = (μ.prod ν).real E := by
  have hfun : Integrable (E.indicator (fun _ ↦ (1 : ℝ))) (μ.prod ν) :=
    (integrable_const (1 : ℝ)).indicator hE
  calc
    _ = ∫ u, ∫ v, E.indicator (fun _ ↦ (1 : ℝ)) (u, v) ∂ν ∂μ := by
      congr 1
      funext u
      have hu : MeasurableSet (Prod.mk u ⁻¹' E) := measurable_prodMk_left hE
      calc
        _ = ∫ v in Prod.mk u ⁻¹' E, (1 : ℝ) ∂ν := by simp [Measure.real]
        _ = ∫ v, (Prod.mk u ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) v ∂ν :=
          (integral_indicator hu).symm
        _ = _ := by
          congr 1
    _ = ∫ q, E.indicator (fun _ ↦ (1 : ℝ)) q ∂(μ.prod ν) :=
      (integral_prod _ hfun).symm
    _ = (μ.prod ν).real E := by
      rw [integral_indicator hE]
      simp [Measure.real]

/-- Conditional probabilities above a threshold are rare when the joint
event has small probability. -/
theorem real_conditional_tail_le_joint_div (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set (Ω × Ξ)} (hE : MeasurableSet E)
    {δ : ℝ} (hδ : 0 < δ) :
    μ.real {u | δ ≤ ν.real (Prod.mk u ⁻¹' E)} ≤
      (μ.prod ν).real E / δ := by
  let f : Ω → ℝ := fun u ↦ ν.real (Prod.mk u ⁻¹' E)
  have hf : Measurable f := (measurable_measure_prodMk_left hE).ennreal_toReal
  have hfn : ∀ u, 0 ≤ f u := fun u ↦ measureReal_nonneg
  have hfb : ∀ u, f u ≤ 1 := by
    intro u
    exact (measureReal_mono (Set.subset_univ _)).trans_eq (by simp)
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ fun u ↦ by simp only [Real.norm_eq_abs, abs_of_nonneg (hfn u)]; exact hfb u)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ hfn) hfi δ
  have htotal := integral_real_section_eq_prod_real μ ν hE
  dsimp [f] at hmarkov
  rw [htotal] at hmarkov
  exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hmarkov)

end MeasureTheory.Measure

namespace HeightPaper.CountCoupling

/-- Quantitative transfer from a joint tail event to a lower conditional
moment, outside an exceptional set of outer samples. -/
theorem conditional_lower_moment_bad_le_joint_tail
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × Ξ → ℝ) (hF : Measurable F) (hFn : ∀ q, 0 ≤ F q)
    (S B : Set Ω)
    (a R p q C δ ε : ℝ) (ha : 0 < a) (haR : a ≤ R)
    (hp : 0 ≤ p) (hpq : p < q) (hδ : 0 < δ)
    (hnum : a ^ p + R ^ p * δ + R ^ (p - q) * C ≤ ε)
    (hfp : ∀ u, Integrable (fun v ↦ F (u, v) ^ p) ν)
    (hfq : ∀ u, Integrable (fun v ↦ F (u, v) ^ q) ν)
    (hhigh : ∀ u ∈ S, u ∉ B → (∫ v, F (u, v) ^ q ∂ν) ≤ C) :
    μ.real {u | u ∈ S ∧ ε < ∫ v, F (u, v) ^ p ∂ν} ≤
      μ.real B + (μ.prod ν).real {w | a < F w} / δ := by
  let E : Set (Ω × Ξ) := {w | a < F w}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hF
  let D : Set Ω := {u | δ ≤ ν.real (Prod.mk u ⁻¹' E)}
  have hD : MeasurableSet D :=
    measurableSet_le measurable_const (measurable_measure_prodMk_left hE).ennreal_toReal
  have hsub : {u | u ∈ S ∧ ε < ∫ v, F (u, v) ^ p ∂ν} ⊆ B ∪ D := by
    intro u hu
    by_contra hnot
    have huB : u ∉ B := fun h ↦ hnot (Or.inl h)
    have huD : u ∉ D := fun h ↦ hnot (Or.inr h)
    have htail : ν.real {v | a < F (u, v)} ≤ δ := by
      have hh : ν.real (Prod.mk u ⁻¹' E) < δ := lt_of_not_ge huD
      change ν.real {v | a < F (u, v)} < δ at hh
      exact hh.le
    have hFu : Measurable (fun v ↦ F (u, v)) :=
      hF.comp (measurable_const.prodMk measurable_id)
    have hlow := integral_rpow_le_of_tail_and_high_moment ν
      (fun v ↦ F (u, v)) hFu (fun v ↦ hFn (u, v))
      a R p q C δ ha haR hp hpq (hfp u) (hfq u) htail
      (hhigh u hu.1 huB)
    exact not_lt_of_ge (hlow.trans hnum) hu.2
  calc
    _ ≤ μ.real (B ∪ D) := measureReal_mono hsub
    _ ≤ μ.real B + μ.real D := measureReal_union_le _ _
    _ ≤ μ.real B + (μ.prod ν).real E / δ :=
      by
        have hh := Measure.real_conditional_tail_le_joint_div μ ν hE hδ
        change μ.real D ≤ (μ.prod ν).real E / δ at hh
        simpa only [add_comm] using add_le_add_right hh (μ.real B)
    _ = _ := rfl

/-- The conditional higher moment and integrability are needed only almost
everywhere on the good outer event. This form is suited to local profile
limits, whose moment control is obtained outside rare count words. -/
theorem conditional_lower_moment_bad_le_joint_tail_ae
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × Ξ → ℝ) (hF : Measurable F) (hFn : ∀ q, 0 ≤ F q)
    (S B : Set Ω) (hS : MeasurableSet S)
    (a R p q C δ ε : ℝ) (ha : 0 < a) (haR : a ≤ R)
    (hp : 0 ≤ p) (hpq : p < q) (hδ : 0 < δ)
    (hnum : a ^ p + R ^ p * δ + R ^ (p - q) * C ≤ ε)
    (hgood : ∀ᵐ u ∂μ, u ∈ S → u ∉ B →
      Integrable (fun v ↦ F (u, v) ^ p) ν ∧
      Integrable (fun v ↦ F (u, v) ^ q) ν ∧
      (∫ v, F (u, v) ^ q ∂ν) ≤ C) :
    μ.real {u | u ∈ S ∧ ε < ∫ v, F (u, v) ^ p ∂ν} ≤
      μ.real B + (μ.prod ν).real {w | w.1 ∈ S ∧ a < F w} / δ := by
  let E : Set (Ω × Ξ) := {w | w.1 ∈ S ∧ a < F w}
  have hE : MeasurableSet E :=
    (hS.preimage measurable_fst).inter (measurableSet_lt measurable_const hF)
  let D : Set Ω := {u | δ ≤ ν.real (Prod.mk u ⁻¹' E)}
  have hsub : ∀ᵐ u ∂μ,
      u ∈ {u | u ∈ S ∧ ε < ∫ v, F (u, v) ^ p ∂ν} → u ∈ B ∪ D := by
    filter_upwards [hgood] with u hu hbad
    by_contra hnot
    have huB : u ∉ B := fun h ↦ hnot (Or.inl h)
    have huD : u ∉ D := fun h ↦ hnot (Or.inr h)
    have htail : ν.real {v | a < F (u, v)} ≤ δ := by
      have hh : ν.real (Prod.mk u ⁻¹' E) < δ := lt_of_not_ge huD
      apply (measureReal_mono (show
        {v | a < F (u, v)} ⊆ Prod.mk u ⁻¹' E from ?_)).trans hh.le
      intro v hv
      exact ⟨hbad.1, hv⟩
    have hFu : Measurable (fun v ↦ F (u, v)) :=
      hF.comp (measurable_const.prodMk measurable_id)
    obtain ⟨hfp, hfq, hhigh⟩ := hu hbad.1 huB
    have hlow := integral_rpow_le_of_tail_and_high_moment ν
      (fun v ↦ F (u, v)) hFu (fun v ↦ hFn (u, v))
      a R p q C δ ha haR hp hpq hfp hfq htail hhigh
    exact not_lt_of_ge (hlow.trans hnum) hbad.2
  have hm := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  calc
    _ ≤ μ.real (B ∪ D) := hm
    _ ≤ μ.real B + μ.real D := measureReal_union_le _ _
    _ ≤ μ.real B + (μ.prod ν).real E / δ := by
      have hh := Measure.real_conditional_tail_le_joint_div μ ν hE hδ
      change μ.real D ≤ (μ.prod ν).real E / δ at hh
      simpa only [add_comm] using add_le_add_right hh (μ.real B)
    _ = _ := rfl

/-- Uniform version over an arbitrary index set.  Measurability is required
only for the simultaneous joint tail event; the index set may be uncountable. -/
theorem conditional_lower_moment_exists_bad_le_joint_tail
    {Ω Ξ Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Z → Ω × Ξ → ℝ) (K : Set Z)
    (hFn : ∀ z ∈ K, ∀ r, 0 ≤ F z r)
    (S B : Set Ω)
    (a R p q C δ ε : ℝ) (ha : 0 < a) (haR : a ≤ R)
    (hp : 0 ≤ p) (hpq : p < q) (hδ : 0 < δ)
    (hnum : a ^ p + R ^ p * δ + R ^ (p - q) * C ≤ ε)
    (hE : MeasurableSet {r | r.1 ∈ S ∧ ∃ z ∈ K, a < F z r})
    (hFmeas : ∀ z ∈ K, ∀ u, Measurable (fun v ↦ F z (u, v)))
    (hfp : ∀ z ∈ K, ∀ u, Integrable (fun v ↦ F z (u, v) ^ p) ν)
    (hfq : ∀ z ∈ K, ∀ u, Integrable (fun v ↦ F z (u, v) ^ q) ν)
    (hhigh : ∀ z ∈ K, ∀ u ∈ S, u ∉ B →
      (∫ v, F z (u, v) ^ q ∂ν) ≤ C) :
    μ.real {u | u ∈ S ∧ ∃ z ∈ K, ε < ∫ v, F z (u, v) ^ p ∂ν} ≤
      μ.real B + (μ.prod ν).real {r | r.1 ∈ S ∧
        ∃ z ∈ K, a < F z r} / δ := by
  let E : Set (Ω × Ξ) := {r | r.1 ∈ S ∧ ∃ z ∈ K, a < F z r}
  let D : Set Ω := {u | δ ≤ ν.real (Prod.mk u ⁻¹' E)}
  have hsub : {u | u ∈ S ∧ ∃ z ∈ K, ε < ∫ v, F z (u, v) ^ p ∂ν} ⊆
      B ∪ D := by
    intro u hu
    by_contra hnot
    have huB : u ∉ B := fun h ↦ hnot (Or.inl h)
    have huD : u ∉ D := fun h ↦ hnot (Or.inr h)
    obtain ⟨z, hz, hbad⟩ := hu.2
    have htail : ν.real {v | a < F z (u, v)} ≤ δ := by
      have hsubz : {v | a < F z (u, v)} ⊆ Prod.mk u ⁻¹' E := by
        intro v hv
        exact ⟨hu.1, z, hz, hv⟩
      exact (measureReal_mono hsubz).trans (lt_of_not_ge huD).le
    have hlow := integral_rpow_le_of_tail_and_high_moment ν
      (fun v ↦ F z (u, v)) (hFmeas z hz u) (fun v ↦ hFn z hz (u, v))
      a R p q C δ ha haR hp hpq (hfp z hz u) (hfq z hz u) htail
      (hhigh z hz u hu.1 huB)
    exact not_lt_of_ge (hlow.trans hnum) hbad
  calc
    _ ≤ μ.real (B ∪ D) := measureReal_mono hsub
    _ ≤ μ.real B + μ.real D := measureReal_union_le _ _
    _ ≤ μ.real B + (μ.prod ν).real E / δ := by
      have hh := Measure.real_conditional_tail_le_joint_div μ ν hE hδ
      change μ.real D ≤ (μ.prod ν).real E / δ at hh
      simpa only [add_comm] using add_le_add_right hh (μ.real B)
    _ = _ := rfl

end HeightPaper.CountCoupling
