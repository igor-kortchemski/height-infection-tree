module

public import HeightPaper.Probability.AnalyticBoundarySeries
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
public import Mathlib.Analysis.Complex.Basic

/-!
# Measurable compact zero events from uniform limits

The infimum is in the extended nonnegative reals, so the empty-set value is
infinity. Uniform convergence to a continuous function identifies convergence
of the infimum to zero with the presence of a zero on a compact parameter set.
Finite positive multiplicative comparisons preserve this convergence event.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace HeightPaper

noncomputable def normInfOn {X : Type*} (K : Set X) (f : X → ℂ) : ℝ≥0∞ :=
  ⨅ z : K, ENNReal.ofReal ‖f z‖

theorem normInfOn_le {X : Type*} (K : Set X) (f : X → ℂ) {z : X} (hz : z ∈ K) :
    normInfOn K f ≤ ENNReal.ofReal ‖f z‖ := by
  unfold normInfOn
  exact iInf_le (fun t : K ↦ ENNReal.ofReal ‖f t.val‖) ⟨z, hz⟩

/-- Uncountably many tilts are allowed inside the infimum. -/
theorem measurable_normInfOn {Ω X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [SecondCountableTopology X] (K : Set X) (f : Ω → X → ℂ)
    (hf : ∀ z ∈ K, Measurable (fun ω ↦ f ω z))
    (hc : ∀ ω, ContinuousOn (f ω) K) : Measurable (fun ω ↦ normInfOn K (f ω)) := by
  have h := measurable_iInf_of_upperSemicontinuous
    (fun z : K ↦ (hf z z.property).norm.ennreal_ofReal)
    (fun ω ↦ (ENNReal.continuous_ofReal.comp
      ((continuousOn_iff_continuous_domRestrict.mp (hc ω)).norm)).upperSemicontinuous)
  convert h using 1
  funext ω
  simp only [normInfOn, iInf_apply]

theorem measurableSet_tendsto_normInfOn_zero {Ω X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [SecondCountableTopology X] (K : Set X) (f : ℕ → Ω → X → ℂ)
    (hf : ∀ k z, z ∈ K → Measurable (fun ω ↦ f k ω z))
    (hc : ∀ k ω, ContinuousOn (f k ω) K) :
    MeasurableSet {ω | Tendsto (fun k ↦ normInfOn K (f k ω)) atTop (𝓝 0)} :=
  measurableSet_tendsto _ (fun k ↦ measurable_normInfOn K (f k) (hf k) (hc k))

theorem exists_zero_iff_tendsto_normInfOn_zero {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {F : ℕ → X → ℂ} {f : X → ℂ}
    (hf : ContinuousOn f K) (hconv : TendstoUniformlyOn F f atTop K) :
    (∃ z ∈ K, f z = 0) ↔ Tendsto (fun k ↦ normInfOn K (F k)) atTop (𝓝 0) := by
  constructor
  · rintro ⟨z, hz, hzero⟩
    have ht := ENNReal.tendsto_ofReal (hconv.tendsto_at hz).norm
    simp only [hzero, norm_zero, ENNReal.ofReal_zero] at ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ ↦ bot_le) (fun k ↦ normInfOn_le K (F k) hz)
  · intro ht
    by_contra hnone
    have hpos : ∀ z ∈ K, 0 < ‖f z‖ := by
      intro z hz
      exact norm_pos_iff.mpr (fun he ↦ hnone ⟨z, hz, he⟩)
    obtain ⟨b, hb, hbound⟩ := hK.exists_forall_le' hf.norm hpos
    have hhalf : 0 < b / 2 := half_pos hb
    have hunif := (Metric.tendstoUniformlyOn_iff.mp hconv) (b / 2) hhalf
    have hlower : ∀ᶠ k in atTop, ENNReal.ofReal (b / 2) ≤ normInfOn K (F k) := by
      filter_upwards [hunif] with k hk
      apply le_iInf
      intro z
      apply ENNReal.ofReal_le_ofReal
      have hd := hk z z.property
      rw [dist_eq_norm] at hd
      have hn := norm_sub_norm_le (f z) (F k z)
      have hbz := hbound z z.property
      linarith
    exact (ENNReal.ofReal_pos.mpr hhalf).not_ge (ge_of_tendsto ht hlower)

theorem normInfOn_le_mul {X : Type*} {K : Set X} {f g : X → ℂ} {B : ℝ}
    (hB : 0 < B) (hfg : ∀ z ∈ K, ‖f z‖ ≤ B * ‖g z‖) :
    normInfOn K f ≤ ENNReal.ofReal B * normInfOn K g := by
  unfold normInfOn
  rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hB).ne' ENNReal.ofReal_ne_top]
  apply iInf_mono
  intro z
  rw [← ENNReal.ofReal_mul hB.le]
  exact ENNReal.ofReal_le_ofReal (hfg z z.property)

/-- Multiplicative bounds may hold only after a finite initial segment. -/
theorem tendsto_normInfOn_zero_of_comparison {X : Type*} {K : Set X}
    {F G : ℕ → X → ℂ} {B : ℝ} (hB : 0 < B)
    (hfg : ∀ᶠ k in atTop, ∀ z ∈ K, ‖F k z‖ ≤ B * ‖G k z‖)
    (hg : Tendsto (fun k ↦ normInfOn K (G k)) atTop (𝓝 0)) :
    Tendsto (fun k ↦ normInfOn K (F k)) atTop (𝓝 0) := by
  have ht : Tendsto (fun k ↦ ENNReal.ofReal B * normInfOn K (G k)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).tendsto 0 |>.comp hg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall (fun _ ↦ bot_le))
    (hfg.mono fun _ hk ↦ normInfOn_le_mul hB hk)

end HeightPaper
