module

public import HeightPaper.Model.InfiniteProfile
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Passing a conditional profile moment bound to an almost-sure limit

Fatou's lemma for Lp seminorms keeps the same moment constant when a
profile sequence converges almost surely.  This is the limit step needed
for conditional moments of the canonical local profile.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace HeightPaper.Model

theorem integral_norm_sub_limit_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f : ℕ → Ω → ℂ} {g h : Ω → ℂ} {p C : ℝ}
    (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ m, MemLp (f m - h) (ENNReal.ofReal p) μ)
    (hg : Measurable g) (hh : Measurable h)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun m ↦ f m ω) atTop (𝓝 (g ω)))
    (hbound : ∀ᶠ m in atTop, (∫ ω, ‖f m ω - h ω‖ ^ p ∂μ) ≤ C) :
    Integrable (fun ω ↦ ‖g ω - h ω‖ ^ p) μ ∧
      (∫ ω, ‖g ω - h ω‖ ^ p ∂μ) ≤ C := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp [hp]
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hnorm : eLpNorm (g - h) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (C ^ p⁻¹) := by
    apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun m ↦ f m - h)
    · filter_upwards [hbound] with m hm
      rw [MemLp.eLpNorm_eq_integral_rpow_norm hp0 hptop (hf m),
        ENNReal.toReal_ofReal hp.le]
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
        hm (inv_nonneg.mpr hp.le)
    · exact fun m ↦ (hf m).aestronglyMeasurable
    · exact (hg.sub hh).aestronglyMeasurable
    · filter_upwards [hlim] with ω hω
      exact hω.sub_const (h ω)
  have hmem : MemLp (g - h) (ENNReal.ofReal p) μ :=
    hnorm.trans_lt ENNReal.ofReal_lt_top
  have hint : Integrable (fun ω ↦ ‖g ω - h ω‖ ^ p) μ := by
    simpa only [Pi.sub_apply, ENNReal.toReal_ofReal hp.le] using
      hmem.integrable_norm_rpow hp0 hptop
  refine ⟨hint, ?_⟩
  rw [hmem.eLpNorm_eq_integral_rpow_norm hp0 hptop,
    ENNReal.toReal_ofReal hp.le] at hnorm
  have hpownonneg : 0 ≤ ∫ ω, ‖g ω - h ω‖ ^ p ∂μ :=
    integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hreal := (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hC _)).mp hnorm
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hpownonneg _) hreal hp.le
  rw [← Real.rpow_mul hpownonneg, inv_mul_cancel₀ hp.ne', Real.rpow_one,
    ← Real.rpow_mul hC, inv_mul_cancel₀ hp.ne', Real.rpow_one] at hpow
  exact hpow

end HeightPaper.Model

namespace HeightPaper.Model

/-- Add a bounded finite profile to a controlled limit difference. -/
theorem integral_norm_limit_rpow_le_of_sub_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {g h : Ω → ℂ} {p C B : ℝ} (hp : 1 ≤ p) (_hB : 0 ≤ B)
    (hg : Measurable g)
    (hsub : Integrable (fun ω ↦ ‖g ω - h ω‖ ^ p) μ ∧
      (∫ ω, ‖g ω - h ω‖ ^ p ∂μ) ≤ C)
    (hbound : ∀ᵐ ω ∂μ, ‖h ω‖ ≤ B) :
    Integrable (fun ω ↦ ‖g ω‖ ^ p) μ ∧
      (∫ ω, ‖g ω‖ ^ p ∂μ) ≤
        (2 : ℝ) ^ (p - 1) * (C + B ^ p) := by
  have hpower (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      (a + b) ^ p ≤ (2 : ℝ) ^ (p - 1) * (a ^ p + b ^ p) := by
    lift a to NNReal using ha
    lift b to NNReal using hb
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow a b hp
  have hc : 0 ≤ (2 : ℝ) ^ (p - 1) := Real.rpow_nonneg (by norm_num) _
  have hpoint : ∀ᵐ ω ∂μ,
      ‖g ω‖ ^ p ≤ (2 : ℝ) ^ (p - 1) * (‖g ω - h ω‖ ^ p + B ^ p) := by
    filter_upwards [hbound] with ω hω
    have hnorm : ‖g ω‖ ≤ ‖g ω - h ω‖ + ‖h ω‖ := by
      calc
        ‖g ω‖ = ‖(g ω - h ω) + h ω‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    calc
      ‖g ω‖ ^ p ≤ (‖g ω - h ω‖ + ‖h ω‖) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) hnorm (zero_le_one.trans hp)
      _ ≤ (2 : ℝ) ^ (p - 1) * (‖g ω - h ω‖ ^ p + ‖h ω‖ ^ p) :=
        hpower _ _ (norm_nonneg _) (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ (p - 1) * (‖g ω - h ω‖ ^ p + B ^ p) := by
        gcongr
  have hdom : Integrable
      (fun ω ↦ (2 : ℝ) ^ (p - 1) * (‖g ω - h ω‖ ^ p + B ^ p)) μ :=
    (hsub.1.add (integrable_const _)).const_mul _
  have hint : Integrable (fun ω ↦ ‖g ω‖ ^ p) μ := by
    apply Integrable.mono' hdom
      ((Real.continuous_rpow_const (zero_le_one.trans hp)).measurable.comp
        hg.norm).aestronglyMeasurable
    filter_upwards [hpoint] with ω hω
    simpa only [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (g ω)) p),
      abs_of_nonneg (mul_nonneg hc (add_nonneg
        (Real.rpow_nonneg (norm_nonneg (g ω - h ω)) p)
        (Real.rpow_nonneg _hB p)))] using hω
  refine ⟨hint, ?_⟩
  calc
    (∫ ω, ‖g ω‖ ^ p ∂μ) ≤
      ∫ ω, (2 : ℝ) ^ (p - 1) * (‖g ω - h ω‖ ^ p + B ^ p) ∂μ :=
      integral_mono_ae hint hdom hpoint
    _ = (2 : ℝ) ^ (p - 1) * ((∫ ω, ‖g ω - h ω‖ ^ p ∂μ) + B ^ p) := by
      rw [integral_const_mul, integral_add hsub.1 (integrable_const _)]
      simp
    _ ≤ (2 : ℝ) ^ (p - 1) * (C + B ^ p) :=
      mul_le_mul_of_nonneg_left (by linarith [hsub.2]) hc

end HeightPaper.Model
