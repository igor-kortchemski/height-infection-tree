module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Rate scaling and the Bernoulli mixture in the main theorem

These declarations preserve arbitrary sequences of nonnegative infection rates;
they do not replace the hypothesis by the special case `rate n = l / n`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology Asymptotics

namespace HeightPaper

/-- The survival parameter `1 - 1/l`, valid for the supercritical regime. -/
noncomputable def survivalParameter (l : ℝ) (hl : 1 < l) : unitInterval :=
  ⟨1 - 1 / l, by
    have hlpos : 0 < l := lt_trans zero_lt_one hl
    constructor
    · have : 1 / l < 1 := (div_lt_one hlpos).mpr hl
      linarith
    · have : 0 ≤ 1 / l := div_nonneg zero_le_one hlpos.le
      linarith⟩

@[simp] theorem coe_survivalParameter (l : ℝ) (hl : 1 < l) :
    (survivalParameter l hl : ℝ) = 1 - 1 / l := rfl

/-- The limiting law with mass `1/l` at zero and mass `1 - 1/l` at `κ`. -/
noncomputable def heightLimitLaw (l : ℝ) (hl : 1 < l) (κ : ℝ) : ProbabilityMeasure ℝ :=
  ⟨bernoulliMeasure κ 0 (survivalParameter l hl), inferInstance⟩

/-- This is exactly the law of `κ` times a Bernoulli variable with the stated
survival probability, rather than a deterministic limit conditional on survival. -/
theorem heightLimitLaw_eq_scaledBernoulli (l : ℝ) (hl : 1 < l) (κ : ℝ) :
    (heightLimitLaw l hl κ : Measure ℝ) =
      (bernoulliMeasure (1 : ℝ) 0 (survivalParameter l hl)).map (fun x ↦ κ * x) := by
  simp [heightLimitLaw, map_bernoulliMeasure]

@[simp] theorem heightLimitLaw_mass_zero {l κ : ℝ} (hl : 1 < l) (hκ : κ ≠ 0) :
    (heightLimitLaw l hl κ : Measure ℝ).real {0} = 1 / l := by
  simpa [heightLimitLaw, survivalParameter] using
    bernoulliMeasure_real_apply_of_notMem_of_mem (x := κ) (y := (0 : ℝ))
      (survivalParameter l hl) (measurableSet_singleton 0)
      (by simpa using hκ) (by simp)

@[simp] theorem heightLimitLaw_mass_coefficient {l κ : ℝ} (hl : 1 < l) (hκ : κ ≠ 0) :
    (heightLimitLaw l hl κ : Measure ℝ).real {κ} = 1 - 1 / l := by
  simpa [heightLimitLaw, survivalParameter] using
    bernoulliMeasure_real_apply_of_mem_of_notMem (x := κ) (y := (0 : ℝ))
      (survivalParameter l hl) (measurableSet_singleton κ)
      (by simp) (by simpa using hκ.symm)

/-- The source hypothesis `rate n ∼ l/n` is equivalent to the scaling used by
our formal statement. The finitely many zero denominators do not affect the limit. -/
theorem rate_asymptotic_iff_scaled_tendsto {rate : ℕ → ℝ} {l : ℝ} (hl : l ≠ 0) :
    rate ~[atTop] (fun n : ℕ ↦ l / n) ↔
      Tendsto (fun n : ℕ ↦ (n : ℝ) * rate n) atTop (𝓝 l) := by
  have hnonzero : ∀ᶠ n : ℕ in atTop, l / (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_ne_zero hl (by exact_mod_cast (by omega : n ≠ 0))
  rw [Asymptotics.isEquivalent_iff_tendsto_one hnonzero]
  have hquot : (rate / fun n : ℕ ↦ l / n) =
      (fun n : ℕ ↦ ((n : ℝ) * rate n) / l) := by
    funext n
    simp only [Pi.div_apply, div_eq_mul_inv]
    simp [mul_comm, mul_left_comm]
  rw [hquot]
  constructor
  · intro h
    have hm := h.mul_const l
    simpa [hl] using hm
  · intro h
    simpa [hl] using h.div_const l

end HeightPaper
