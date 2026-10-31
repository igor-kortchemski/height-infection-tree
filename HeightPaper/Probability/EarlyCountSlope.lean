module

public import HeightPaper.Probability.EarlyExtinctionTail
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Sharp linear slopes in early-count geometric estimates -/

@[expose] public section

open Filter Set
open scoped Topology

namespace HeightPaper.Model

/-- The derivative at one of the geometric moment multiplier is exactly the
embedded epidemic's active-count drift at the specified pressure. -/
theorem geometricContraction_hasDerivAt_one {R : ℝ} (hR : 0 ≤ R) :
    HasDerivAt (geometricContraction R) ((R - 1) / (R + 1)) 1 := by
  have hd : 1 + R ≠ 0 := by positivity
  have hnum : HasDerivAt (fun q : ℝ ↦ R * q ^ 2 + 1) (2 * R) 1 := by
    simpa [id_eq, mul_comm] using (((hasDerivAt_id (1 : ℝ)).fun_pow 2).const_mul R).add_const 1
  have hden : HasDerivAt (fun q : ℝ ↦ q * (1 + R)) (1 + R) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (1 + R)
  convert hnum.div hden (by simpa using hd) using 1
  · rfl
  · field_simp
    ring

/-- Every slope below the limiting drift is admitted by a geometric lower-tail
estimate, by choosing the geometric parameter sufficiently close to one. -/
theorem exists_lower_count_parameter {R c : ℝ} (hR : 0 ≤ R)
    (hc : c < (R - 1) / (R + 1)) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ geometricContraction R q < q ^ c := by
  let f : ℝ → ℝ := fun q ↦ q ^ c - geometricContraction R q
  have hd : HasDerivAt f (c - (R - 1) / (R + 1)) 1 := by
    convert (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := c) (Or.inl one_ne_zero)).sub
      (geometricContraction_hasDerivAt_one hR) using 1
    simp
  have hf1 : f 1 = 0 := by
    have hh : (R + 1 : ℝ) ≠ 0 := by positivity
    simp [f, geometricContraction, add_comm, hh]
  have hneg : ∀ᶠ q in 𝓝[<] (1 : ℝ), slope f 1 q < 0 :=
    (hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE 1)).eventually
      (Iio_mem_nhds (sub_neg.mpr hc))
  have he : ∀ᶠ q in 𝓝[<] (1 : ℝ), 0 < q ∧ q < 1 ∧ geometricContraction R q < q ^ c := by
    filter_upwards [hneg, self_mem_nhdsWithin,
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with q hs hq1 hq
    refine ⟨hq, hq1, ?_⟩
    rw [slope_def_field, hf1, sub_zero] at hs
    have hfq := (div_lt_iff_of_neg (sub_neg.mpr hq1)).mp hs
    exact sub_pos.mp (by simpa only [zero_mul, f] using hfq)
  exact he.exists

/-- Every slope above the limiting drift is admitted by the corresponding
upper-tail geometric estimate with parameter greater than one. -/
theorem exists_upper_count_parameter {R c : ℝ} (hR : 0 ≤ R)
    (hc : (R - 1) / (R + 1) < c) :
    ∃ q : ℝ, 1 < q ∧ geometricContraction R q < q ^ c := by
  let f : ℝ → ℝ := fun q ↦ q ^ c - geometricContraction R q
  have hd : HasDerivAt f (c - (R - 1) / (R + 1)) 1 := by
    convert (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := c) (Or.inl one_ne_zero)).sub
      (geometricContraction_hasDerivAt_one hR) using 1
    simp
  have hf1 : f 1 = 0 := by
    have hh : (R + 1 : ℝ) ≠ 0 := by positivity
    simp [f, geometricContraction, add_comm, hh]
  have hpos : ∀ᶠ q in 𝓝[>] (1 : ℝ), 0 < slope f 1 q :=
    (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 1)).eventually
      (Ioi_mem_nhds (sub_pos.mpr hc))
  have he : ∀ᶠ q in 𝓝[>] (1 : ℝ), 1 < q ∧ geometricContraction R q < q ^ c := by
    filter_upwards [hpos, self_mem_nhdsWithin] with q hs hq1
    refine ⟨hq1, ?_⟩
    rw [slope_def_field, hf1, sub_zero] at hs
    have hfq := (lt_div_iff₀ (sub_pos.mpr hq1)).mp hs
    exact sub_pos.mp (by simpa only [zero_mul, f] using hfq)
  exact he.exists

end HeightPaper.Model
