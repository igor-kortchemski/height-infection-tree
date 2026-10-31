module

public import HeightPaper.Analysis.Parameters
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.PSeries

/-!
# Summable profile moment exponents

The derivative at moment order one is minus the profile exponent. Its strict
positivity below the profile edge supplies a moment order in `(1,2)` with a
summable decay exponent, as in `eq asymptotique p tend vers un`.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace HeightPaper

noncomputable def profileMomentExponent (l x p : ℝ) : ℝ :=
  -p + growthFactor l * (Real.exp (p * x) - 1 - p * (Real.exp x - 1))

@[simp] theorem profileMomentExponent_one (l x : ℝ) : profileMomentExponent l x 1 = -1 := by
  simp [profileMomentExponent]

theorem hasDerivAt_profileMomentExponent (l x p : ℝ) :
    HasDerivAt (profileMomentExponent l x)
      (-1 + growthFactor l * (x * Real.exp (p * x) - (Real.exp x - 1))) p := by
  have he := (((hasDerivAt_id p).mul_const x).exp).sub_const 1
  have hm := (hasDerivAt_id p).mul_const (Real.exp x - 1)
  have h := (hasDerivAt_id p).neg.add ((he.sub hm).const_mul (growthFactor l))
  convert h using 1 <;> first | rfl | (simp only [id_eq, one_mul]; ring)

theorem hasDerivAt_profileMomentExponent_one (l x : ℝ) :
    HasDerivAt (profileMomentExponent l x) (-profileExponent l x) 1 := by
  convert hasDerivAt_profileMomentExponent l x 1 using 1
  simp only [profileExponent, one_mul]
  ring

/-- Strict negativity is obtained from the derivative, without taking an
unproved asymptotic expansion as an input. -/
theorem exists_profileMomentExponent_lt_neg_one {l x : ℝ} (hl : 1 < l)
    (hx : 0 ≤ x) (hxr : x < profileRoot l) :
    ∃ p ∈ Ioo (1 : ℝ) 2, profileMomentExponent l x p < -1 := by
  have hf := profileExponent_pos hl hx hxr
  have hd := (hasDerivAt_profileMomentExponent_one l x).hasDerivWithinAt
    (s := Ioi (1 : ℝ))
  have hneg := hd.limsup_slope_le' (by simp) (show -profileExponent l x < 0 by linarith)
  have htwo : ∀ᶠ p : ℝ in 𝓝[>] (1 : ℝ), p < 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hone : ∀ᶠ p : ℝ in 𝓝[>] (1 : ℝ), 1 < p := self_mem_nhdsWithin
  obtain ⟨p, hp, hp2, hs⟩ := (hone.and (htwo.and hneg)).exists
  refine ⟨p, ⟨hp, hp2⟩, ?_⟩
  rw [slope_def_field, profileMomentExponent_one] at hs
  have hh := (div_lt_iff₀ (show 0 < p - 1 by linarith)).mp hs
  linarith

/-- The polynomial increment bound is summable for some moment order. -/
theorem exists_summable_profileMomentExponent {l x : ℝ} (hl : 1 < l)
    (hx : 0 ≤ x) (hxr : x < profileRoot l) :
    ∃ p ∈ Ioo (1 : ℝ) 2, Summable (fun k : ℕ ↦ (k : ℝ) ^ profileMomentExponent l x p) := by
  obtain ⟨p, hp, he⟩ := exists_profileMomentExponent_lt_neg_one hl hx hxr
  exact ⟨p, hp, Real.summable_nat_rpow.mpr he⟩

end HeightPaper
