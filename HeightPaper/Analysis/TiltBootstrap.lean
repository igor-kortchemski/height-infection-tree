module

public import HeightPaper.Analysis.ProfileMomentExponent

/-!
# Uniform moment margin and losses between real tilts

A single moment order works below any fixed interior profile tilt. The loss
in the deterministic Jensen lower comparison is controlled by the distance
between successive tilts. These facts support a finite bootstrap argument;
the stochastic propagation step is a separate obligation.
-/

public section

open Set

namespace HeightPaper

theorem hasDerivAt_profileMomentExponent_tilt (l p x : ℝ) :
    HasDerivAt (fun y ↦ profileMomentExponent l y p)
      (growthFactor l * p * (Real.exp (p * x) - Real.exp x)) x := by
  have he := ((hasDerivAt_id x).const_mul p).exp
  have hd := ((he.sub_const 1).sub ((Real.hasDerivAt_exp x).sub_const 1 |>.const_mul p))
    |>.const_mul (growthFactor l) |>.const_add (-p)
  convert hd using 1 <;> first | rfl | (simp only [id_eq, mul_one]; ring)

theorem profileMomentExponent_mono_tilt {l p : ℝ} (hl : 1 < l) (hp : 1 ≤ p) :
    MonotoneOn (fun x ↦ profileMomentExponent l x p) (Ici 0) := by
  have hd (x : ℝ) := hasDerivAt_profileMomentExponent_tilt l p x
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (continuous_iff_continuousAt.mpr fun x ↦ (hd x).continuousAt).continuousOn
    (fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  rw [(hd x).deriv]
  apply mul_nonneg (mul_nonneg (growthFactor_pos hl).le (zero_le_one.trans hp))
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A common moment order and a strictly positive decay margin work over an
entire compact interval of nonnegative tilts below the profile edge. -/
theorem exists_uniform_profileMoment_margin {l X : ℝ} (hl : 1 < l)
    (hX : 0 ≤ X) (hXz : X < profileRoot l) :
    ∃ p ∈ Ioo (1 : ℝ) 2, ∃ β > (0 : ℝ), ∀ x ∈ Icc (0 : ℝ) X,
      profileMomentExponent l x p ≤ -1 - β := by
  obtain ⟨p, hp, hB⟩ := exists_profileMomentExponent_lt_neg_one hl hX hXz
  refine ⟨p, hp, -1 - profileMomentExponent l X p, by linarith, ?_⟩
  intro x hx
  have hmono := profileMomentExponent_mono_tilt hl hp.1.le hx.1 hX hx.2
  linarith

theorem exp_sub_exp_le_exp_mul_sub {x y : ℝ} :
    Real.exp y - Real.exp x ≤ Real.exp y * (y - x) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x - y)) (Real.exp_nonneg y)
  have he : Real.exp y * Real.exp (x - y) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  nlinarith

/-- The Jensen loss between two positive tilts is at most a uniform linear
multiple of their gap. -/
theorem profile_tilt_loss_le {l x y X : ℝ} (hl : 1 < l) (hx : 0 < x)
    (hxy : x ≤ y) (hyX : y ≤ X) :
    growthFactor l * (Real.exp y - 1) -
        (y / x) * (growthFactor l * (Real.exp x - 1)) ≤
      growthFactor l * Real.exp X * (y - x) := by
  have hratio : 1 ≤ y / x := (le_div_iff₀ hx).mpr (by simpa using hxy)
  have hb : 0 ≤ growthFactor l * (Real.exp x - 1) :=
    mul_nonneg (growthFactor_pos hl).le (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hx.le))
  have hmul := mul_le_mul_of_nonneg_right hratio hb
  have he := exp_sub_exp_le_exp_mul_sub (x := x) (y := y)
  have heX := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hyX) (sub_nonneg.mpr hxy)
  have hh := mul_le_mul_of_nonneg_left (he.trans heX) (growthFactor_pos hl).le
  nlinarith only [hmul, hh]

/-- The base step from tilt zero has the same linear upper bound on its
normalization loss. -/
theorem profile_tilt_base_loss_le {l y X : ℝ} (hl : 1 < l) (hy : 0 ≤ y) (hyX : y ≤ X) :
    growthFactor l * (Real.exp y - 1) ≤ growthFactor l * Real.exp X * y := by
  have he := exp_sub_exp_le_exp_mul_sub (x := 0) (y := y)
  simp only [Real.exp_zero, sub_zero] at he
  have heX := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hyX) hy
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (he.trans heX) (growthFactor_pos hl).le

end HeightPaper
