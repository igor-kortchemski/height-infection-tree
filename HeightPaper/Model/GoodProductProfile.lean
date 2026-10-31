module

public import HeightPaper.Model.UniformProfileLower
public import HeightPaper.Model.GoodProductWords

/-! # Applying the finite tilt bootstrap to controlled product words -/

public section

namespace HeightPaper.Model

theorem GoodProductWord.profilePolynomialControl {lo hi c : ℝ} {A B : ℝ → ℝ}
    {K N : ℕ} {events : ℕ → Bool} (h : GoodProductWord lo hi c A B K N events)
    {w p : ℝ} (hw : 1 ≤ w) (hp : 0 ≤ p) :
    ProfilePolynomialControl w p ((w - 1) * lo) ((w - 1) * hi) ((w ^ p - 1) * hi)
      (A w) (B w) (B (w ^ p)) c K N events where
  positive := h.positive
  count := h.count
  lower := h.lower w hw
  upper := h.upper w hw
  powerUpper := h.upper (w ^ p) (Real.one_le_rpow hw hp)

theorem goodProduct_uniformProfileLower_base {lo hi c x p : ℝ} (A B : ℝ → ℝ)
    (hhi : 0 ≤ hi) (hc : 0 < c) (hx : 0 ≤ x) (hp : 1 < p) (hp2 : p ≤ 2)
    (hAB : ∀ w ≥ (1 : ℝ), 0 < A w ∧ 0 < B w) (K : ℕ)
    (hgap : ((Real.exp x) ^ p - 1) * hi - p * ((Real.exp x - 1) * lo + 1) + 1 +
      ((Real.exp x - 1) * hi) * p < 0) :
    UniformProfileLower (GoodProductWord lo hi c A B K) x ((Real.exp x - 1) * lo) := by
  have hw : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  have hp0 : 0 ≤ p := by linarith
  have hwp : 1 ≤ (Real.exp x) ^ p := Real.one_le_rpow hw hp0
  exact uniformProfileLower_base _ hx hp hp2
    (mul_nonneg (sub_nonneg.mpr hw) hhi) (mul_nonneg (sub_nonneg.mpr hwp) hhi)
    (hAB _ hw).1 (hAB _ hw).2 (hAB _ hwp).2 hc K
    (fun N events h ↦ h.profilePolynomialControl hw hp0) hgap

theorem goodProduct_uniformProfileLower_step {lo hi c x y ε₀ p : ℝ} (A B : ℝ → ℝ)
    (hhi : 0 ≤ hi) (hc : 0 < c) (hx : 0 < x) (hxy : x ≤ y) (hε₀ : 0 < ε₀)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (hAB : ∀ w ≥ (1 : ℝ), 0 < A w ∧ 0 < B w) (K : ℕ)
    (hexp : ((Real.exp y) ^ p - 1) * hi - p * ((Real.exp y - 1) * lo + 1) < -1)
    (hgap : ((Real.exp y) ^ p - 1) * hi - p * ((Real.exp y - 1) * lo + 1) + 1 +
      ((Real.exp y - 1) * hi - (y / x) * ((Real.exp x - 1) * lo - ε₀)) * p < 0)
    (hprevious : UniformProfileLower (GoodProductWord lo hi c A B K) x
      ((Real.exp x - 1) * lo)) :
    UniformProfileLower (GoodProductWord lo hi c A B K) y ((Real.exp y - 1) * lo) := by
  have hw : 1 ≤ Real.exp y := Real.one_le_exp_iff.mpr (hx.le.trans hxy)
  have hp0 : 0 ≤ p := by linarith
  have hwp : 1 ≤ (Real.exp y) ^ p := Real.one_le_rpow hw hp0
  exact uniformProfileLower_step _ hx hxy hε₀ hp hp2
    (mul_nonneg (sub_nonneg.mpr hwp) hhi)
    (hAB _ hw).1 (hAB _ hw).2 (hAB _ hwp).2 hc K
    (fun _ _ _ hj _ h ↦ h.prefix hj)
    (fun N events h ↦ h.profilePolynomialControl hw hp0) hexp hgap hprevious

end HeightPaper.Model
