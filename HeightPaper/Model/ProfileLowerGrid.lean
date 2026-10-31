module

public import HeightPaper.Model.GoodProductProfile
public import HeightPaper.Analysis.TiltGrid

/-!
# Uniform lower profiles at every interior positive tilt

The analytic finite grid and the checked stochastic propagation give a lower
profile bound for all controlled event words. This proves the required real
lower estimate without asserting the source's complex nonvanishing argument.
-/

public section

namespace HeightPaper.Model

theorem goodProduct_uniformProfileLower_of_grid {lo hi c X p : ℝ}
    (A B : ℝ → ℝ) (K J : ℕ) (hhi : 0 ≤ hi) (hc : 0 < c) (hX : 0 < X)
    (hp : 1 < p) (hp2 : p ≤ 2) (hAB : ∀ w ≥ (1 : ℝ), 0 < A w ∧ 0 < B w)
    (hbase : tiltBasePower lo hi p (lowerTiltGrid X J 0) < 0)
    (hmoment : ∀ i : Fin (J + 1), tiltMomentPower lo hi p (lowerTiltGrid X J i) < 0)
    (hstep : ∀ i : Fin J, ∃ e > (0 : ℝ),
      tiltStepPower lo hi p (lowerTiltGrid X J i.castSucc) (lowerTiltGrid X J i.succ) e < 0) :
    UniformProfileLower (GoodProductWord lo hi c A B K) X ((Real.exp X - 1) * lo) := by
  have hpow (x : ℝ) : (Real.exp x) ^ p = Real.exp (p * x) := by
    rw [← Real.exp_mul, mul_comm]
  have hall : ∀ i : Fin (J + 1),
      UniformProfileLower (GoodProductWord lo hi c A B K) (lowerTiltGrid X J i)
        ((Real.exp (lowerTiltGrid X J i) - 1) * lo) := by
    intro i
    induction i using Fin.induction with
    | zero =>
        apply goodProduct_uniformProfileLower_base A B hhi hc (lowerTiltGrid_mem hX J 0).1.le
          hp hp2 hAB K
        rw [hpow]
        dsimp only [tiltBasePower, tiltMomentPower, lowerProfileSlope] at hbase
        nlinarith only [hbase]
    | succ i ih =>
        obtain ⟨e, he, hs⟩ := hstep i
        apply goodProduct_uniformProfileLower_step A B hhi hc
          (lowerTiltGrid_mem hX J i.castSucc).1 (lowerTiltGrid_strict hX J i).le he hp hp2 hAB K
          _ _ ih
        · rw [hpow]
          have hm := hmoment i.succ
          dsimp only [tiltMomentPower, lowerProfileSlope] at hm
          nlinarith only [hm]
        · rw [hpow]
          dsimp only [tiltStepPower, tiltMomentPower, lowerProfileSlope] at hs
          nlinarith only [hs]
  simpa only [lowerTiltGrid_last] using hall (Fin.last J)

/-- One neighborhood of the ideal normalizer slope suffices for the entire
finite bootstrap to a fixed interior tilt, uniformly in all product constants. -/
theorem exists_goodProduct_uniformProfileLower {l X : ℝ}
    (hl : 1 < l) (hX : 0 < X) (hXz : X < profileRoot l) :
    ∃ η > (0 : ℝ), ∀ lo hi : ℝ,
      |lo - growthFactor l| < η → |hi - growthFactor l| < η →
      ∀ (c : ℝ) (A B : ℝ → ℝ) (K : ℕ), 0 < c →
        (∀ w ≥ (1 : ℝ), 0 < A w ∧ 0 < B w) →
        UniformProfileLower (GoodProductWord lo hi c A B K) X ((Real.exp X - 1) * lo) := by
  obtain ⟨p, J, η, hp, hη, hgrid⟩ := exists_uniform_lower_tilt_grid hl hX hXz
  refine ⟨η, hη, ?_⟩
  intro lo hi hlo hhi c A B K hc hAB
  obtain ⟨_, hhi0, hbase, hmoment, hstep⟩ := hgrid lo hi hlo hhi
  exact goodProduct_uniformProfileLower_of_grid A B K J hhi0.le hc hX hp.1 hp.2.le
    hAB hbase hmoment hstep

end HeightPaper.Model
