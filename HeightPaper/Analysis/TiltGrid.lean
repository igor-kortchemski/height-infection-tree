module

public import HeightPaper.Analysis.TiltBootstrap
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # A common finite tilt grid for uniform lower-profile induction -/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace HeightPaper

def lowerProfileSlope (g x : ℝ) : ℝ := g * (Real.exp x - 1)

def tiltMomentPower (lo hi p y : ℝ) : ℝ :=
  hi * (Real.exp (p * y) - 1) - p * (lowerProfileSlope lo y + 1) + 1

def tiltBasePower (lo hi p y : ℝ) : ℝ :=
  tiltMomentPower lo hi p y + lowerProfileSlope hi y * p

def tiltStepPower (lo hi p x y e : ℝ) : ℝ :=
  tiltMomentPower lo hi p y +
    (lowerProfileSlope hi y - (y / x) * (lowerProfileSlope lo x - e)) * p

def lowerTiltGrid (X : ℝ) (J : ℕ) (i : Fin (J + 1)) : ℝ :=
  X * (i.val + 1 : ℕ) / (J + 1 : ℕ)

theorem lowerTiltGrid_mem {X : ℝ} (hX : 0 < X) (J : ℕ) (i : Fin (J + 1)) :
    lowerTiltGrid X J i ∈ Ioc 0 X := by
  have hd : (0 : ℝ) < (J + 1 : ℕ) := by positivity
  have hi : ((i.val + 1 : ℕ) : ℝ) ≤ (J + 1 : ℕ) := by exact_mod_cast (show i.val + 1 ≤ J + 1 by omega)
  exact ⟨div_pos (mul_pos hX (by positivity)) hd,
    (div_le_iff₀ hd).mpr (mul_le_mul_of_nonneg_left hi hX.le)⟩

theorem lowerTiltGrid_strict {X : ℝ} (hX : 0 < X) (J : ℕ) (i : Fin J) :
    lowerTiltGrid X J i.castSucc < lowerTiltGrid X J i.succ := by
  unfold lowerTiltGrid
  apply div_lt_div_of_pos_right _ (by positivity)
  apply mul_lt_mul_of_pos_left _ hX
  exact_mod_cast (show i.val + 1 < i.val + 1 + 1 by omega)

@[simp] theorem lowerTiltGrid_last (X : ℝ) (J : ℕ) :
    lowerTiltGrid X J (Fin.last J) = X := by
  unfold lowerTiltGrid
  simp only [Fin.val_last]
  exact mul_div_cancel_right₀ X (by positivity)

private theorem tiltMomentPower_ideal (l p y : ℝ) :
    tiltMomentPower (growthFactor l) (growthFactor l) p y = profileMomentExponent l y p + 1 := by
  unfold tiltMomentPower lowerProfileSlope profileMomentExponent
  ring

private theorem exists_positive_step_tolerance {lo hi p x y : ℝ}
    (hgap : tiltStepPower lo hi p x y 0 < 0) :
    ∃ e > (0 : ℝ), tiltStepPower lo hi p x y e < 0 := by
  have hc : ContinuousAt (fun e ↦ tiltStepPower lo hi p x y e) 0 := by
    unfold tiltStepPower
    fun_prop
  obtain ⟨d, hd, hbound⟩ := Metric.eventually_nhds_iff.mp
    (hc.tendsto.eventually (gt_mem_nhds hgap))
  refine ⟨d / 2, half_pos hd, hbound ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hd)]
  exact half_lt_self hd

/-- A fixed moment order and a fixed positive finite grid work for all pairs
of normalizer slopes in one neighborhood of the exact epidemic slope. -/
theorem exists_uniform_lower_tilt_grid {l X : ℝ} (hl : 1 < l) (hX : 0 < X)
    (hXz : X < profileRoot l) :
    ∃ (p : ℝ) (J : ℕ) (η : ℝ), p ∈ Ioo (1 : ℝ) 2 ∧ 0 < η ∧
      ∀ lo hi : ℝ, |lo - growthFactor l| < η → |hi - growthFactor l| < η →
        0 < lo ∧ 0 < hi ∧
        tiltBasePower lo hi p (lowerTiltGrid X J 0) < 0 ∧
        (∀ i : Fin (J + 1), tiltMomentPower lo hi p (lowerTiltGrid X J i) < 0) ∧
        (∀ i : Fin J, ∃ e > (0 : ℝ),
          tiltStepPower lo hi p (lowerTiltGrid X J i.castSucc) (lowerTiltGrid X J i.succ) e < 0) := by
  classical
  obtain ⟨p, hp, β, hβ, hmoment⟩ := exists_uniform_profileMoment_margin hl hX.le hXz
  let γ := growthFactor l
  let C := γ * Real.exp X
  have hC : 0 < C := mul_pos (growthFactor_pos hl) (Real.exp_pos X)
  have hp0 : 0 < p := zero_lt_one.trans hp.1
  have hstep : Tendsto (fun J : ℕ ↦ X / (J + 1 : ℕ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hbasecont : Continuous (fun y ↦ tiltBasePower γ γ p y) := by
    unfold tiltBasePower tiltMomentPower lowerProfileSlope
    fun_prop
  have hbaselim : Tendsto (fun J : ℕ ↦ tiltBasePower γ γ p (X / (J + 1 : ℕ))) atTop (𝓝 (1 - p)) := by
    have hz : tiltBasePower γ γ p 0 = 1 - p := by
      simp [tiltBasePower, tiltMomentPower, lowerProfileSlope]
      ring
    rw [← hz]
    exact hbasecont.continuousAt.tendsto.comp hstep
  have hsmall := hstep.eventually (gt_mem_nhds (div_pos hβ (mul_pos hp0 hC)))
  obtain ⟨J, hJbase, hJgap⟩ := ((hbaselim.eventually (gt_mem_nhds (sub_neg.mpr hp.1))).and hsmall).exists
  have hbase : tiltBasePower γ γ p (lowerTiltGrid X J 0) < 0 := by
    simpa only [lowerTiltGrid, Fin.val_zero, Nat.zero_add, Nat.cast_one, mul_one] using hJbase
  have hu : ∀ i : Fin (J + 1), tiltMomentPower γ γ p (lowerTiltGrid X J i) < 0 := by
    intro i
    have hb := hmoment _ ⟨(lowerTiltGrid_mem hX J i).1.le, (lowerTiltGrid_mem hX J i).2⟩
    rw [tiltMomentPower_ideal]
    linarith
  have hs : ∀ i : Fin J,
      tiltStepPower γ γ p (lowerTiltGrid X J i.castSucc) (lowerTiltGrid X J i.succ) 0 < 0 := by
    intro i
    let x := lowerTiltGrid X J i.castSucc
    let y := lowerTiltGrid X J i.succ
    have hx : 0 < x := (lowerTiltGrid_mem hX J i.castSucc).1
    have hxy : x ≤ y := (lowerTiltGrid_strict hX J i).le
    have hyX : y ≤ X := (lowerTiltGrid_mem hX J i.succ).2
    have hgap : y - x = X / (J + 1 : ℕ) := by
      dsimp [x, y, lowerTiltGrid]
      push_cast
      ring
    have hloss := profile_tilt_loss_le hl hx hxy hyX
    have hb := hmoment y ⟨hx.le.trans hxy, hyX⟩
    have hsmall' := (lt_div_iff₀ (mul_pos hp0 hC)).mp hJgap
    change tiltStepPower γ γ p x y 0 < 0
    unfold tiltStepPower
    rw [tiltMomentPower_ideal]
    simp only [sub_zero]
    change profileMomentExponent l y p + 1 +
      (γ * (Real.exp y - 1) - y / x * (γ * (Real.exp x - 1))) * p < 0
    rw [hgap] at hloss
    dsimp [C, γ] at hsmall'
    have hh := mul_le_mul_of_nonneg_right hloss hp0.le
    dsimp [γ]
    nlinarith
  have hevent : ∀ᶠ q : ℝ × ℝ in 𝓝 (γ, γ),
      0 < q.1 ∧ 0 < q.2 ∧ tiltBasePower q.1 q.2 p (lowerTiltGrid X J 0) < 0 ∧
      (∀ i : Fin (J + 1), tiltMomentPower q.1 q.2 p (lowerTiltGrid X J i) < 0) ∧
      (∀ i : Fin J, tiltStepPower q.1 q.2 p (lowerTiltGrid X J i.castSucc) (lowerTiltGrid X J i.succ) 0 < 0) := by
    have hb : ContinuousAt (fun q : ℝ × ℝ ↦ tiltBasePower q.1 q.2 p (lowerTiltGrid X J 0)) (γ, γ) := by
      unfold tiltBasePower tiltMomentPower lowerProfileSlope
      fun_prop
    have hu' : ∀ᶠ q : ℝ × ℝ in 𝓝 (γ, γ), ∀ i : Fin (J + 1),
        tiltMomentPower q.1 q.2 p (lowerTiltGrid X J i) < 0 := by
      apply eventually_all.mpr
      intro i
      have hc : ContinuousAt (fun q : ℝ × ℝ ↦ tiltMomentPower q.1 q.2 p (lowerTiltGrid X J i)) (γ, γ) := by
        unfold tiltMomentPower lowerProfileSlope
        fun_prop
      exact hc.tendsto.eventually (gt_mem_nhds (hu i))
    have hs' : ∀ᶠ q : ℝ × ℝ in 𝓝 (γ, γ), ∀ i : Fin J,
        tiltStepPower q.1 q.2 p (lowerTiltGrid X J i.castSucc) (lowerTiltGrid X J i.succ) 0 < 0 := by
      apply eventually_all.mpr
      intro i
      have hc : ContinuousAt (fun q : ℝ × ℝ ↦
          tiltStepPower q.1 q.2 p (lowerTiltGrid X J i.castSucc) (lowerTiltGrid X J i.succ) 0) (γ, γ) := by
        unfold tiltStepPower tiltMomentPower lowerProfileSlope
        fun_prop
      exact hc.tendsto.eventually (gt_mem_nhds (hs i))
    filter_upwards [continuousAt_fst.tendsto.eventually (lt_mem_nhds (growthFactor_pos hl)),
      continuousAt_snd.tendsto.eventually (lt_mem_nhds (growthFactor_pos hl)),
      hb.tendsto.eventually (gt_mem_nhds hbase), hu', hs'] with q hq1 hq2 hqb hqu hqs
    exact ⟨hq1, hq2, hqb, hqu, hqs⟩
  obtain ⟨η, hη, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨p, J, η, hp, hη, ?_⟩
  intro lo hi hlo hhi
  have hdist : dist (lo, hi) (γ, γ) < η := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt hlo hhi
  obtain ⟨hlo0, hhi0, hb, hu, hs⟩ := hnear hdist
  exact ⟨hlo0, hhi0, hb, hu, fun i ↦ exists_positive_step_tolerance (hs i)⟩

end HeightPaper
