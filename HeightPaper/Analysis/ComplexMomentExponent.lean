module

public import HeightPaper.Analysis.ProfileMomentExponent
public import HeightPaper.Analysis.ProfileMomentTail
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Complex.Exponential

/-!
# Complex profile moment exponents near a real tilt

The paper's summable increment exponent persists on a whole complex
neighborhood, with one moment order and one decay margin for every epidemic
parameter above a fixed lower endpoint. This is the deterministic uniformity
step in `corollaire M nt proche de M An`.
-/

@[expose] public section

open Filter Set
open scoped Topology BigOperators

namespace HeightPaper

noncomputable def complexProfileMomentExponent (l : ℝ) (z : ℂ) (p : ℝ) : ℝ :=
  -p + growthFactor l *
    (Real.exp (p * z.re) - 1 - p * ((Complex.exp z).re - 1))

@[simp] theorem complexProfileMomentExponent_ofReal (l x p : ℝ) :
    complexProfileMomentExponent l (x : ℂ) p = profileMomentExponent l x p := by
  simp [complexProfileMomentExponent, profileMomentExponent, ← Complex.ofReal_exp]

theorem continuous_complexProfileMomentExponent (l p : ℝ) :
    Continuous (fun z : ℂ ↦ complexProfileMomentExponent l z p) := by
  unfold complexProfileMomentExponent
  fun_prop

theorem complex_profile_ratio_exponent_nonneg (z : ℂ) {p : ℝ} (hp : 1 ≤ p) :
    0 ≤ Real.exp (p * z.re) - 1 - p * ((Complex.exp z).re - 1) := by
  have h := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ Real.exp z.re - 1 by linarith [Real.exp_pos z.re]) hp
  rw [show 1 + (Real.exp z.re - 1) = Real.exp z.re by ring,
    ← Real.exp_mul] at h
  have hre : (Complex.exp z).re ≤ Real.exp z.re := by
    simpa only [Complex.norm_exp] using Complex.re_le_norm (Complex.exp z)
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have := mul_le_mul_of_nonneg_left hre hp0
  rw [mul_comm z.re p] at h
  nlinarith

theorem growthFactor_antitone {l L : ℝ} (hl : 1 < l) (hL : l ≤ L) :
    growthFactor L ≤ growthFactor l := by
  unfold growthFactor
  apply (div_le_div_iff₀ (by linarith : 0 < L - 1) (by linarith : 0 < l - 1)).mpr
  nlinarith

theorem complexProfileMomentExponent_antitone_parameter {l L p : ℝ}
    (hl : 1 < l) (hL : l ≤ L) (hp : 1 ≤ p) (z : ℂ) :
    complexProfileMomentExponent L z p ≤ complexProfileMomentExponent l z p := by
  exact add_le_add_right
    (mul_le_mul_of_nonneg_right (growthFactor_antitone hl hL)
      (complex_profile_ratio_exponent_nonneg z hp)) _

/-- A common moment order, disk, and strictly summable exponent for all
parameters above the lower endpoint. In particular these constants are uniform
on every compact parameter interval with that endpoint. -/
theorem exists_uniform_complex_profile_moment_decay {l x : ℝ} (hl : 1 < l)
    (hx : 0 ≤ x) (hxr : x < profileRoot l) :
    ∃ p ∈ Ioo (1 : ℝ) 2, ∃ η > 0, ∃ r > 0,
      ∀ L : ℝ, l ≤ L → ∀ z : ℂ, dist z (x : ℂ) < r →
        complexProfileMomentExponent L z p ≤ -1 - η := by
  obtain ⟨p, hp, he⟩ := exists_profileMomentExponent_lt_neg_one hl hx hxr
  let η := (-1 - profileMomentExponent l x p) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hlt : complexProfileMomentExponent l (x : ℂ) p < -1 - η := by
    rw [complexProfileMomentExponent_ofReal]
    dsimp [η]
    linarith
  have hnb : ∀ᶠ z in 𝓝 (x : ℂ),
      complexProfileMomentExponent l z p < -1 - η :=
    (continuous_complexProfileMomentExponent l p).continuousAt.eventually
      (gt_mem_nhds hlt)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnb
  refine ⟨p, hp, η, hη, r, hr, ?_⟩
  intro L hL z hz
  exact (complexProfileMomentExponent_antitone_parameter hl hL hp.1.le z).trans
    (hball hz).le

/-- A single deterministic power tail controls all exponents in the preceding
complex neighborhood, uniformly in the terminal horizon. -/
theorem sum_complex_profile_moment_le {l p η : ℝ} {z : ℂ}
    (hη : 0 < η) (he : complexProfileMomentExponent l z p ≤ -1 - η)
    {j N : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) :
    ∑ k ∈ Finset.Ico j N, ((k + 1 : ℕ) : ℝ) ^
      complexProfileMomentExponent l z p ≤ (j : ℝ) ^ (-η) / η := by
  calc
    _ ≤ ∑ k ∈ Finset.Ico j N, ((k + 1 : ℕ) : ℝ) ^ (-1 - η) := by
      apply Finset.sum_le_sum
      intro k _
      apply Real.rpow_le_rpow_of_exponent_le _ he
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    _ ≤ (j : ℝ) ^ ((-1 - η) + 1) / (-(-1 - η) - 1) :=
      sum_Ico_succ_rpow_le (by linarith) hj hjN
    _ = _ := by
      rw [show (-1 - η) + 1 = -η by ring, show -(-1 - η) - 1 = η by ring]

end HeightPaper
