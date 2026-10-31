module

public import HeightPaper.Model.ProfilePolynomialTransfer
public import HeightPaper.Analysis.LogCutoff

/-!
# Uniform lower profiles over controlled event words

Uniformity includes the initial susceptible population, so taking a prefix
does not change the initial state parameter. The word conditions below are
explicit polynomial estimates, not stochastic assumptions.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace HeightPaper.Model

def UniformProfileLower (Good : ℕ → (ℕ → Bool) → Prop) (x a : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ ζ > (0 : ℝ), ∀ᶠ N in atTop,
    ∀ n events, Good N events →
      (kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N).real
        {q | realNormalizedLaplace x q.last < (N : ℝ) ^ (a - ε)} ≤ ζ

structure ProfilePolynomialControl (w p a b d A B Bp c : ℝ) (K N : ℕ)
    (events : ℕ → Bool) : Prop where
  positive : ∀ i ≤ N, 0 < prescribedWalk events 1 i
  count : ∀ k ∈ Finset.Icc K N, c * k ≤ (prescribedWalk events 1 k : ℝ)
  lower : ∀ k ∈ Finset.Icc K N, A * (k : ℝ) ^ a ≤ realNormalizer w events 1 k
  upper : ∀ k ∈ Finset.Icc K N, realNormalizer w events 1 k ≤ B * (k : ℝ) ^ b
  powerUpper : ∀ k ∈ Finset.Icc K N, realNormalizer (w ^ p) events 1 k ≤ Bp * (k : ℝ) ^ d

theorem uniformProfileLower_base (Good : ℕ → (ℕ → Bool) → Prop)
    {x p a b d A B Bp c : ℝ} (hx : 0 ≤ x) (hp : 1 < p) (hp2 : p ≤ 2)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hA : 0 < A) (hB : 0 < B) (hBp : 0 < Bp)
    (hc : 0 < c) (K : ℕ)
    (hcontrol : ∀ N events, Good N events →
      ProfilePolynomialControl (Real.exp x) p a b d A B Bp c K N events)
    (hgap : d - p * (a + 1) + 1 + b * p < 0) :
    UniformProfileLower Good x a := by
  let u := d - p * (a + 1) + 1
  let M := (4 * (2 : ℝ) ^ p) * (((Real.exp x) / (A * c)) ^ p * (2 : ℝ) ^ p * Bp) /
    (-(d - p * (a + 1)) - 1)
  let δ₀ := 1 / (2 * B)
  have hδ₀ : 0 < δ₀ := by dsimp only [δ₀]; positivity
  have hexp : d - p * (a + 1) < -1 := by
    have := mul_nonneg hb (by linarith : 0 ≤ p)
    linarith
  have herror := tendsto_moment_error_power_zero (M := M) (d := δ₀) (u := u)
    (D := b) (p := p) hδ₀.le hgap logCutoff tendsto_logCutoff_atTop
  intro ε hε ζ hζ
  have hscale := eventually_rpow_le_mul_logCutoff_rpow
    (show 0 < A / (2 * B) by positivity) hε a b
  filter_upwards [herror.eventually_lt_const hζ, hscale, eventually_logCutoff_le,
    tendsto_logCutoff_atTop.eventually (eventually_ge_atTop (max K 1)), eventually_ge_atTop 1]
      with N herr hscaleN hjN hjK hN
  intro n events hG
  have ctl := hcontrol N events hG
  let j := logCutoff N
  have hj : 1 ≤ j := (le_max_right K 1).trans hjK
  have hKj : K ≤ j := (le_max_left K 1).trans hjK
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let δ := δ₀ * (j : ℝ) ^ (-b)
  have hδ : 0 < δ := mul_pos hδ₀ (Real.rpow_pos_of_pos hjp _)
  have hm := prescribedPath_profile_moment_power_le (Real.one_le_exp_iff.mpr hx) hp hp2
    hA hBp.le hc hd hexp events n N j hj hjN ctl.positive
    (fun k hk ↦ ctl.lower k (by have := Finset.mem_Icc.mp hk; simp; omega))
    (fun k hk ↦ ctl.powerUpper k (by have := Finset.mem_Icc.mp hk; simp; omega))
    (fun k hk ↦ ctl.count k (by have := Finset.mem_Icc.mp hk; simp; omega))
  change (∫ q, ‖normalizedActiveWeight (Real.exp x : ℂ) q.last /
      prescribedNormalizer (Real.exp x : ℂ) events 1 N -
      normalizedActiveWeight (Real.exp x : ℂ) (q.eval j) /
      prescribedNormalizer (Real.exp x : ℂ) events 1 j‖ ^ p
    ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N) ≤ M * (j : ℝ) ^ u at hm
  have hth : 2 * (B * (j : ℝ) ^ b) * δ ≤ 1 := by
    dsimp only [δ, δ₀]
    rw [Real.rpow_neg hjp.le]
    have hjpow := (Real.rpow_pos_of_pos hjp b).ne'
    field_simp
    nlinarith
  have hbound := prescribedPath_profile_base_lower_transfer hx (by linarith : 0 < p)
    (mul_pos hA (Real.rpow_pos_of_pos hNp a)) hδ hth events n N j hjN ctl.positive
    (ctl.lower N (Finset.mem_Icc.mpr ⟨hKj.trans hjN, le_rfl⟩))
    (ctl.upper j (Finset.mem_Icc.mpr ⟨hKj, hjN⟩)) hm
  have hfinal : (N : ℝ) ^ (a - ε) ≤ (A * (N : ℝ) ^ a) * δ := by
    convert hscaleN using 1
    dsimp only [δ, δ₀, j]
    ring
  apply (measureReal_mono (fun q hq ↦ lt_of_lt_of_le hq hfinal)).trans
  exact hbound.trans herr.le

/-- Propagate a uniform lower profile through one positive tilt step. The
moment gap is checked after the precise Jensen loss at the cutoff. -/
theorem uniformProfileLower_step (Good : ℕ → (ℕ → Bool) → Prop)
    {x y f ε₀ p a b d A B Bp c : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hε₀ : 0 < ε₀) (hp : 1 < p) (hp2 : p ≤ 2) (hd : 0 ≤ d)
    (hA : 0 < A) (hB : 0 < B) (hBp : 0 < Bp) (hc : 0 < c) (K : ℕ)
    (hprefix : ∀ N j, K ≤ j → j ≤ N → ∀ events, Good N events → Good j events)
    (hcontrol : ∀ N events, Good N events →
      ProfilePolynomialControl (Real.exp y) p a b d A B Bp c K N events)
    (hexp : d - p * (a + 1) < -1)
    (hgap : d - p * (a + 1) + 1 + (b - (y / x) * (f - ε₀)) * p < 0)
    (hprevious : UniformProfileLower Good x f) :
    UniformProfileLower Good y a := by
  let u := d - p * (a + 1) + 1
  let D := b - (y / x) * (f - ε₀)
  let M := (4 * (2 : ℝ) ^ p) * (((Real.exp y) / (A * c)) ^ p * (2 : ℝ) ^ p * Bp) /
    (-(d - p * (a + 1)) - 1)
  let δ₀ := 1 / (2 * B)
  have hδ₀ : 0 < δ₀ := by dsimp only [δ₀]; positivity
  have herror := tendsto_moment_error_power_zero (M := M) (d := δ₀) (u := u)
    (D := D) (p := p) hδ₀.le hgap logCutoff tendsto_logCutoff_atTop
  intro ε hε ζ hζ
  have hscale := eventually_rpow_le_mul_logCutoff_rpow
    (show 0 < A / (2 * B) by positivity) hε a D
  have hprior := tendsto_logCutoff_atTop.eventually (hprevious ε₀ hε₀ (ζ / 2) (by positivity))
  filter_upwards [herror.eventually_lt_const (by positivity : 0 < ζ / 2), hprior, hscale,
    eventually_logCutoff_le,
    tendsto_logCutoff_atTop.eventually (eventually_ge_atTop (max K 1)), eventually_ge_atTop 1]
      with N herr hpriorN hscaleN hjN hjK hN
  intro n events hG
  have ctl := hcontrol N events hG
  let j := logCutoff N
  have hj : 1 ≤ j := (le_max_right K 1).trans hjK
  have hKj : K ≤ j := (le_max_left K 1).trans hjK
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let δ := δ₀ * (j : ℝ) ^ (-D)
  have hδ : 0 < δ := mul_pos hδ₀ (Real.rpow_pos_of_pos hjp _)
  have hm := prescribedPath_profile_moment_power_le (Real.one_le_exp_iff.mpr (hx.le.trans hxy))
    hp hp2 hA hBp.le hc hd hexp events n N j hj hjN ctl.positive
    (fun k hk ↦ ctl.lower k (by have := Finset.mem_Icc.mp hk; simp; omega))
    (fun k hk ↦ ctl.powerUpper k (by have := Finset.mem_Icc.mp hk; simp; omega))
    (fun k hk ↦ ctl.count k (by have := Finset.mem_Icc.mp hk; simp; omega))
  change (∫ q, ‖normalizedActiveWeight (Real.exp y : ℂ) q.last /
      prescribedNormalizer (Real.exp y : ℂ) events 1 N -
      normalizedActiveWeight (Real.exp y : ℂ) (q.eval j) /
      prescribedNormalizer (Real.exp y : ℂ) events 1 j‖ ^ p
    ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N) ≤ M * (j : ℝ) ^ u at hm
  have hth : 2 * (B * (j : ℝ) ^ b) * δ ≤ ((j : ℝ) ^ (f - ε₀)) ^ (y / x) := by
    apply le_of_eq
    calc
      _ = (j : ℝ) ^ (b - D) := by
        dsimp only [δ, δ₀]
        rw [Real.rpow_sub hjp, Real.rpow_neg hjp.le]
        field_simp
      _ = _ := by
        rw [← Real.rpow_mul hjp.le]
        congr 1
        dsimp only [D]
        ring
  have hbound := prescribedPath_profile_tilt_lower_transfer hx hxy (by linarith : 0 < p)
    (mul_pos hA (Real.rpow_pos_of_pos hNp a)) hδ (Real.rpow_nonneg hjp.le _) hth
    events n N j hjN ctl.positive
    (ctl.lower N (Finset.mem_Icc.mpr ⟨hKj.trans hjN, le_rfl⟩))
    (ctl.upper j (Finset.mem_Icc.mpr ⟨hKj, hjN⟩)) hm
  have hfinal : (N : ℝ) ^ (a - ε) ≤ (A * (N : ℝ) ^ a) * δ := by
    convert hscaleN using 1
    dsimp only [δ, δ₀, j]
    ring
  apply (measureReal_mono (fun q hq ↦ lt_of_lt_of_le hq hfinal)).trans
  apply hbound.trans
  have hpr := hpriorN n events (hprefix N j hKj hjN events hG)
  linarith

end HeightPaper.Model
