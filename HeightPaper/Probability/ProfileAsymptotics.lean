module

public import HeightPaper.Probability.ProfileBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

import Mathlib.Tactic.FieldSimp

/-!
# Logarithmic finite-profile bounds from real Laplace estimates

These deterministic transfer results turn exponential Laplace bounds at nearby
real tilts into bounds for a narrower bin, then include that bin in the requested
one. For the paper's weak logarithmic estimate, the narrower bin must approach
the lower endpoint of the requested bin. No epidemic Laplace asymptotic or
probabilistic convergence is asserted here.
-/

public section

open Filter Set
open scoped Topology

namespace HeightPaper.Profile

variable {ι : Type*} {α : ι → Type*} {ℓ : Filter ι}

/-- Increasing a bin can only increase its mass for nonnegative weights. -/
theorem binMass_mono {β : Type*} (s : Finset β) (w d : β → ℝ)
    {a b A B : ℝ} (hA : A ≤ a) (hB : b ≤ B) (hw : ∀ i ∈ s, 0 ≤ w i) :
    binMass s w d a b ≤ binMass s w d A B := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : a ≤ d i ∧ d i ≤ b
  · have h' : A ≤ d i ∧ d i ≤ B := ⟨hA.trans h.1, h.2.trans hB⟩
    simp only [h, h', le_refl]
  · simp only [h, ite_false]
    split_ifs
    · exact hw i hi
    · exact le_rfl

/-- A strict gap in exponential rates absorbs any fixed positive prefactor. -/
theorem eventually_exp_le_const_mul_exp {L : ι → ℝ} (hL : Tendsto L ℓ atTop)
    {u v q : ℝ} (huv : u < v) (hq : 0 < q) :
    ∀ᶠ n in ℓ, Real.exp (u * L n) ≤ q * Real.exp (v * L n) := by
  have ht : Tendsto (fun n ↦ Real.exp ((u - v) * L n)) ℓ (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (sub_neg.mpr huv) hL)
  filter_upwards [ht.eventually (Iio_mem_nhds hq)] with n hn
  calc
    Real.exp (u * L n) = Real.exp ((u - v) * L n) * Real.exp (v * L n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ q * Real.exp (v * L n) :=
      mul_le_mul_of_nonneg_right hn.le (Real.exp_nonneg _)

/-- Logarithmic convergence gives eventual exponential bounds, provided the
transform and scale are positive. -/
theorem eventually_exp_bounds_of_log_tendsto {L Z : ι → ℝ}
    (hL : Tendsto L ℓ atTop) (hZ : ∀ᶠ n in ℓ, 0 < Z n) {c lo hi : ℝ}
    (hlog : Tendsto (fun n ↦ Real.log (Z n) / L n) ℓ (𝓝 c))
    (hlo : lo < c) (hhi : c < hi) :
    ∀ᶠ n in ℓ, Real.exp (lo * L n) ≤ Z n ∧ Z n ≤ Real.exp (hi * L n) := by
  filter_upwards [hL.eventually_gt_atTop 0, hZ,
    hlog.eventually (Ioo_mem_nhds hlo hhi)] with n hLn hZn hn
  constructor
  · have hh : lo * L n < Real.log (Z n) := (lt_div_iff₀ hLn).mp hn.1
    simpa only [Real.exp_log hZn] using (Real.exp_lt_exp.mpr hh).le
  · have hh : Real.log (Z n) < hi * L n := (div_lt_iff₀ hLn).mp hn.2
    simpa only [Real.exp_log hZn] using (Real.exp_lt_exp.mpr hh).le

/-- Three eventual exponential Laplace bounds force an exponential lower bound
for any larger bin. The loss uses the upper endpoint `b` of the inner bin. -/
theorem eventually_exp_le_binMass_of_laplace_bounds
    (s : (n : ι) → Finset (α n)) (w d : (n : ι) → α n → ℝ)
    {L : ι → ℝ} (hL : Tendsto L ℓ atTop)
    (hw : ∀ n, ∀ i ∈ s n, 0 ≤ w n i)
    {t ε a b A B c cm cp r : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hA : A ≤ a) (hB : b ≤ B)
    (hm : cm + ε * a < c) (hp : cp - ε * b < c) (hr : r < c - t * b)
    (hcentral : ∀ᶠ n in ℓ, Real.exp (c * L n) ≤ laplaceSum (s n) (w n) (d n) t)
    (hminus : ∀ᶠ n in ℓ, laplaceSum (s n) (w n) (d n) (t - ε) ≤
      Real.exp (cm * L n))
    (hplus : ∀ᶠ n in ℓ, laplaceSum (s n) (w n) (d n) (t + ε) ≤
      Real.exp (cp * L n)) :
    ∀ᶠ n in ℓ, Real.exp (r * L n) ≤
      binMass (s n) (w n) (d n) (A * L n) (B * L n) := by
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  filter_upwards [hL.eventually_ge_atTop 0, hcentral, hminus, hplus,
    eventually_exp_le_const_mul_exp hL hm hquarter,
    eventually_exp_le_const_mul_exp hL hp hquarter,
    eventually_exp_le_const_mul_exp hL hr hhalf] with n hLn hc hn hp' hem hep her
  have hminus' : Real.exp (ε * (a * L n)) * laplaceSum (s n) (w n) (d n) (t - ε) ≤
      (1 / 4) * Real.exp (c * L n) := by
    calc
      _ ≤ Real.exp (ε * (a * L n)) * Real.exp (cm * L n) :=
        mul_le_mul_of_nonneg_left hn (Real.exp_nonneg _)
      _ = Real.exp ((cm + ε * a) * L n) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := hem
  have hplus' : Real.exp (-ε * (b * L n)) * laplaceSum (s n) (w n) (d n) (t + ε) ≤
      (1 / 4) * Real.exp (c * L n) := by
    calc
      _ ≤ Real.exp (-ε * (b * L n)) * Real.exp (cp * L n) :=
        mul_le_mul_of_nonneg_left hp' (Real.exp_nonneg _)
      _ = Real.exp ((cp - ε * b) * L n) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := hep
  have hsmall : Real.exp (ε * (a * L n)) * laplaceSum (s n) (w n) (d n) (t - ε) +
      Real.exp (-ε * (b * L n)) * laplaceSum (s n) (w n) (d n) (t + ε) ≤
      (1 / 2) * laplaceSum (s n) (w n) (d n) t := by linarith
  calc
    Real.exp (r * L n) ≤ (1 / 2) * Real.exp ((c - t * b) * L n) := her
    _ = Real.exp (-t * (b * L n)) * ((1 - 1 / 2) * Real.exp (c * L n)) := by
      have hexp : Real.exp ((c - t * b) * L n) =
          Real.exp (-t * (b * L n)) * Real.exp (c * L n) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    _ ≤ Real.exp (-t * (b * L n)) * ((1 - 1 / 2) *
        laplaceSum (s n) (w n) (d n) t) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact mul_le_mul_of_nonneg_left hc (by norm_num)
    _ ≤ binMass (s n) (w n) (d n) (a * L n) (b * L n) :=
      one_sub_mul_laplace_le_binMass (s n) (w n) (d n) ht hε _ _ (hw n) hsmall
    _ ≤ binMass (s n) (w n) (d n) (A * L n) (B * L n) :=
      binMass_mono _ _ _ (mul_le_mul_of_nonneg_right hA hLn)
        (mul_le_mul_of_nonneg_right hB hLn) (hw n)

/-- The one-sided exponential Markov bound transferred to a growing scale. -/
theorem eventually_binMass_le_exp_of_laplace_bound
    (s : (n : ι) → Finset (α n)) (w d : (n : ι) → α n → ℝ)
    (hw : ∀ n, ∀ i ∈ s n, 0 ≤ w n i)
    {L : ι → ℝ} {t A B c : ℝ} (ht : 0 ≤ t)
    (hupper : ∀ᶠ n in ℓ, laplaceSum (s n) (w n) (d n) t ≤ Real.exp (c * L n)) :
    ∀ᶠ n in ℓ, binMass (s n) (w n) (d n) (A * L n) (B * L n) ≤
      Real.exp ((c - t * A) * L n) := by
  filter_upwards [hupper] with n hn
  calc
    _ ≤ tailMass (s n) (w n) (d n) (A * L n) := binMass_le_tailMass _ _ _ _ _ (hw n)
    _ ≤ Real.exp (-t * (A * L n)) * laplaceSum (s n) (w n) (d n) t :=
      tailMass_le_exp_neg_mul_laplaceSum _ _ _ ht _ (hw n)
    _ ≤ Real.exp (-t * (A * L n)) * Real.exp (c * L n) :=
      mul_le_mul_of_nonneg_left hn (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Logarithmic Laplace limits at a central tilt and two neighboring tilts
imply every strictly smaller inner-bin exponent for the outer bin. -/
theorem eventually_exp_le_binMass_of_log_laplace
    (s : (n : ι) → Finset (α n)) (w d : (n : ι) → α n → ℝ)
    {L : ι → ℝ} (hL : Tendsto L ℓ atTop)
    (hw : ∀ n, ∀ i ∈ s n, 0 ≤ w n i)
    {t ε a b A B c cm cp r : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hA : A ≤ a) (hB : b ≤ B)
    (hm : cm + ε * a < c) (hp : cp - ε * b < c) (hr : r < c - t * b)
    (hZ : ∀ᶠ n in ℓ, 0 < laplaceSum (s n) (w n) (d n) t)
    (hZm : ∀ᶠ n in ℓ, 0 < laplaceSum (s n) (w n) (d n) (t - ε))
    (hZp : ∀ᶠ n in ℓ, 0 < laplaceSum (s n) (w n) (d n) (t + ε))
    (hc : Tendsto (fun n ↦ Real.log (laplaceSum (s n) (w n) (d n) t) / L n) ℓ (𝓝 c))
    (hcm : Tendsto (fun n ↦ Real.log (laplaceSum (s n) (w n) (d n) (t - ε)) / L n)
      ℓ (𝓝 cm))
    (hcp : Tendsto (fun n ↦ Real.log (laplaceSum (s n) (w n) (d n) (t + ε)) / L n)
      ℓ (𝓝 cp)) :
    ∀ᶠ n in ℓ, Real.exp (r * L n) ≤
      binMass (s n) (w n) (d n) (A * L n) (B * L n) := by
  have hmax : max (r + t * b) (max (cm + ε * a) (cp - ε * b)) < c := by
    exact max_lt (by linarith) (max_lt hm hp)
  obtain ⟨c', hc'low, hc'high⟩ := exists_between hmax
  have hr' : r < c' - t * b := by
    have := (le_max_left (r + t * b) (max (cm + ε * a) (cp - ε * b))).trans_lt hc'low
    linarith
  have hm' : cm < c' - ε * a := by
    have := (le_max_left (cm + ε * a) (cp - ε * b)).trans
      (le_max_right (r + t * b) (max (cm + ε * a) (cp - ε * b)))
    linarith
  have hp' : cp < c' + ε * b := by
    have := (le_max_right (cm + ε * a) (cp - ε * b)).trans
      (le_max_right (r + t * b) (max (cm + ε * a) (cp - ε * b)))
    linarith
  obtain ⟨cm', hcm'low, hcm'high⟩ := exists_between hm'
  obtain ⟨cp', hcp'low, hcp'high⟩ := exists_between hp'
  have hec := eventually_exp_bounds_of_log_tendsto hL hZ hc hc'high (show c < c + 1 by linarith)
  have hem := eventually_exp_bounds_of_log_tendsto hL hZm hcm
    (show cm - 1 < cm by linarith) hcm'low
  have hep := eventually_exp_bounds_of_log_tendsto hL hZp hcp
    (show cp - 1 < cp by linarith) hcp'low
  exact eventually_exp_le_binMass_of_laplace_bounds s w d hL hw ht hε hA hB
    (by linarith) (by linarith) hr'
    (hec.mono fun _ h ↦ h.1) (hem.mono fun _ h ↦ h.2) (hep.mono fun _ h ↦ h.2)

/-- A logarithmic Laplace limit gives every strictly larger tail exponent. -/
theorem eventually_binMass_le_exp_of_log_laplace
    (s : (n : ι) → Finset (α n)) (w d : (n : ι) → α n → ℝ)
    {L : ι → ℝ} (hL : Tendsto L ℓ atTop)
    (hw : ∀ n, ∀ i ∈ s n, 0 ≤ w n i)
    {t A B c r : ℝ} (ht : 0 ≤ t) (hr : c - t * A < r)
    (hZ : ∀ᶠ n in ℓ, 0 < laplaceSum (s n) (w n) (d n) t)
    (hc : Tendsto (fun n ↦ Real.log (laplaceSum (s n) (w n) (d n) t) / L n) ℓ (𝓝 c)) :
    ∀ᶠ n in ℓ, binMass (s n) (w n) (d n) (A * L n) (B * L n) ≤
      Real.exp (r * L n) := by
  have he := eventually_exp_bounds_of_log_tendsto hL hZ hc
    (show c - 1 < c by linarith) (show c < r + t * A by linarith)
  have hb := eventually_binMass_le_exp_of_laplace_bound s w d hw ht (A := A) (B := B)
    (he.mono fun _ h ↦ h.2)
  simpa only [add_sub_cancel_right] using hb

/-- An exponential sandwich yields positivity and the corresponding logarithmic
sandwich. This avoids using the totalized value of `log 0` as an asymptotic. -/
theorem eventually_log_bounds_of_exp_bounds {L Z : ι → ℝ}
    (hL : Tendsto L ℓ atTop) {lo hi : ℝ}
    (hlo : ∀ᶠ n in ℓ, Real.exp (lo * L n) ≤ Z n)
    (hhi : ∀ᶠ n in ℓ, Z n ≤ Real.exp (hi * L n)) :
    ∀ᶠ n in ℓ, 0 < Z n ∧ lo ≤ Real.log (Z n) / L n ∧
      Real.log (Z n) / L n ≤ hi := by
  filter_upwards [hL.eventually_gt_atTop 0, hlo, hhi] with n hLn hlow hhigh
  have hZn : 0 < Z n := (Real.exp_pos _).trans_le hlow
  exact ⟨hZn, (le_div_iff₀ hLn).mpr ((Real.le_log_iff_exp_le hZn).mpr hlow),
    (div_le_iff₀ hLn).mpr ((Real.log_le_iff_le_exp hZn).mpr hhigh)⟩

/-- A negative derivative gives a strict decrease to the right, locally. -/
theorem eventually_lt_of_hasDerivAt_neg {f : ℝ → ℝ} {f' : ℝ}
    (hf : HasDerivAt f f' 0) (hf' : f' < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε < f 0 := by
  have hh := hf.tendsto_slope_zero_right.eventually_lt_const hf'
  filter_upwards [hh, self_mem_nhdsWithin] with ε h hε
  have hε' : 0 < ε := hε
  simp only [zero_add, smul_eq_mul] at h
  have hinv : 0 < ε⁻¹ := inv_pos.mpr hε'
  nlinarith

/-- If the derivative lies strictly between two bin slopes, sufficiently nearby
tilts have the strict exponential gaps needed by the lower bound. -/
theorem exists_nearby_laplace_gaps {ψ : ℝ → ℝ} {t D a b : ℝ}
    (hψ : HasDerivAt ψ D t) (ha : a < D) (hb : D < b)
    {U : Set ℝ} (hU : IsOpen U) (htU : t ∈ U) :
    ∃ ε > 0, t - ε ∈ U ∧ t + ε ∈ U ∧
      ψ (t - ε) + ε * a < ψ t ∧ ψ (t + ε) - ε * b < ψ t := by
  have hdminus : HasDerivAt (fun ε : ℝ ↦ ψ (t - ε) + ε * a) (-D + a) 0 := by
    have hi : HasDerivAt (fun ε : ℝ ↦ t - ε) (-1) 0 := by
      convert (hasDerivAt_const 0 t).sub (hasDerivAt_id 0) using 1 <;> first | rfl | ring
    have hc := (show HasDerivAt ψ D (t - 0) by simpa using hψ).comp 0 hi
    convert hc.add ((hasDerivAt_id 0).mul_const a) using 1 <;> first | rfl | ring
  have hdplus : HasDerivAt (fun ε : ℝ ↦ ψ (t + ε) - ε * b) (D - b) 0 := by
    have hi : HasDerivAt (fun ε : ℝ ↦ t + ε) 1 0 := by
      convert (hasDerivAt_const 0 t).add (hasDerivAt_id 0) using 1 <;> first | rfl | ring
    have hc := (show HasDerivAt ψ D (t + 0) by simpa using hψ).comp 0 hi
    convert hc.sub ((hasDerivAt_id 0).mul_const b) using 1 <;> first | rfl | ring
  have hminus := eventually_lt_of_hasDerivAt_neg hdminus (by linarith)
  have hplus := eventually_lt_of_hasDerivAt_neg hdplus (by linarith)
  have hcontminus : ContinuousAt (fun ε : ℝ ↦ t - ε) 0 := continuous_const.sub continuous_id |>.continuousAt
  have hcontplus : ContinuousAt (fun ε : ℝ ↦ t + ε) 0 := continuous_const.add continuous_id |>.continuousAt
  have hmemminus : ∀ᶠ ε in 𝓝 (0 : ℝ), t - ε ∈ U :=
    hcontminus.eventually (by simpa using hU.mem_nhds htU)
  have hmemplus : ∀ᶠ ε in 𝓝 (0 : ℝ), t + ε ∈ U :=
    hcontplus.eventually (by simpa using hU.mem_nhds htU)
  have hh : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ t - ε ∈ U ∧ t + ε ∈ U ∧
      ψ (t - ε) + ε * a < ψ t ∧ ψ (t + ε) - ε * b < ψ t := by
    filter_upwards [self_mem_nhdsWithin, hmemminus.filter_mono nhdsWithin_le_nhds,
      hmemplus.filter_mono nhdsWithin_le_nhds, hminus, hplus] with ε hε hm hp hm' hp'
    exact ⟨hε, hm, hp, by simpa using hm', by simpa using hp'⟩
  exact hh.exists

end HeightPaper.Profile
