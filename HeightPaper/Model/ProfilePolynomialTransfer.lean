module

public import HeightPaper.Model.ProfileLowerTransfer
public import HeightPaper.Model.ProfileMomentDecay
public import HeightPaper.Model.EpidemicEventConditioning

/-! # Finite polynomial inputs to the lower-profile bootstrap -/

public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.Model

theorem ae_prescribedPath_active_eval (events : ℕ → Bool) (n N j : ℕ) (hj : j ≤ N)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events 1 i) :
    ∀ᵐ q ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N,
      (q.eval j).active.Nonempty := by
  filter_upwards [ae_mem_support_kernelPathLaw (fun i ↦ prescribedStep (events i)) (initial n) N]
    with q hq
  have he := mem_eventCylinder_of_prescribed_support events (initial n) N
    (by simpa only [infectious_initial] using fun i (hi : i < N) ↦ hpos i hi.le) q hq j hj
  simp only [infectious_initial] at he
  apply Finset.card_pos.mp
  change 0 < infectious (q.eval j)
  rw [he]
  exact hpos j hj

theorem prescribedPath_profile_base_lower_transfer {x p D A B δ : ℝ}
    (hx : 0 ≤ x) (hp : 0 < p) (hA : 0 < A) (hδ : 0 < δ)
    (hthreshold : 2 * B * δ ≤ 1) (events : ℕ → Bool) (n N j : ℕ) (hj : j ≤ N)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events 1 i)
    (hClower : A ≤ realNormalizer (Real.exp x) events 1 N)
    (hCupper : realNormalizer (Real.exp x) events 1 j ≤ B)
    (hmoment :
      (∫ q, ‖normalizedActiveWeight (Real.exp x : ℂ) q.last /
          prescribedNormalizer (Real.exp x : ℂ) events 1 N -
        normalizedActiveWeight (Real.exp x : ℂ) (q.eval j) /
          prescribedNormalizer (Real.exp x : ℂ) events 1 j‖ ^ p
        ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N) ≤ D) :
    (kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N).real
      {q | realNormalizedLaplace x q.last < A * δ} ≤ D / δ ^ p := by
  apply le_trans _ (prescribedPath_profile_lower_transfer hx hp hA hδ events n N j
    hClower hCupper hmoment)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ae_prescribedPath_active_eval events n N j hj hpos] with q hq
  exact fun hlow ↦ ⟨hthreshold.trans (one_le_realNormalizedLaplace hx _ hq), hlow⟩

/-- Natural-index polynomial controls imply a terminal-time-uniform power
bound for the martingale difference. -/
theorem prescribedPath_profile_moment_power_le {w p A B c a d : ℝ}
    (hw : 1 ≤ w) (hp : 1 < p) (hp2 : p ≤ 2) (hA : 0 < A) (hB : 0 ≤ B)
    (hc : 0 < c) (hd : 0 ≤ d) (hexp : d - p * (a + 1) < -1)
    (events : ℕ → Bool) (n N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events 1 i)
    (hClower : ∀ k ∈ Finset.Icc j N, A * (k : ℝ) ^ a ≤ realNormalizer w events 1 k)
    (hCupper : ∀ k ∈ Finset.Icc j N, realNormalizer (w ^ p) events 1 k ≤ B * (k : ℝ) ^ d)
    (hcount : ∀ k ∈ Finset.Icc j N, c * k ≤ (prescribedWalk events 1 k : ℝ)) :
    (∫ q, ‖normalizedActiveWeight (w : ℂ) q.last / prescribedNormalizer (w : ℂ) events 1 N -
      normalizedActiveWeight (w : ℂ) (q.eval j) / prescribedNormalizer (w : ℂ) events 1 j‖ ^ p
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N) ≤
      ((4 * (2 : ℝ) ^ p) * ((w / (A * c)) ^ p * (2 : ℝ) ^ p * B) /
        (-(d - p * (a + 1)) - 1)) * (j : ℝ) ^ (d - p * (a + 1) + 1) := by
  have hh := prescribedPath_profile_moment_polynomial_le hw hp hp2 hA hB hc hexp
    events n N j hj hjN hpos
    (fun k hk ↦ hClower (k + 1) (by have := Finset.mem_Ico.mp hk; simp; omega))
    (fun k hk ↦ (hCupper k (by have := Finset.mem_Ico.mp hk; simp; omega)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg k) (by push_cast; linarith) hd) hB))
    (fun k hk ↦ hcount (k + 1) (by have := Finset.mem_Ico.mp hk; simp; omega))
  convert hh using 1
  ring

end HeightPaper.Model
