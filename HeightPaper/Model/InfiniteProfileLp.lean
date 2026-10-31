module

public import HeightPaper.Model.InfiniteProfile
public import HeightPaper.Model.KernelTrajectoryPrefix

/-!
# Lp limits of the infinite prescribed-tree profile

The exact finite-prefix marginal transfers the paper's finite moment-difference
bounds to the infinite history space. Fatou's lemma then yields convergence in
the same Lp space, under summability of the explicit count-word increment bound.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace HeightPaper.Model

/-- The finite p-moment difference estimate holds on the actual infinite law,
with both times evaluated on the same infinite trajectory. -/
theorem prescribedTrajectory_profile_moment_sub_le (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N J j : ℕ) (hJj : J ≤ j) (hjN : j ≤ N)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizerFrom w events (infectious s₀) J N ≠ 0) :
    (∫ ω, ‖prescribedNormalizedProfile w events s₀ J N (ω N) -
      prescribedNormalizedProfile w events s₀ J j (ω j)‖ ^ p
        ∂prescribedTrajectoryMeasure events s₀) ≤
      (4 * (2 : ℝ) ^ p) *
        ∑ k ∈ Finset.Ico j N, prescribedShiftedMomentBound w events s₀ J p k := by
  have heq := kernelTrajectory_integral_prefix (fun i ↦ prescribedStep (events i)) s₀ N
    (fun q ↦ ‖prescribedNormalizedProfile w events s₀ J N q.last -
      prescribedNormalizedProfile w events s₀ J j (q.eval j)‖ ^ p)
  have hm := prescribedPath_complex_moment_sub_le w events s₀ N J j hJj hjN hp hp2 hpos hC
  calc
    _ = ∫ q, ‖prescribedNormalizedProfile w events s₀ J N q.last -
        prescribedNormalizedProfile w events s₀ J j (q.eval j)‖ ^ p
          ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N := by
      simpa only [trajectoryPrefix_last, trajectoryPrefix_eval N _ j hjN,
        prescribedTrajectoryMeasure] using heq
    _ ≤ _ := by simpa only [prescribedNormalizedProfile] using hm

/-- First moments obey the same history estimate by a direct triangle sum. -/
theorem prescribedTrajectory_profile_moment_sub_le_one (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N J j : ℕ) (hJj : J ≤ j) (hjN : j ≤ N)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizerFrom w events (infectious s₀) J N ≠ 0) :
    (∫ ω, ‖prescribedNormalizedProfile w events s₀ J N (ω N) -
      prescribedNormalizedProfile w events s₀ J j (ω j)‖ ^ (1 : ℝ)
        ∂prescribedTrajectoryMeasure events s₀) ≤
      ∑ k ∈ Finset.Ico j N, prescribedShiftedMomentBound w events s₀ J 1 k := by
  have heq := kernelTrajectory_integral_prefix (fun i ↦ prescribedStep (events i)) s₀ N
    (fun q ↦ ‖prescribedNormalizedProfile w events s₀ J N q.last -
      prescribedNormalizedProfile w events s₀ J j (q.eval j)‖)
  have hm := prescribedPath_complex_moment_sub_le_one w events s₀ N J j hJj hjN hpos hC
  calc
    _ = ∫ q, ‖prescribedNormalizedProfile w events s₀ J N q.last -
        prescribedNormalizedProfile w events s₀ J j (q.eval j)‖
          ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N := by
      simpa only [Real.rpow_one, trajectoryPrefix_last, trajectoryPrefix_eval N _ j hjN,
        prescribedTrajectoryMeasure] using heq
    _ ≤ _ := by simpa only [prescribedNormalizedProfile] using hm

/-- The full closed moment-order interval, including its first-moment endpoint. -/
theorem prescribedTrajectory_profile_moment_sub_le_all (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N J j : ℕ) (hJj : J ≤ j) (hjN : j ≤ N)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizerFrom w events (infectious s₀) J N ≠ 0) :
    (∫ ω, ‖prescribedNormalizedProfile w events s₀ J N (ω N) -
      prescribedNormalizedProfile w events s₀ J j (ω j)‖ ^ p
        ∂prescribedTrajectoryMeasure events s₀) ≤
      (4 * (2 : ℝ) ^ p) *
        ∑ k ∈ Finset.Ico j N, prescribedShiftedMomentBound w events s₀ J p k := by
  by_cases hpeq : p = 1
  · subst p
    have hh := prescribedTrajectory_profile_moment_sub_le_one w events s₀ N J j
      hJj hjN hpos hC
    have hnonneg : 0 ≤ ∑ k ∈ Finset.Ico j N,
        prescribedShiftedMomentBound w events s₀ J 1 k :=
      (integral_nonneg (fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)).trans hh
    simpa only [Real.rpow_one] using hh.trans (by nlinarith :
      (∑ k ∈ Finset.Ico j N, prescribedShiftedMomentBound w events s₀ J 1 k) ≤
      (4 * (2 : ℝ) ^ (1 : ℝ)) *
        ∑ k ∈ Finset.Ico j N, prescribedShiftedMomentBound w events s₀ J 1 k)
  · exact prescribedTrajectory_profile_moment_sub_le w events s₀ N J j hJj hjN
      (lt_of_le_of_ne hp (Ne.symm hpeq)) hp2 hpos hC

/-- Almost-sure and Lp convergence to one measurable limit, with no extra
hypothesis on that limit and with the actual infinite tree-history law. -/
theorem prescribedTrajectory_exists_profile_lp_limit (w : ℂ)
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hpos : ∀ i, 0 < prescribedWalk events (infectious s₀) i)
    (hC : ∀ k ≥ J, prescribedNormalizerFrom w events (infectious s₀) J k ≠ 0)
    (hsum : Summable (fun i ↦ prescribedShiftedMomentBound w events s₀ J p (J + i))) :
    ∃ M : (ℕ → State) → ℂ, Measurable M ∧
      MemLp M (ENNReal.ofReal p) (prescribedTrajectoryMeasure events s₀) ∧
      (∀ᵐ ω ∂prescribedTrajectoryMeasure events s₀,
        Tendsto (fun n ↦ prescribedNormalizedProfile w events s₀ J (J + n) (ω (J + n)))
          atTop (𝓝 (M ω))) ∧
      Tendsto (fun n ↦ eLpNorm
        ((fun ω ↦ prescribedNormalizedProfile w events s₀ J (J + n) (ω (J + n))) - M)
        (ENNReal.ofReal p) (prescribedTrajectoryMeasure events s₀)) atTop (𝓝 0) := by
  obtain ⟨M, hM, hlim⟩ := prescribedTrajectory_exists_measurable_profile_limit w events s₀ J
    hp hp2 hpos hC hsum
  let B : ℕ → ℝ := fun k ↦ prescribedShiftedMomentBound w events s₀ J p k
  let T : ℕ → ℝ := fun n ↦ (4 * (2 : ℝ) ^ p) * ∑' i, B (J + (n + i))
  have ht : Tendsto (fun n ↦ ∑' i, B (J + (n + i))) atTop (𝓝 0) := by
    have h := tendsto_sum_nat_add (fun i ↦ B (J + i))
    convert h using 1
    funext n
    apply tsum_congr
    intro i
    congr 1
    omega
  have hT : Tendsto T atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul (4 * (2 : ℝ) ^ p)
  have hLp := lp_convergence_of_ae_tendsto_moment_tail (prescribedTrajectoryMeasure events s₀)
    (f := fun k ω ↦ prescribedNormalizedProfile w events s₀ J (J + k) (ω (J + k)))
    (M := M) (p := p) (by linarith : 0 < p)
    (fun n ↦ prescribedTrajectory_profile_memLp w events s₀ J n (by linarith))
    hM hlim T hT (fun n m hnm ↦ ?_)
  · exact ⟨M, hM, hLp.1, hlim, hLp.2⟩
  · have hm := prescribedTrajectory_profile_moment_sub_le w events s₀ (J + m) J (J + n)
      (Nat.le_add_right J n) (Nat.add_le_add_left hnm J) hp hp2
      (fun i _ ↦ hpos i) (hC (J + m) (Nat.le_add_right J m))
    refine hm.trans ?_
    change (4 * (2 : ℝ) ^ p) * _ ≤ (4 * (2 : ℝ) ^ p) * _
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 4 * (2 : ℝ) ^ p)
    rw [Finset.sum_Ico_eq_sum_range]
    have hs := hsum.comp_injective
      (show Function.Injective (fun i : ℕ ↦ n + i) from fun i j h ↦ by dsimp at h; omega)
    have hb (i : ℕ) : 0 ≤ B (J + (n + i)) :=
      prescribedShiftedMomentBound_nonneg w events s₀ J (J + (n + i)) (by omega) hp.le
        (fun k _ ↦ hpos k) (hC (J + (n + i) + 1) (by omega))
    simpa only [B, Nat.add_assoc] using
      hs.sum_le_tsum (Finset.range ((J + m) - (J + n))) (fun i _ ↦ hb i)

/-- Explicit count and product power bounds discharge the summability hypothesis
of the infinite-profile almost-sure and Lp convergence theorem. -/
theorem prescribedTrajectory_exists_profile_lp_limit_of_polynomial {w : ℂ}
    {p A B c a b : ℝ} (hw : 1 ≤ ‖w‖) (hp : 1 < p) (hp2 : p ≤ 2)
    (hA : 0 < A) (hB : 0 ≤ B) (hc : 0 < c) (hexp : b - p * (a + 1) < -1)
    (events : ℕ → Bool) (n J : ℕ)
    (hpos : ∀ i, 0 < prescribedWalk events 1 i)
    (hC : ∀ k ≥ J, prescribedNormalizerFrom w events 1 J k ≠ 0)
    (hClower : ∀ k ≥ J,
      A * ((k + 1 : ℕ) : ℝ) ^ a ≤ ‖prescribedNormalizerFrom w events 1 J (k + 1)‖)
    (hCupper : ∀ k ≥ J,
      realNormalizer (‖w‖ ^ p) events 1 k ≤ B * ((k + 1 : ℕ) : ℝ) ^ b)
    (hcount : ∀ k ≥ J, c * (k + 1 : ℕ) ≤ (prescribedWalk events 1 (k + 1) : ℝ)) :
    ∃ M : (ℕ → State) → ℂ, Measurable M ∧
      MemLp M (ENNReal.ofReal p) (prescribedTrajectoryMeasure events (initial n)) ∧
      (∀ᵐ ω ∂prescribedTrajectoryMeasure events (initial n),
        Tendsto (fun k ↦ prescribedNormalizedProfile w events (initial n) J (J + k) (ω (J + k)))
          atTop (𝓝 (M ω))) ∧
      Tendsto (fun k ↦ eLpNorm
        ((fun ω ↦ prescribedNormalizedProfile w events (initial n) J (J + k) (ω (J + k))) - M)
        (ENNReal.ofReal p) (prescribedTrajectoryMeasure events (initial n)))
        atTop (𝓝 0) := by
  apply prescribedTrajectory_exists_profile_lp_limit w events (initial n) J hp hp2
  · simpa only [infectious_initial] using hpos
  · simpa only [infectious_initial] using hC
  · exact prescribedShiftedMomentBound_summable_of_polynomial hw hp hA hB hc hexp
      events n J hpos hC hClower hCupper hcount

end HeightPaper.Model
