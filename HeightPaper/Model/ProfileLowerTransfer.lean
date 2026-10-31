module

public import HeightPaper.Model.ProfileWindowMoments
public import HeightPaper.Model.ProfileTilt

/-!
# A finite lower-profile transfer

A lower profile at the earlier time and a small normalized martingale
difference force a lower profile at the final time. This statement retains
the earlier profile as a random variable under the same history law.
-/

public section

open MeasureTheory

namespace HeightPaper.Model

theorem normalized_profile_difference_ofReal (x : ℝ) (events : ℕ → Bool)
    (N j : ℕ) (q : FinitePath N) :
    ‖normalizedActiveWeight (Real.exp x : ℂ) q.last /
        prescribedNormalizer (Real.exp x : ℂ) events 1 N -
      normalizedActiveWeight (Real.exp x : ℂ) (q.eval j) /
        prescribedNormalizer (Real.exp x : ℂ) events 1 j‖ =
      |realNormalizedLaplace x q.last / realNormalizer (Real.exp x) events 1 N -
        realNormalizedLaplace x (q.eval j) / realNormalizer (Real.exp x) events 1 j| := by
  simp only [normalizedActiveWeight_ofReal, prescribedNormalizer_ofReal,
    ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    realNormalizedLaplace]

theorem prescribedPath_profile_lower_transfer {x p D A B δ : ℝ}
    (hx : 0 ≤ x) (hp : 0 < p) (hA : 0 < A) (hδ : 0 < δ)
    (events : ℕ → Bool) (n N j : ℕ)
    (hClower : A ≤ realNormalizer (Real.exp x) events 1 N)
    (hCupper : realNormalizer (Real.exp x) events 1 j ≤ B)
    (hmoment :
      (∫ q, ‖normalizedActiveWeight (Real.exp x : ℂ) q.last /
          prescribedNormalizer (Real.exp x : ℂ) events 1 N -
        normalizedActiveWeight (Real.exp x : ℂ) (q.eval j) /
          prescribedNormalizer (Real.exp x : ℂ) events 1 j‖ ^ p
        ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N) ≤ D) :
    (kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N).real
      {q | 2 * B * δ ≤ realNormalizedLaplace x (q.eval j) ∧
        realNormalizedLaplace x q.last < A * δ} ≤ D / δ ^ p := by
  apply (measureReal_mono ?_).trans
    (prescribedPath_profile_deviation_le_of_moment (Real.exp x : ℂ) events n N j hp hδ hmoment)
  intro q hq
  change δ ≤ ‖normalizedActiveWeight (Real.exp x : ℂ) q.last /
    prescribedNormalizer (Real.exp x : ℂ) events 1 N -
    normalizedActiveWeight (Real.exp x : ℂ) (q.eval j) /
    prescribedNormalizer (Real.exp x : ℂ) events 1 j‖
  rw [normalized_profile_difference_ofReal]
  have hw : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  have hCj : 0 < realNormalizer (Real.exp x) events 1 j :=
    zero_lt_one.trans_le (one_le_realNormalizer hw events 1 j)
  have hCN : 0 < realNormalizer (Real.exp x) events 1 N := hA.trans_le hClower
  have hj : 2 * δ ≤ realNormalizedLaplace x (q.eval j) /
      realNormalizer (Real.exp x) events 1 j := by
    apply (le_div_iff₀ hCj).mpr
    nlinarith only [hq.1, mul_le_mul_of_nonneg_right hCupper hδ.le]
  have hN : realNormalizedLaplace x q.last /
      realNormalizer (Real.exp x) events 1 N < δ := by
    apply (div_lt_iff₀ hCN).mpr
    nlinarith only [hq.2, mul_le_mul_of_nonneg_right hClower hδ.le]
  exact (by linarith : δ ≤ -(realNormalizedLaplace x q.last /
      realNormalizer (Real.exp x) events 1 N - realNormalizedLaplace x (q.eval j) /
      realNormalizer (Real.exp x) events 1 j)).trans (neg_le_abs _)

/-- A previous tilt at the cutoff controls the later tilt at the endpoint.
The only probability on the right besides the moment error is measured under
the exact prefix law. -/
theorem prescribedPath_profile_tilt_lower_transfer {x y p D A B δ H : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hp : 0 < p) (hA : 0 < A) (hδ : 0 < δ)
    (hH : 0 ≤ H) (hthreshold : 2 * B * δ ≤ H ^ (y / x))
    (events : ℕ → Bool) (n N j : ℕ) (hjN : j ≤ N)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events 1 i)
    (hClower : A ≤ realNormalizer (Real.exp y) events 1 N)
    (hCupper : realNormalizer (Real.exp y) events 1 j ≤ B)
    (hmoment :
      (∫ q, ‖normalizedActiveWeight (Real.exp y : ℂ) q.last /
          prescribedNormalizer (Real.exp y : ℂ) events 1 N -
        normalizedActiveWeight (Real.exp y : ℂ) (q.eval j) /
          prescribedNormalizer (Real.exp y : ℂ) events 1 j‖ ^ p
        ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N) ≤ D) :
    (kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N).real
      {q | realNormalizedLaplace y q.last < A * δ} ≤
      (kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) j).real
        {q | realNormalizedLaplace x q.last < H} + D / δ ^ p := by
  let μ := kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N
  have hprefix : μ.real {q | realNormalizedLaplace x (q.eval j) < H} =
      (kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) j).real
        {q | realNormalizedLaplace x q.last < H} := by
    rw [← kernelPathMeasure_map_prefixAt _ (initial n) N j hjN]
    simp only [measureReal_def]
    rw [Measure.map_apply (FinitePath.measurable _)
      (show MeasurableSet {q : FinitePath j | realNormalizedLaplace x q.last < H} from trivial)]
    rfl
  have hsub : μ.real {q | realNormalizedLaplace y q.last < A * δ} ≤
      μ.real ({q | realNormalizedLaplace x (q.eval j) < H} ∪
        {q | 2 * B * δ ≤ realNormalizedLaplace y (q.eval j) ∧
          realNormalizedLaplace y q.last < A * δ}) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [ae_mem_support_kernelPathLaw (fun i ↦ prescribedStep (events i)) (initial n) N]
      with q hq
    intro hlow
    by_cases hprior : realNormalizedLaplace x (q.eval j) < H
    · exact Or.inl hprior
    · right
      refine ⟨?_, hlow⟩
      have hprefixSupport : q.prefixAt j ∈
          (kernelPathLaw (fun i ↦ prescribedStep (events i)) (initial n) j).support := by
        rw [← kernelPathLaw_map_prefixAt _ (initial n) N j hjN]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩
      have hcount := infectious_kernelPathLaw_prescribed events (initial n) j
        (by simpa only [infectious_initial] using fun i (hi : i < j) ↦ hpos i (by omega))
        (q.prefixAt j) hprefixSupport
      simp only [FinitePath.prefixAt_last, infectious_initial] at hcount
      have ha : (q.eval j).active.Nonempty := by
        apply Finset.card_pos.mp
        change 0 < infectious (q.eval j)
        rw [hcount]
        exact hpos j hjN
      exact hthreshold.trans ((Real.rpow_le_rpow hH (le_of_not_gt hprior)
        (div_nonneg (hx.le.trans hxy) hx.le)).trans
          (realNormalizedLaplace_tilt_lower hx hxy _ ha))
  calc
    _ ≤ _ := hsub.trans ((measureReal_union_le _ _).trans (add_le_add le_rfl
      (prescribedPath_profile_lower_transfer (hx.le.trans hxy) hp hA hδ events n N j
        hClower hCupper hmoment)))
    _ = _ := by rw [hprefix]

end HeightPaper.Model
