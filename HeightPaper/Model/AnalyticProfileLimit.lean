module

public import HeightPaper.Model.InfiniteProfileLp
public import HeightPaper.Probability.AnalyticBoundarySeries
public import HeightPaper.Probability.FiniteCircleIntegral

/-!
# Analytic profile limits on the actual tree trajectory law

The finite-prefix law supplies all boundary-integrability requirements. A
summable bound on pointwise expected increments then produces one analytic
limit, uniformly on every smaller disk. The time sequence may be dyadic.
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology BigOperators ENNReal

namespace HeightPaper.Model

/-- The probability-space inclusion `Lᵖ ⊆ L¹`, with the real moment written
explicitly so it can be combined with the profile moment estimates. -/
theorem integral_norm_le_moment_root {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℂ} {p : ℝ}
    (hp : 1 ≤ p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∫ ω, ‖f ω‖ ∂μ) ≤ (∫ ω, ‖f ω‖ ^ p ∂μ) ^ p⁻¹ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hp)
  have hh := eLpNorm_le_eLpNorm_of_exponent_le (f := f) (μ := μ) hp1
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
    (hf.mono_exponent hp1),
    MemLp.eLpNorm_eq_integral_rpow_norm (by simp [hp0]) ENNReal.ofReal_ne_top hf] at hh
  simp only [ENNReal.toReal_one, inv_one, Real.rpow_one,
    ENNReal.toReal_ofReal hp0.le] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

theorem differentiable_normalizedActiveWeight_exp (s : State) :
    Differentiable ℂ (fun z => normalizedActiveWeight (Complex.exp z) s) := by
  unfold normalizedActiveWeight activeWeight
  fun_prop

theorem differentiable_prescribedNormalizerFrom_exp (events : ℕ → Bool)
    (i₀ J k : ℕ) :
    Differentiable ℂ (fun z => prescribedNormalizerFrom (Complex.exp z) events i₀ J k) := by
  unfold prescribedNormalizerFrom
  apply Differentiable.fun_finsetProd
  intro i hi
  unfold prescribedProfileFactor
  split_ifs <;> fun_prop

theorem differentiableOn_prescribedNormalizedProfile_exp (events : ℕ → Bool)
    (s₀ s : State) (J k : ℕ) {U : Set ℂ}
    (hC : ∀ z ∈ U, prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0) :
    DifferentiableOn ℂ (fun z => prescribedNormalizedProfile (Complex.exp z) events s₀ J k s) U :=
  (differentiable_normalizedActiveWeight_exp s).differentiableOn.div
    (differentiable_prescribedNormalizerFrom_exp events (infectious s₀) J k).differentiableOn hC

/-- Finite-prefix observables are integrable on the concrete infinite history law. -/
theorem kernelTrajectory_integrable_prefix {E : Type*} [NormedAddCommGroup E]
    (K : ℕ → State → PMF State) (hK : ∀ k s, (K k s).support.Finite)
    (s₀ : State) (N : ℕ) (f : FinitePath N → E) :
    Integrable (fun ω => f (trajectoryPrefix N ω))
      (FinitePMF.kernelTrajectoryMeasure K (fun _ => measurable_state _) s₀) := by
  have hi := integrable_kernelPathMeasure K hK s₀ N f
  rw [← kernelTrajectoryMeasure_map_prefix K s₀ N] at hi
  exact hi.comp_aemeasurable (measurable_trajectoryPrefix N).aemeasurable

/-- Pointwise expected increments on a surrounding circle yield a common
analytic limit for a time subsequence of the actual kernel trajectory. -/
theorem kernelTrajectory_exists_analytic_sequence_limit
    (K : ℕ → State → PMF State) (hK : ∀ k s, (K k s).support.Finite)
    (s₀ : State) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (G : ℕ → State → ℂ → ℂ)
    (hG : ∀ k s, DifferentiableOn ℂ (G k s) (closedBall c R))
    (times : ℕ → ℕ) (htimes : Monotone times) (B : ℕ → ℝ) (hB : Summable B)
    (hbound : ∀ m z, z ∈ sphere c R →
      (∫ ω, ‖G (times (m + 1)) (ω (times (m + 1))) z -
        G (times m) (ω (times m)) z‖
        ∂FinitePMF.kernelTrajectoryMeasure K (fun _ => measurable_state _) s₀) ≤ B m) :
    ∃ L : (ℕ → State) → ℂ → ℂ,
      ∀ᵐ ω ∂FinitePMF.kernelTrajectoryMeasure K (fun _ => measurable_state _) s₀,
        ∀ r : ℝ, 0 ≤ r → r < R →
          TendstoUniformlyOn (fun m => G (times m) (ω (times m))) (L ω)
              atTop (closedBall c r) ∧
            DifferentiableOn ℂ (L ω) (ball c r) := by
  let μ := FinitePMF.kernelTrajectoryMeasure K (fun _ => measurable_state _) s₀
  let F : ℕ → (ℕ → State) → ℂ → ℂ := fun m ω z => G (times m) (ω (times m)) z
  have hprefix (m : ℕ) : times m ≤ times (m + 1) := htimes (Nat.le_succ m)
  let D (m : ℕ) (q : FinitePath (times (m + 1))) (z : ℂ) : ℂ :=
    G (times (m + 1)) q.last z - G (times m) (q.eval (times m)) z
  have heq (m : ℕ) (ω : ℕ → State) (z : ℂ) :
      D m (trajectoryPrefix (times (m + 1)) ω) z = F (m + 1) ω z - F m ω z := by
    simp only [D, F, trajectoryPrefix_last, trajectoryPrefix_eval _ _ _ (hprefix m)]
  have heqfun (m : ℕ) (ω : ℕ → State) :
      D m (trajectoryPrefix (times (m + 1)) ω) =
        (fun z => F (m + 1) ω z - F m ω z) := funext (heq m ω)
  have hcont (m : ℕ) (q : FinitePath (times (m + 1))) :
      ContinuousOn (D m q) (sphere c |R|) := by
    rw [abs_of_pos hR]
    exact ((hG _ _).sub (hG _ _)).continuousOn.mono sphere_subset_closedBall
  have hi (m : ℕ) : Integrable
      (fun ω => circleL1 c R (fun z => F (m + 1) ω z - F m ω z)) μ := by
    have h := kernelTrajectory_integrable_prefix K hK s₀ (times (m + 1))
      (fun q => circleL1 c R (D m q))
    simpa only [heqfun, μ] using h
  have hmean (m : ℕ) :
      (∫ ω, circleL1 c R (fun z => F (m + 1) ω z - F m ω z) ∂μ) ≤
        (2 * Real.pi) * B m := by
    have htransfer := kernelTrajectory_integral_prefix K s₀ (times (m + 1))
      (fun q => circleL1 c R (D m q))
    simp only [heqfun] at htransfer
    dsimp only [μ]
    rw [htransfer]
    apply finitePMF_integral_circleL1_le _ (finite_support_kernelPathLaw K hK s₀ _)
      c R (D m) (fun q _ => hcont m q)
    intro z hz
    have hp := kernelTrajectory_integral_prefix K s₀ (times (m + 1))
      (fun q => ‖D m q z‖)
    simp only [heq] at hp
    change (∫ q, ‖D m q z‖ ∂kernelPathMeasure K s₀ (times (m + 1))) ≤ B m
    rw [← hp]
    exact hbound m z (by simpa [abs_of_pos hR] using hz)
  refine ⟨analyticSequenceLimit F, ?_⟩
  apply ae_analytic_sequence_of_summable_mean_circleL1 μ c R F
    (ae_of_all μ (fun ω m => hG _ _)) hi
  exact Summable.of_nonneg_of_le
    (fun m => integral_nonneg (fun ω => circleL1_nonneg c R _)) hmean
    (hB.mul_left (2 * Real.pi))

/-- A finite-positive moment bound can be supplied directly, without a
separate first-moment estimate for the boundary values. -/
theorem prescribedTrajectory_exists_analytic_sequence_limit_of_moments
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (times : ℕ → ℕ) (htimes : Monotone times)
    (hJtimes : ∀ m, J ≤ times m)
    (hC : ∀ k ≥ J, ∀ z ∈ closedBall c R,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0)
    {p : ℝ} (hp : 1 ≤ p) (B : ℕ → ℝ)
    (hB : Summable (fun m => (B m) ^ p⁻¹))
    (hbound : ∀ m z, z ∈ sphere c R →
      (∫ ω, ‖prescribedNormalizedProfile (Complex.exp z) events s₀ J
            (times (m + 1)) (ω (times (m + 1))) -
          prescribedNormalizedProfile (Complex.exp z) events s₀ J
            (times m) (ω (times m))‖ ^ p
        ∂prescribedTrajectoryMeasure events s₀) ≤ B m) :
    ∃ L : (ℕ → State) → ℂ → ℂ,
      ∀ᵐ ω ∂prescribedTrajectoryMeasure events s₀,
        ∀ r : ℝ, 0 ≤ r → r < R →
          TendstoUniformlyOn
            (fun m z => prescribedNormalizedProfile (Complex.exp z) events s₀ J
              (times m) (ω (times m))) (L ω) atTop (closedBall c r) ∧
            DifferentiableOn ℂ (L ω) (ball c r) := by
  have hG (k : ℕ) (s : State) : DifferentiableOn ℂ
      (fun z => prescribedNormalizedProfile (Complex.exp z) events s₀ J k s)
      (closedBall c R) := by
    by_cases hk : J ≤ k
    · exact differentiableOn_prescribedNormalizedProfile_exp events s₀ s J k (hC k hk)
    · apply differentiableOn_prescribedNormalizedProfile_exp events s₀ s J k
      intro z hz
      simp [prescribedNormalizerFrom, Finset.Ico_eq_empty_of_le (by omega : k ≤ J)]
  apply kernelTrajectory_exists_analytic_sequence_limit
    (fun k => prescribedStep (events k))
    (fun k s => finite_support_prescribedStep (events k) s) s₀ c hR
    (fun k s z => prescribedNormalizedProfile (Complex.exp z) events s₀ J k s)
    hG times htimes (fun m => (B m) ^ p⁻¹) hB
  intro m z hz
  have hLp (i : ℕ) : MemLp
        (fun ω => prescribedNormalizedProfile (Complex.exp z) events s₀ J
          (times i) (ω (times i)))
        (ENNReal.ofReal p) (prescribedTrajectoryMeasure events s₀) := by
      have h := prescribedTrajectory_profile_memLp (Complex.exp z) events s₀ J
        (times i - J) (lt_of_lt_of_le zero_lt_one hp)
      simpa only [Nat.add_sub_of_le (hJtimes i)] using h
  exact (integral_norm_le_moment_root _ hp ((hLp (m + 1)).sub (hLp m))).trans
      (Real.rpow_le_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))
        (hbound m z hz) (inv_nonneg.mpr (zero_le_one.trans hp)))

end HeightPaper.Model
