module

public import HeightPaper.Model.AnalyticProfileProbability
public import HeightPaper.Model.PrescribedPrefix

/-!
# The canonical measurable analytic profile limit

The limit is the explicit telescoping sum along dyadic times. The same
function is used for every count word, which permits subsequent joint-law
and tail-event arguments without independent choices of analytic versions.
-/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology BigOperators ENNReal

namespace HeightPaper.Model

/-- At finite time the event word enters through a finite Boolean prefix.
This proves joint measurability without any count-word law assumption. -/
theorem measurable_prescribedNormalizedProfile_joint (s₀ : State) (J k : ℕ) (z : ℂ) :
    Measurable (fun q : (ℕ → Bool) × (ℕ → State) =>
      prescribedNormalizedProfile (Complex.exp z) q.1 s₀ J k (q.2 k)) := by
  classical
  let extend (b : Fin k → Bool) (i : ℕ) : Bool := if hi : i < k then b ⟨i, hi⟩ else false
  let f (q : (Fin k → Bool) × State) :=
    prescribedNormalizedProfile (Complex.exp z) (extend q.1) s₀ J k q.2
  have hf : Measurable f := measurable_of_countable _
  have hm : Measurable (fun q : (ℕ → Bool) × (ℕ → State) =>
      ((fun i : Fin k => q.1 i), q.2 k)) :=
    (Measurable.of_eval (fun i : Fin k =>
      (measurable_pi_apply (X := fun _ : ℕ => Bool) (i : ℕ)).comp measurable_fst)).prodMk
      ((measurable_pi_apply k).comp measurable_snd)
  convert hf.comp hm using 1
  ext q
  dsimp only [f, Function.comp_def, prescribedNormalizedProfile]
  rw [prescribedNormalizerFrom_congr_prefix (Complex.exp z) (infectious s₀) J
    (show ∀ i < k, q.1 i = extend (fun j : Fin k => q.1 j) i by
      intro i hi; simp only [extend, dite_eq_left hi]) le_rfl]

noncomputable def prescribedAnalyticSequenceLimit (events : ℕ → Bool)
    (s₀ : State) (J : ℕ) (times : ℕ → ℕ) (ω : ℕ → State) (z : ℂ) : ℂ :=
  analyticSequenceLimit (fun m ω z => prescribedNormalizedProfile (Complex.exp z)
    events s₀ J (times m) (ω (times m))) ω z

noncomputable def prescribedAnalyticProfileLimit (events : ℕ → Bool)
    (s₀ : State) (J : ℕ) (ω : ℕ → State) (z : ℂ) : ℂ :=
  prescribedAnalyticSequenceLimit events s₀ J (fun m => J + 2 ^ m) ω z

theorem measurable_prescribedAnalyticSequenceLimit_eval (events : ℕ → Bool)
    (s₀ : State) (J : ℕ) (times : ℕ → ℕ) (z : ℂ) :
    Measurable (fun ω => prescribedAnalyticSequenceLimit events s₀ J times ω z) := by
  apply measurable_analyticSequenceLimit_eval
  intro m
  exact (measurable_state (prescribedNormalizedProfile (Complex.exp z) events s₀ J (times m))).comp
    (measurable_pi_apply (X := fun _ : ℕ => State) (times m))

theorem measurable_prescribedAnalyticProfileLimit_eval (events : ℕ → Bool)
    (s₀ : State) (J : ℕ) (z : ℂ) :
    Measurable (fun ω => prescribedAnalyticProfileLimit events s₀ J ω z) :=
  measurable_prescribedAnalyticSequenceLimit_eval events s₀ J (fun m => J + 2 ^ m) z

theorem measurable_prescribedAnalyticProfileLimit_joint (s₀ : State) (J : ℕ) (z : ℂ) :
    Measurable (fun q : (ℕ → Bool) × (ℕ → State) =>
      prescribedAnalyticProfileLimit q.1 s₀ J q.2 z) := by
  unfold prescribedAnalyticProfileLimit prescribedAnalyticSequenceLimit analyticSequenceLimit
  exact (measurable_prescribedNormalizedProfile_joint s₀ J (J + 2 ^ 0) z).add
    (Measurable.tsum (fun m =>
      (measurable_prescribedNormalizedProfile_joint s₀ J (J + 2 ^ (m + 1)) z).sub
        (measurable_prescribedNormalizedProfile_joint s₀ J (J + 2 ^ m) z)))

/-- The cutoff may be any measurable natural-valued function of the event
word; it is included as a discrete argument in this joint measurable map. -/
theorem measurable_prescribedAnalyticProfileLimit_joint_cutoff (s₀ : State) (z : ℂ) :
    Measurable (fun q : ((ℕ → Bool) × (ℕ → State)) × ℕ =>
      prescribedAnalyticProfileLimit q.1.1 s₀ q.2 q.1.2 z) :=
  measurable_from_prod_countable_left (fun J =>
    measurable_prescribedAnalyticProfileLimit_joint s₀ J z)

theorem kernelTrajectory_canonical_analytic_sequence_limit
    (K : ℕ → State → PMF State) (hK : ∀ k s, (K k s).support.Finite)
    (s₀ : State) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (G : ℕ → State → ℂ → ℂ)
    (hG : ∀ k s, DifferentiableOn ℂ (G k s) (closedBall c R))
    (times : ℕ → ℕ) (htimes : Monotone times) (B : ℕ → ℝ) (hB : Summable B)
    (hbound : ∀ m z, z ∈ sphere c R →
      (∫ ω, ‖G (times (m + 1)) (ω (times (m + 1))) z -
        G (times m) (ω (times m)) z‖
        ∂FinitePMF.kernelTrajectoryMeasure K (fun _ => measurable_state _) s₀) ≤ B m) :
    ∀ᵐ ω ∂FinitePMF.kernelTrajectoryMeasure K (fun _ => measurable_state _) s₀,
        ∀ r : ℝ, 0 ≤ r → r < R →
          TendstoUniformlyOn (fun m => G (times m) (ω (times m))) (analyticSequenceLimit (fun m ω z => G (times m) (ω (times m)) z) ω)
              atTop (closedBall c r) ∧
            DifferentiableOn ℂ (analyticSequenceLimit (fun m ω z => G (times m) (ω (times m)) z) ω) (ball c r) := by
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
  apply ae_analytic_sequence_of_summable_mean_circleL1 μ c R F
    (ae_of_all μ (fun ω m => hG _ _)) hi
  exact Summable.of_nonneg_of_le
    (fun m => integral_nonneg (fun ω => circleL1_nonneg c R _)) hmean
    (hB.mul_left (2 * Real.pi))

theorem prescribedTrajectory_canonical_analytic_sequence_limit_of_moments
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
    ∀ᵐ ω ∂prescribedTrajectoryMeasure events s₀,
        ∀ r : ℝ, 0 ≤ r → r < R →
          TendstoUniformlyOn
            (fun m z => prescribedNormalizedProfile (Complex.exp z) events s₀ J
              (times m) (ω (times m))) (prescribedAnalyticSequenceLimit events s₀ J times ω) atTop (closedBall c r) ∧
            DifferentiableOn ℂ (prescribedAnalyticSequenceLimit events s₀ J times ω) (ball c r) := by
  have hG (k : ℕ) (s : State) : DifferentiableOn ℂ
      (fun z => prescribedNormalizedProfile (Complex.exp z) events s₀ J k s)
      (closedBall c R) := by
    by_cases hk : J ≤ k
    · exact differentiableOn_prescribedNormalizedProfile_exp events s₀ s J k (hC k hk)
    · apply differentiableOn_prescribedNormalizedProfile_exp events s₀ s J k
      intro z hz
      simp [prescribedNormalizerFrom, Finset.Ico_eq_empty_of_le (by omega : k ≤ J)]
  apply kernelTrajectory_canonical_analytic_sequence_limit
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

theorem prescribedTrajectory_canonical_analytic_dyadic_limit_of_moment_decay
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) (z₀ : ℂ) {R : ℝ} (hR : 0 < R)
    (hC : ∀ k ≥ J, ∀ z ∈ closedBall z₀ R,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0)
    {p D η : ℝ} (hp : 1 ≤ p) (hD : 0 ≤ D) (hη : 0 < η)
    (hbound : ∀ j k : ℕ, J ≤ j → 1 ≤ j → j ≤ k → ∀ z ∈ sphere z₀ R,
      (∫ ω, ‖prescribedNormalizedProfile (Complex.exp z) events s₀ J k (ω k) -
          prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)‖ ^ p
        ∂prescribedTrajectoryMeasure events s₀) ≤ D * (j : ℝ) ^ (-η)) :
    ∀ᵐ ω ∂prescribedTrajectoryMeasure events s₀,
        ∀ r : ℝ, 0 ≤ r → r < R →
          TendstoUniformlyOn
            (fun m z => prescribedNormalizedProfile (Complex.exp z) events s₀ J
              (J + 2 ^ m) (ω (J + 2 ^ m))) (prescribedAnalyticProfileLimit events s₀ J ω) atTop (closedBall z₀ r) ∧
            DifferentiableOn ℂ (prescribedAnalyticProfileLimit events s₀ J ω) (ball z₀ r) := by
  have htimes : Monotone (fun m : ℕ => J + 2 ^ m) := by
    intro i j hij
    exact Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) hij) J
  apply prescribedTrajectory_canonical_analytic_sequence_limit_of_moments events s₀ J
    z₀ hR (fun m => J + 2 ^ m) htimes (fun _ => Nat.le_add_right _ _) hC hp
    (fun m => D * ((2 : ℝ) ^ m) ^ (-η))
    (summable_dyadic_moment_root hD (neg_neg_of_pos hη) (lt_of_lt_of_le zero_lt_one hp))
  intro m z hz
  have hj : 1 ≤ J + 2 ^ m := Nat.one_le_two_pow.trans (Nat.le_add_left _ _)
  refine (hbound _ _ (Nat.le_add_right _ _) hj (htimes (Nat.le_succ m)) z hz).trans ?_
  apply mul_le_mul_of_nonneg_left _ hD
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hη.le)
  exact_mod_cast Nat.le_add_left (2 ^ m) J

theorem prescribedTrajectory_canonical_analytic_limit_in_probability_of_moment_decay
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) (z₀ : ℂ) {R : ℝ} (hR : 0 < R)
    (hC : ∀ k ≥ J, ∀ z ∈ closedBall z₀ R,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0)
    {p D η : ℝ} (hp : 1 ≤ p) (hD : 0 ≤ D) (hη : 0 < η)
    (hbound : ∀ j k : ℕ, J ≤ j → 1 ≤ j → j ≤ k → ∀ z ∈ sphere z₀ R,
      (∫ ω, ‖prescribedNormalizedProfile (Complex.exp z) events s₀ J k (ω k) -
          prescribedNormalizedProfile (Complex.exp z) events s₀ J j (ω j)‖ ^ p
        ∂prescribedTrajectoryMeasure events s₀) ≤ D * (j : ℝ) ^ (-η)) :
    (∀ᵐ ω ∂prescribedTrajectoryMeasure events s₀,
        ∀ r : ℝ, 0 ≤ r → r < R →
          TendstoUniformlyOn
            (fun m z => prescribedNormalizedProfile (Complex.exp z) events s₀ J
              (J + 2 ^ m) (ω (J + 2 ^ m))) (prescribedAnalyticProfileLimit events s₀ J ω) atTop (closedBall z₀ r) ∧
            DifferentiableOn ℂ (prescribedAnalyticProfileLimit events s₀ J ω) (ball z₀ r)) ∧
      ∀ r : ℝ, 0 ≤ r → r < R → ∀ ε > (0 : ℝ),
        Tendsto (fun k => (prescribedTrajectoryMeasure events s₀).real
          {ω | ∃ z ∈ closedBall z₀ r,
            ε < ‖prescribedAnalyticProfileLimit events s₀ J ω z - prescribedNormalizedProfile (Complex.exp z) events s₀ J
              (J + k) (ω (J + k))‖}) atTop (𝓝 0) := by
  have hL := prescribedTrajectory_canonical_analytic_dyadic_limit_of_moment_decay
    events s₀ J z₀ hR hC hp hD hη hbound
  refine ⟨hL, ?_⟩
  intro r hr hrR ε hε
  have ht : Tendsto (fun k : ℕ => ((J + k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun k => Nat.le_add_left k J) tendsto_id)
  have hpow : Tendsto (fun k : ℕ => (D * (((J + k : ℕ) : ℝ) ^ (-η))) ^ p⁻¹)
      atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop hη).comp ht).const_mul D
    have h' : Tendsto (fun k : ℕ => D * (((J + k : ℕ) : ℝ) ^ (-η))) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using h
    exact h'.rpow_const_nhds_zero (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hp))
  have hupper := (hpow.const_mul
    (R / (2 * Real.pi * (R - r)) * (2 * Real.pi))).div_const (ε / 2)
  simp only [mul_zero, zero_div] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact prescribedTrajectory_uniform_limit_probability_le events s₀ J z₀ hr hrR hC hp hD hη
    hbound (prescribedAnalyticProfileLimit events s₀ J) (hL.mono (fun ω hω => (hω r hr hrR).1)) (Nat.le_add_right _ _)
    (hk.trans (Nat.le_add_left _ _)) hε

end HeightPaper.Model
