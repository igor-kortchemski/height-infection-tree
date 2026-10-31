module

public import HeightPaper.Probability.KernelTrajectory
public import HeightPaper.Model.ComplexProfileMoments
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Infinite prescribed-tree profile martingales

The infinite process uses Ionescu--Tulcea applied to the actual prescribed
uniform-parent kernels. The cutoff retains the random tree prefix. Count-word
positivity and normalizer conditions are explicit pathwise hypotheses; no
random-event-word convergence or complex-uniform nonvanishing is asserted.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace HeightPaper.Model

/-- One probability space carrying every prescribed-tree time. -/
noncomputable def prescribedTrajectoryMeasure (events : ℕ → Bool) (s₀ : State) :
    Measure (ℕ → State) :=
  FinitePMF.kernelTrajectoryMeasure (fun k ↦ prescribedStep (events k))
    (fun _ ↦ measurable_state _) s₀

instance prescribedTrajectoryMeasure_isProbability (events : ℕ → Bool) (s₀ : State) :
    IsProbabilityMeasure (prescribedTrajectoryMeasure events s₀) := by
  unfold prescribedTrajectoryMeasure
  infer_instance

/-- The shifted normalized profile at physical time `k`. -/
noncomputable def prescribedNormalizedProfile (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (J k : ℕ) (s : State) : ℂ :=
  normalizedActiveWeight w s / prescribedNormalizerFrom w events (infectious s₀) J k

/-- Its one-step conditional mean on every reachable state. -/
theorem prescribedNormalizedProfile_mean (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (J k : ℕ) (hJk : J ≤ k)
    (hpos : ∀ i ≤ k + 1, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizerFrom w events (infectious s₀) J (k + 1) ≠ 0)
    (s : State) (hs : s ∈ (FinitePMF.kernelEvolve (PMF.pure s₀)
      (fun i ↦ prescribedStep (events i)) k).support) :
    (∫ t, prescribedNormalizedProfile w events s₀ J (k + 1) t
      ∂(prescribedStep (events k) s).toMeasure) =
      prescribedNormalizedProfile w events s₀ J k s := by
  have hc := infectious_prescribedKernelEvolve events s₀ k
    (fun i hi ↦ hpos i (by omega)) s hs
  have hactive : s.active.Nonempty := by
    apply Finset.card_pos.mp
    change 0 < infectious s
    rw [hc]
    exact hpos k (by omega)
  have hnext : 0 < prescribedActiveCount (events k) (infectious s) := by
    rw [hc]
    exact hpos (k + 1) le_rfl
  have hfactor : prescribedProfileFactor w (events k)
      (prescribedWalk events (infectious s₀) k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hC k (Finset.mem_Ico.mpr ⟨hJk, Nat.lt_succ_self k⟩)
  unfold prescribedNormalizedProfile
  rw [integral_div, prescribedStep_normalized_integral w (events k) s hactive hnext,
    prescribedNormalizerFrom_succ w events (infectious s₀) hJk, hc]
  exact mul_div_mul_right _ _ hfactor

/-- The paper's infinite complex profile martingale on the concrete trajectory
space, with a fixed prescribed count word and a possibly nonzero cutoff. -/
theorem prescribedTrajectory_profile_martingale (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (J : ℕ)
    (hpos : ∀ i, 0 < prescribedWalk events (infectious s₀) i)
    (hC : ∀ k ≥ J, prescribedNormalizerFrom w events (infectious s₀) J k ≠ 0) :
    Martingale
      (fun n ω ↦ prescribedNormalizedProfile w events s₀ J (J + n) (ω (J + n)))
      (FinitePMF.trajectoryFiltrationFrom J) (prescribedTrajectoryMeasure events s₀) := by
  apply FinitePMF.kernelTrajectory_martingale_from
    (fun k ↦ prescribedStep (events k)) (fun _ ↦ measurable_state _)
    (fun k s ↦ finite_support_prescribedStep (events k) s) s₀ J
    (prescribedNormalizedProfile w events s₀ J) (fun _ ↦ measurable_state _)
  intro k hk s hs
  exact prescribedNormalizedProfile_mean w events s₀ J k hk (fun i _ ↦ hpos i)
    (hC (k + 1) (by omega)) s hs

/-- A complex trajectory martingale with uniformly bounded expected norms
converges almost surely, by applying the real convergence theorem to both
coordinates. This uses the actual kernel trajectory law. -/
theorem kernelTrajectory_complex_ae_tendsto_of_integral_norm_bdd
    (K : ℕ → State → PMF State) (hK : ∀ k s, (K k s).support.Finite)
    (s₀ : State) (J : ℕ) (F : ℕ → State → ℂ)
    (hmean : ∀ k, J ≤ k → ∀ s, s ∈ (FinitePMF.kernelEvolve (PMF.pure s₀) K k).support →
      (∫ t, F (k + 1) t ∂(K k s).toMeasure) = F k s)
    (B : ℝ)
    (hbdd : ∀ n, (∫ s, ‖F (J + n) s‖
      ∂(FinitePMF.kernelEvolve (PMF.pure s₀) K (J + n)).toMeasure) ≤ B) :
    ∀ᵐ ω ∂FinitePMF.kernelTrajectoryMeasure K (fun _ ↦ measurable_state _) s₀,
      ∃ c : ℂ, Tendsto (fun n ↦ F (J + n) (ω (J + n))) atTop (𝓝 c) := by
  let μ := FinitePMF.kernelTrajectoryMeasure K (fun _ ↦ measurable_state _) s₀
  have hcoord (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, |L z| ≤ ‖z‖) :
      ∀ᵐ ω ∂μ, ∃ c : ℝ,
        Tendsto (fun n ↦ L (F (J + n) (ω (J + n)))) atTop (𝓝 c) := by
    have hm : Martingale (fun n ω ↦ L (F (J + n) (ω (J + n))))
        (FinitePMF.trajectoryFiltrationFrom J) μ := by
      apply FinitePMF.kernelTrajectory_martingale_from K (fun _ ↦ measurable_state _)
        hK s₀ J (fun k s ↦ L (F k s)) (fun _ ↦ measurable_state _)
      intro k hk s hs
      rw [L.integral_comp_comm (FinitePMF.integrable_of_finite_support _ (hK k s) _),
        hmean k hk s hs]
    apply hm.submartingale.exists_ae_tendsto_of_bdd (R := Real.toNNReal B)
    intro n
    have hint := FinitePMF.kernelTrajectory_integrable_eval K
      (fun _ ↦ measurable_state _) hK s₀ (J + n) (fun s ↦ L (F (J + n) s))
    rw [eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hint]
    change ENNReal.ofReal _ ≤ ENNReal.ofReal B
    apply ENNReal.ofReal_le_ofReal
    rw [FinitePMF.kernelTrajectory_integral_eval K (fun _ ↦ measurable_state _) s₀
      (J + n) (fun s ↦ ‖L (F (J + n) s)‖) (measurable_state _)]
    refine le_trans ?_ (hbdd n)
    apply integral_mono
      (FinitePMF.integrable_of_finite_support _
        (FinitePMF.kernelEvolve_support_finite _ K (by simp) hK _) _)
      (FinitePMF.integrable_of_finite_support _
        (FinitePMF.kernelEvolve_support_finite _ K (by simp) hK _) _)
    intro s
    exact hL _
  have hre := hcoord RCLike.reCLM RCLike.abs_re_le_norm
  have him := hcoord RCLike.imCLM RCLike.abs_im_le_norm
  filter_upwards [hre, him] with ω hωre hωim
  obtain ⟨r, hr⟩ := hωre
  obtain ⟨i, hi⟩ := hωim
  refine ⟨(r : ℂ) + (i : ℂ) * Complex.I, ?_⟩
  have h := ((Complex.continuous_ofReal.tendsto r).comp hr).add
    (((Complex.continuous_ofReal.tendsto i).comp hi).mul_const Complex.I)
  simpa only [RCLike.reCLM_apply, RCLike.imCLM_apply, RCLike.re_eq_complex_re,
    RCLike.im_eq_complex_im, Function.comp_def, Complex.re_add_im] using h

/-- A coordinate integral can be computed on any finite history containing it. -/
theorem kernelEvolve_integral_eq_path_eval (K : ℕ → State → PMF State)
    (s₀ : State) (N k : ℕ) (hk : k ≤ N) (f : State → ℝ) :
    (∫ s, f s ∂(FinitePMF.kernelEvolve (PMF.pure s₀) K k).toMeasure) =
      ∫ q, f (q.eval k) ∂kernelPathMeasure K s₀ N := by
  rw [← kernelPathMeasure_map_eval K s₀ N k hk,
    integral_map_of_stronglyMeasurable (FinitePath.measurable _)
      (measurable_state f).stronglyMeasurable]

/-- The finite p-moment difference estimate gives an L¹ bound with the entire
random cutoff profile retained. -/
theorem prescribedPath_profile_norm_integral_le (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N J : ℕ) (hJN : J ≤ N) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizerFrom w events (infectious s₀) J N ≠ 0) :
    (∫ q, ‖prescribedNormalizedProfile w events s₀ J N q.last‖
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N) ≤
      1 + (4 * (2 : ℝ) ^ p) *
        ∑ k ∈ Finset.Ico J N, prescribedShiftedMomentBound w events s₀ J p k +
      ∫ q, ‖normalizedActiveWeight w q.last‖
        ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ J := by
  let K := fun i ↦ prescribedStep (events i)
  have hK : ∀ k s, (K k s).support.Finite :=
    fun k s ↦ finite_support_prescribedStep (events k) s
  have hm := prescribedPath_shifted_profile_moment_le w events s₀ N J hJN hp hp2 hpos hC
  have hx (x : ℝ) (hx0 : 0 ≤ x) : x ≤ 1 + x ^ p := by
    by_cases hx1 : x ≤ 1
    · linarith [Real.rpow_nonneg hx0 p]
    · have hr := Real.self_le_rpow_of_one_le (le_of_not_ge hx1) hp.le
      linarith
  have hpoint (q : FinitePath N) :
      ‖prescribedNormalizedProfile w events s₀ J N q.last‖ ≤
        (1 + ‖prescribedNormalizedProfile w events s₀ J N q.last -
          normalizedActiveWeight w (q.eval J)‖ ^ p) +
        ‖normalizedActiveWeight w (q.eval J)‖ := by
    have hn := norm_le_norm_sub_add
      (prescribedNormalizedProfile w events s₀ J N q.last)
      (normalizedActiveWeight w (q.eval J))
    have hr := hx ‖prescribedNormalizedProfile w events s₀ J N q.last -
      normalizedActiveWeight w (q.eval J)‖ (norm_nonneg _)
    linarith
  have hprefix : (∫ q, ‖normalizedActiveWeight w (q.eval J)‖ ∂kernelPathMeasure K s₀ N) =
      ∫ q, ‖normalizedActiveWeight w q.last‖ ∂kernelPathMeasure K s₀ J := by
    simpa only [FinitePath.prefixAt_last] using kernelPathMeasure_integral_prefixAt K s₀ N J hJN
      (fun q ↦ ‖normalizedActiveWeight w q.last‖)
  calc
    _ ≤ ∫ q, (1 + ‖prescribedNormalizedProfile w events s₀ J N q.last -
        normalizedActiveWeight w (q.eval J)‖ ^ p) + ‖normalizedActiveWeight w (q.eval J)‖
        ∂kernelPathMeasure K s₀ N :=
      integral_mono (integrable_kernelPathMeasure K hK s₀ N _)
        (integrable_kernelPathMeasure K hK s₀ N _) hpoint
    _ = 1 + (∫ q, ‖prescribedNormalizedProfile w events s₀ J N q.last -
        normalizedActiveWeight w (q.eval J)‖ ^ p ∂kernelPathMeasure K s₀ N) +
        ∫ q, ‖normalizedActiveWeight w q.last‖ ∂kernelPathMeasure K s₀ J := by
      rw [integral_add (integrable_kernelPathMeasure K hK s₀ N _)
        (integrable_kernelPathMeasure K hK s₀ N _),
        integral_add (integrable_kernelPathMeasure K hK s₀ N _)
          (integrable_kernelPathMeasure K hK s₀ N _), hprefix]
      simp
    _ ≤ _ := by
      dsimp only [prescribedNormalizedProfile, K]
      linarith [hm]

/-- The explicit increment bound is nonnegative after the cutoff, since it
bounds an actual nonnegative expected moment. -/
theorem prescribedShiftedMomentBound_nonneg (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (J k : ℕ) (hJk : J ≤ k) {p : ℝ} (hp : 1 ≤ p)
    (hpos : ∀ i ≤ k + 1, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizerFrom w events (infectious s₀) J (k + 1) ≠ 0) :
    0 ≤ prescribedShiftedMomentBound w events s₀ J p k := by
  have h := prescribedPath_shifted_increment_moment_le w events s₀ (k + 1) J k
    hJk (Nat.lt_succ_self k) hp hpos hC
  exact (integral_nonneg (fun _ ↦ integral_nonneg (fun _ ↦
    Real.rpow_nonneg (norm_nonneg _) p))).trans h

/-- Summability of the explicit count-word increment bound proves almost-sure
pointwise convergence of the actual infinite complex profile martingale.
This is the conditional-on-the-word convergence step in the paper. -/
theorem prescribedTrajectory_profile_ae_tendsto_of_summable (w : ℂ)
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hpos : ∀ i, 0 < prescribedWalk events (infectious s₀) i)
    (hC : ∀ k ≥ J, prescribedNormalizerFrom w events (infectious s₀) J k ≠ 0)
    (hsum : Summable (fun i ↦ prescribedShiftedMomentBound w events s₀ J p (J + i))) :
    ∀ᵐ ω ∂prescribedTrajectoryMeasure events s₀,
      ∃ c : ℂ, Tendsto
        (fun n ↦ prescribedNormalizedProfile w events s₀ J (J + n) (ω (J + n)))
        atTop (𝓝 c) := by
  apply kernelTrajectory_complex_ae_tendsto_of_integral_norm_bdd
    (fun i ↦ prescribedStep (events i))
    (fun i s ↦ finite_support_prescribedStep (events i) s) s₀ J
    (prescribedNormalizedProfile w events s₀ J)
    (fun k hk s hs ↦ prescribedNormalizedProfile_mean w events s₀ J k hk
      (fun i _ ↦ hpos i) (hC (k + 1) (by omega)) s hs)
    (1 + (4 * (2 : ℝ) ^ p) *
      (∑' i, prescribedShiftedMomentBound w events s₀ J p (J + i)) +
      ∫ q, ‖normalizedActiveWeight w q.last‖
        ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ J)
  intro n
  rw [kernelEvolve_integral_eq_path_eval _ s₀ (J + n) (J + n) le_rfl]
  simp only [FinitePath.eval_last]
  have hh := prescribedPath_profile_norm_integral_le w events s₀ (J + n) J
    (Nat.le_add_right J n) hp hp2 (fun i _ ↦ hpos i)
    (hC (J + n) (Nat.le_add_right J n))
  refine hh.trans ?_
  have hs : (∑ k ∈ Finset.Ico J (J + n), prescribedShiftedMomentBound w events s₀ J p k) ≤
      ∑' i, prescribedShiftedMomentBound w events s₀ J p (J + i) := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    exact hsum.sum_le_tsum (Finset.range n) (fun i _ ↦
      prescribedShiftedMomentBound_nonneg w events s₀ J (J + i) (Nat.le_add_right J i)
        hp.le (fun k _ ↦ hpos k) (hC (J + i + 1) (by omega)))
  have hmul := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4 * (2 : ℝ) ^ p)
  linarith

/-- The almost-sure pointwise limit can be chosen as a measurable complex
random variable on the same infinite history space. -/
theorem prescribedTrajectory_exists_measurable_profile_limit (w : ℂ)
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hpos : ∀ i, 0 < prescribedWalk events (infectious s₀) i)
    (hC : ∀ k ≥ J, prescribedNormalizerFrom w events (infectious s₀) J k ≠ 0)
    (hsum : Summable (fun i ↦ prescribedShiftedMomentBound w events s₀ J p (J + i))) :
    ∃ M : (ℕ → State) → ℂ, Measurable M ∧
      ∀ᵐ ω ∂prescribedTrajectoryMeasure events s₀,
        Tendsto (fun n ↦ prescribedNormalizedProfile w events s₀ J (J + n) (ω (J + n)))
          atTop (𝓝 (M ω)) := by
  have hf (n : ℕ) : Measurable (fun ω : ℕ → State ↦
      prescribedNormalizedProfile w events s₀ J (J + n) (ω (J + n))) :=
    (measurable_state (prescribedNormalizedProfile w events s₀ J (J + n))).comp
      (measurable_pi_apply (X := fun _ : ℕ ↦ State) (J + n))
  exact measurable_limit_of_tendsto_metrizable_ae (fun n ↦ (hf n).aemeasurable)
    (prescribedTrajectory_profile_ae_tendsto_of_summable w events s₀ J hp hp2 hpos hC hsum)

/-- The source's count and product power bounds imply summability of the actual
complex increment bound whenever its exponent is strictly below minus one. -/
theorem prescribedShiftedMomentBound_summable_of_polynomial {w : ℂ}
    {p A B c a b : ℝ} (hw : 1 ≤ ‖w‖) (hp : 1 < p)
    (hA : 0 < A) (hB : 0 ≤ B) (hc : 0 < c) (hexp : b - p * (a + 1) < -1)
    (events : ℕ → Bool) (n J : ℕ)
    (hpos : ∀ i, 0 < prescribedWalk events 1 i)
    (hC : ∀ k ≥ J, prescribedNormalizerFrom w events 1 J k ≠ 0)
    (hClower : ∀ k ≥ J,
      A * ((k + 1 : ℕ) : ℝ) ^ a ≤ ‖prescribedNormalizerFrom w events 1 J (k + 1)‖)
    (hCupper : ∀ k ≥ J,
      realNormalizer (‖w‖ ^ p) events 1 k ≤ B * ((k + 1 : ℕ) : ℝ) ^ b)
    (hcount : ∀ k ≥ J, c * (k + 1 : ℕ) ≤ (prescribedWalk events 1 (k + 1) : ℝ)) :
    Summable (fun i ↦ prescribedShiftedMomentBound w events (initial n) J p (J + i)) := by
  have hp0 : 0 ≤ p := by linarith
  have hwp : 1 ≤ ‖w‖ ^ p := Real.one_le_rpow hw hp0
  have hnonneg (i : ℕ) :
      0 ≤ prescribedShiftedMomentBound w events (initial n) J p (J + i) := by
    apply prescribedShiftedMomentBound_nonneg w events (initial n) J (J + i)
      (Nat.le_add_right J i) hp.le
    · simpa only [infectious_initial] using (fun k (_ : k ≤ J + i + 1) ↦ hpos k)
    · simpa only [infectious_initial] using hC (J + i + 1) (by omega)
  have hbound (i : ℕ) :
      prescribedShiftedMomentBound w events (initial n) J p (J + i) ≤
        ((‖w‖ / (A * c)) ^ p * (2 : ℝ) ^ p * B) *
          ((J + i + 1 : ℕ) : ℝ) ^ (b - p * (a + 1)) := by
    apply (prescribedShiftedMomentBound_complex_le w hw hp0 events n J (J + i)
      (Nat.le_add_right J i) (hpos (J + i + 1))).trans
    exact profile_moment_ratio_le (norm_nonneg w) hp0 hA hB hc (by positivity)
      (zero_le_one.trans (one_le_realNormalizer hwp events 1 (J + i)))
      (hClower (J + i) (Nat.le_add_right J i))
      (hcount (J + i) (Nat.le_add_right J i))
      (hCupper (J + i) (Nat.le_add_right J i))
  have hpow := (Real.summable_nat_rpow.mpr hexp).comp_injective
    (show Function.Injective (fun i : ℕ ↦ J + i + 1) from fun i j h ↦ by dsimp at h; omega)
  exact Summable.of_nonneg_of_le hnonneg hbound
    (hpow.mul_left ((‖w‖ / (A * c)) ^ p * (2 : ℝ) ^ p * B))

/-- The paper's pointwise infinite-profile convergence step, with count-word
power bounds explicitly supplied rather than stochastic bounds assumed. -/
theorem prescribedTrajectory_exists_profile_limit_of_polynomial {w : ℂ}
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
      ∀ᵐ ω ∂prescribedTrajectoryMeasure events (initial n),
        Tendsto (fun k ↦ prescribedNormalizedProfile w events (initial n) J (J + k) (ω (J + k)))
          atTop (𝓝 (M ω)) := by
  apply prescribedTrajectory_exists_measurable_profile_limit w events (initial n) J hp hp2
  · simpa only [infectious_initial] using hpos
  · simpa only [infectious_initial] using hC
  · exact prescribedShiftedMomentBound_summable_of_polynomial hw hp hA hB hc hexp
      events n J hpos hC hClower hCupper hcount

/-- Fatou's lemma upgrades an almost-sure limit and uniform finite p-moment
Cauchy tails to convergence in the same Lp space. -/
theorem lp_convergence_of_ae_tendsto_moment_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {f : ℕ → Ω → ℂ} {M : Ω → ℂ} {p : ℝ} (hp : 0 < p)
    (hf : ∀ n, MemLp (f n) (ENNReal.ofReal p) μ) (hM : Measurable M)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (𝓝 (M ω)))
    (T : ℕ → ℝ) (hT : Tendsto T atTop (𝓝 0))
    (hbound : ∀ n m, n ≤ m → (∫ ω, ‖f m ω - f n ω‖ ^ p ∂μ) ≤ T n) :
    MemLp M (ENNReal.ofReal p) μ ∧
      Tendsto (fun n ↦ eLpNorm (f n - M) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp [hp]
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have htail (n : ℕ) : eLpNorm (M - f n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal ((T n) ^ p⁻¹) := by
    apply Lp.eLpNorm_le_of_ae_tendsto
      (u := atTop) (f := fun m ↦ f m - f n)
    · filter_upwards [eventually_ge_atTop n] with m hm
      rw [MemLp.eLpNorm_eq_integral_rpow_norm hp0 hptop ((hf m).sub (hf n)),
        ENNReal.toReal_ofReal hp.le]
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow
        (integral_nonneg (fun ω ↦ Real.rpow_nonneg (norm_nonneg _) p))
        (hbound n m hm) (inv_nonneg.mpr hp.le)
    · intro m
      exact (hf m).aestronglyMeasurable.sub (hf n).aestronglyMeasurable
    · exact hM.aestronglyMeasurable.sub (hf n).aestronglyMeasurable
    · filter_upwards [hlim] with ω hω
      exact hω.sub_const (f n ω)
  have hdiff : MemLp (M - f 0) (ENNReal.ofReal p) μ :=
    (htail 0).trans_lt ENNReal.ofReal_lt_top
  constructor
  · simpa only [sub_add_cancel] using hdiff.add (hf 0)
  · have ht : Tendsto (fun n ↦ ENNReal.ofReal ((T n) ^ p⁻¹)) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (hT.rpow_const_nhds_zero (inv_pos.mpr hp))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ ↦ bot_le)
    intro n
    change eLpNorm (f n - M) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ((T n) ^ p⁻¹)
    rw [eLpNorm_sub_comm]
    exact htail n

/-- Every finite-time profile lies in every finite positive Lp space because
its coordinate marginal has finite support. -/
theorem prescribedTrajectory_profile_memLp (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (J n : ℕ) {p : ℝ} (hp : 0 < p) :
    MemLp (fun ω ↦ prescribedNormalizedProfile w events s₀ J (J + n) (ω (J + n)))
      (ENNReal.ofReal p) (prescribedTrajectoryMeasure events s₀) := by
  have hf : Measurable (fun ω : ℕ → State ↦
      prescribedNormalizedProfile w events s₀ J (J + n) (ω (J + n))) :=
    (measurable_state (prescribedNormalizedProfile w events s₀ J (J + n))).comp
      (measurable_pi_apply (X := fun _ : ℕ ↦ State) (J + n))
  apply (integrable_norm_rpow_iff hf.aestronglyMeasurable (by simp [hp])
    ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hp.le, prescribedTrajectoryMeasure] using
    FinitePMF.kernelTrajectory_integrable_eval (fun i ↦ prescribedStep (events i))
      (fun _ ↦ measurable_state _) (fun i s ↦ finite_support_prescribedStep (events i) s)
      s₀ (J + n) (fun s ↦ ‖prescribedNormalizedProfile w events s₀ J (J + n) s‖ ^ p)

end HeightPaper.Model
