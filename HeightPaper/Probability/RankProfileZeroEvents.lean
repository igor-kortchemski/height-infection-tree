module

public import HeightPaper.Model.RankDepthReset
public import HeightPaper.Probability.UniformParentLaw
public import HeightPaper.Probability.UniformTailZeroOne
public import HeightPaper.Probability.CompactZeroEvents
public import HeightPaper.Model.ComplexNormalizer

/-!
# Compact profile zero events on the actual parent-uniform space

The normalizing denominator depends only on the prescribed event word.
Resetting the active depths at any finite time changes positive-real profiles
by finite multiplicative factors. Compact infimum convergence is therefore a
literal tail event of the independent parent uniforms.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace HeightPaper.Model

noncomputable def profileRealDenominator (events : ℕ → Bool) (i₀ J k : ℕ) (x : ℝ) : ℝ :=
  (prescribedWalk events i₀ k : ℝ) * realNormalizerFrom (Real.exp x) events i₀ J k

noncomputable def rankProfileAtReal (events : ℕ → Bool) (s₀ : State) (J : ℕ)
    (u : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  prescribedNormalizedProfile (Complex.exp (x : ℂ)) events s₀ J k (rankState events s₀ u k)

noncomputable def rankResetProfileAtReal (events : ℕ → Bool) (i₀ J N : ℕ)
    (u : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  ((depthWeight (Real.exp x) (rankResetDepths events i₀ N u (k - N)) /
    profileRealDenominator events i₀ J k x : ℝ) : ℂ)

theorem profileRealDenominator_pos (events : ℕ → Bool) (i₀ J k : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (hpos : 0 < prescribedWalk events i₀ k) :
    0 < profileRealDenominator events i₀ J k x :=
  mul_pos (by exact_mod_cast hpos) (realNormalizerFrom_pos (Real.one_le_exp_iff.mpr hx) _ _ _ _)

theorem rankProfileAtReal_eq_ofReal (events : ℕ → Bool) (s₀ : State) (J : ℕ)
    (u : ℕ → ℝ) (k : ℕ) (x : ℝ)
    (hpos : ∀ j < k, 0 < prescribedWalk events (infectious s₀) j) :
    rankProfileAtReal events s₀ J u k x =
      ((activeWeight (Real.exp x) (rankState events s₀ u k) /
        profileRealDenominator events (infectious s₀) J k x : ℝ) : ℂ) := by
  rw [rankProfileAtReal, ← Complex.ofReal_exp, prescribedNormalizedProfile,
    normalizedActiveWeight_ofReal, prescribedNormalizerFrom_ofReal,
    ← Complex.ofReal_div, infectious_rankState events s₀ u k hpos, div_div]
  rfl

theorem rankProfileAtReal_norm (events : ℕ → Bool) (s₀ : State) (J : ℕ)
    (u : ℕ → ℝ) (k : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hpos : ∀ j, 0 < prescribedWalk events (infectious s₀) j) :
    ‖rankProfileAtReal events s₀ J u k x‖ =
      activeWeight (Real.exp x) (rankState events s₀ u k) /
        profileRealDenominator events (infectious s₀) J k x := by
  rw [rankProfileAtReal_eq_ofReal events s₀ J u k x (fun j _ ↦ hpos j), Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg]
  apply div_nonneg _ (profileRealDenominator_pos _ _ _ _ hx (hpos k)).le
  unfold activeWeight
  exact Finset.sum_nonneg (fun _ _ ↦ (pow_pos (Real.exp_pos _) _).le)

theorem rankResetProfileAtReal_norm (events : ℕ → Bool) (i₀ J N : ℕ)
    (u : ℕ → ℝ) (k : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hpos : 0 < prescribedWalk events i₀ k) :
    ‖rankResetProfileAtReal events i₀ J N u k x‖ =
      depthWeight (Real.exp x) (rankResetDepths events i₀ N u (k - N)) /
        profileRealDenominator events i₀ J k x := by
  rw [rankResetProfileAtReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact div_nonneg (depthWeight_nonneg (Real.exp_pos _).le _)
    (profileRealDenominator_pos _ _ _ _ hx hpos).le

theorem measurable_rankProfileAtReal (events : ℕ → Bool) (s₀ : State)
    (J k : ℕ) (x : ℝ) : Measurable (fun u ↦ rankProfileAtReal events s₀ J u k x) :=
  (measurable_state _).comp (measurable_rankState events s₀ k)

theorem continuousOn_rankProfileAtReal (events : ℕ → Bool) (s₀ : State) (J : ℕ)
    (u : ℕ → ℝ) (k : ℕ) {K : Set ℝ} (hK : ∀ x ∈ K, 0 ≤ x)
    (hpos : ∀ j, 0 < prescribedWalk events (infectious s₀) j) :
    ContinuousOn (rankProfileAtReal events s₀ J u k) K := by
  have hn : Continuous (fun x : ℝ ↦ activeWeight (Real.exp x) (rankState events s₀ u k)) := by
    unfold activeWeight
    fun_prop
  have hd : Continuous (profileRealDenominator events (infectious s₀) J k) := by
    unfold profileRealDenominator realNormalizerFrom
    fun_prop
  have hh := Complex.continuous_ofReal.comp_continuousOn
    (hn.continuousOn.div hd.continuousOn
      (fun x hx ↦ (profileRealDenominator_pos _ _ _ _ (hK x hx) (hpos k)).ne'))
  apply hh.congr
  intro x _
  exact rankProfileAtReal_eq_ofReal events s₀ J u k x (fun j _ ↦ hpos j)

theorem rankResetProfileAtReal_bounds (events : ℕ → Bool) (s₀ : State) (J N : ℕ)
    (u : ℕ → ℝ) (k : ℕ) (hk : N ≤ k) {x : ℝ} (hx : 0 ≤ x)
    (hpos : ∀ j, 0 < prescribedWalk events (infectious s₀) j) :
    ‖rankResetProfileAtReal events (infectious s₀) J N u k x‖ ≤
        ‖rankProfileAtReal events s₀ J u k x‖ ∧
      ‖rankProfileAtReal events s₀ J u k x‖ ≤
        (Real.exp x) ^ (rankState events s₀ u N).vertices *
          ‖rankResetProfileAtReal events (infectious s₀) J N u k x‖ := by
  have hb := rankResetDepths_weight_bounds events s₀ u N (k - N)
    (fun j _ ↦ hpos j) (Real.one_le_exp_iff.mpr hx)
  rw [Nat.add_sub_of_le hk] at hb
  rw [rankProfileAtReal_norm events s₀ J u k hx hpos,
    rankResetProfileAtReal_norm events (infectious s₀) J N u k hx (hpos k)]
  have hd := (profileRealDenominator_pos events (infectious s₀) J k hx (hpos k)).le
  exact ⟨div_le_div_of_nonneg_right hb.1 hd,
    (div_le_div_of_nonneg_right hb.2 hd).trans_eq (mul_div_assoc _ _ _)⟩

/-- A candidate zero on a compact set, detected from a fixed cofinal time
sequence. The dyadic times used by the analytic limit are admissible. -/
noncomputable def rankProfileZeroEvent (events : ℕ → Bool) (s₀ : State) (J : ℕ)
    (K : Set ℝ) (times : ℕ → ℕ) : Set (ℕ → ℝ) :=
  {u | Tendsto (fun m ↦ normInfOn K (rankProfileAtReal events s₀ J u (times m))) atTop (𝓝 0)}

theorem measurableSet_rankProfileZeroEvent (events : ℕ → Bool) (s₀ : State) (J : ℕ)
    (K : Set ℝ) (times : ℕ → ℕ) (hK : ∀ x ∈ K, 0 ≤ x)
    (hpos : ∀ j, 0 < prescribedWalk events (infectious s₀) j) :
    MeasurableSet (rankProfileZeroEvent events s₀ J K times) :=
  measurableSet_tendsto_normInfOn_zero K _
    (fun k x _ ↦ measurable_rankProfileAtReal events s₀ J (times k) x)
    (fun k u ↦ continuousOn_rankProfileAtReal events s₀ J u (times k) hK hpos)

theorem rankProfileZeroEvent_iff_reset (events : ℕ → Bool) (s₀ : State) (J N : ℕ)
    (u : ℕ → ℝ) {K : Set ℝ} (hK : IsCompact K) (hK0 : ∀ x ∈ K, 0 ≤ x)
    (times : ℕ → ℕ) (htimes : Tendsto times atTop atTop)
    (hpos : ∀ j, 0 < prescribedWalk events (infectious s₀) j) :
    u ∈ rankProfileZeroEvent events s₀ J K times ↔
      Tendsto (fun m ↦ normInfOn K
        (rankResetProfileAtReal events (infectious s₀) J N u (times m))) atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := (hK.image Real.continuous_exp).bddAbove
  let W : ℝ := max b 1
  have hW : 0 < W := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hWx : ∀ x ∈ K, Real.exp x ≤ W :=
    fun x hx ↦ (hb (Set.mem_image_of_mem Real.exp hx)).trans (le_max_left _ _)
  have hlarge : ∀ᶠ m in atTop, N ≤ times m := htimes.eventually_ge_atTop N
  constructor
  · intro hu
    apply tendsto_normInfOn_zero_of_comparison (B := 1) zero_lt_one _ hu
    filter_upwards [hlarge] with m hm
    intro x hx
    simpa only [one_mul] using
      (rankResetProfileAtReal_bounds events s₀ J N u (times m) hm (hK0 x hx) hpos).1
  · intro hu
    apply tendsto_normInfOn_zero_of_comparison
      (B := W ^ (rankState events s₀ u N).vertices) (pow_pos hW _) _ hu
    filter_upwards [hlarge] with m hm
    intro x hx
    apply (rankResetProfileAtReal_bounds events s₀ J N u (times m) hm (hK0 x hx) hpos).2.trans
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.exp_pos x).le (hWx x hx) _) (norm_nonneg _)

/-- This is literal invariance for all uniform inputs, not just an
almost-sure identification with an unspecified tail event. -/
theorem rankProfileZeroEvent_finite_changes (events : ℕ → Bool) (s₀ : State) (J : ℕ)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : ∀ x ∈ K, 0 ≤ x)
    (times : ℕ → ℕ) (htimes : Tendsto times atTop atTop)
    (hpos : ∀ j, 0 < prescribedWalk events (infectious s₀) j)
    (N : ℕ) (u v : ℕ → ℝ) (huv : ∀ k ≥ N, u k = v k) :
    u ∈ rankProfileZeroEvent events s₀ J K times ↔
      v ∈ rankProfileZeroEvent events s₀ J K times := by
  rw [rankProfileZeroEvent_iff_reset events s₀ J N u hK hK0 times htimes hpos,
    rankProfileZeroEvent_iff_reset events s₀ J N v hK hK0 times htimes hpos]
  have heq : rankResetProfileAtReal events (infectious s₀) J N u =
      rankResetProfileAtReal events (infectious s₀) J N v := by
    funext k x
    rw [rankResetProfileAtReal, rankResetProfileAtReal,
      rankResetDepths_congr_tail events (infectious s₀) N huv]
  rw [heq]

/-- Kolmogorov's zero-one alternative for the actual compact profile-zero
event, with no stochastic assumptions on the fixed positive event word. -/
theorem rankProfileZeroEvent_zero_one (events : ℕ → Bool) (s₀ : State) (J : ℕ)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : ∀ x ∈ K, 0 ≤ x)
    (times : ℕ → ℕ) (htimes : Tendsto times atTop atTop)
    (hpos : ∀ j, 0 < prescribedWalk events (infectious s₀) j) :
    CountCoupling.uniformLaw (rankProfileZeroEvent events s₀ J K times) = 0 ∨
      CountCoupling.uniformLaw (rankProfileZeroEvent events s₀ J K times) = 1 :=
  CountCoupling.uniformLaw_zero_one_of_finite_changes
    (measurableSet_rankProfileZeroEvent events s₀ J K times hK0 hpos)
    (rankProfileZeroEvent_finite_changes events s₀ J hK hK0 times htimes hpos)

end HeightPaper.Model
