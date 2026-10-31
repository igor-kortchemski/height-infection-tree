module

public import HeightPaper.Model.AnalyticProfileLimit
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # The prescribed profile as a continuous-function-valued martingale -/

@[expose] public section

open MeasureTheory Complex Metric Filter Set
open scoped Topology

namespace HeightPaper.Model

noncomputable def continuousPrescribedProfile
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) (c : ℂ) (r : ℝ)
    (hC : ∀ k ≥ J, ∀ z ∈ closedBall c r,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0)
    (k : ℕ) (s : State) : C(↥(closedBall c r), ℂ) :=
  ⟨fun z ↦ prescribedNormalizedProfile (Complex.exp z) events s₀ J k s, by
    have h : ContinuousOn
        (fun z : ℂ ↦ prescribedNormalizedProfile (Complex.exp z) events s₀ J k s)
        (closedBall c r) := by
      apply (differentiableOn_prescribedNormalizedProfile_exp events s₀ s J k ?_).continuousOn
      intro z hz
      by_cases hk : J ≤ k
      · exact hC k hk z hz
      · simp [prescribedNormalizerFrom, Finset.Ico_eq_empty_of_le (by omega : k ≤ J)]
    exact continuousOn_iff_continuous_domRestrict.mp h⟩

@[simp] theorem continuousPrescribedProfile_apply
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) (c : ℂ) (r : ℝ)
    (hC : ∀ k ≥ J, ∀ z ∈ closedBall c r,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0)
    (k : ℕ) (s : State) (z : closedBall c r) :
    continuousPrescribedProfile events s₀ J c r hC k s z =
      prescribedNormalizedProfile (Complex.exp z) events s₀ J k s := rfl

theorem continuousPrescribedProfile_martingale
    (events : ℕ → Bool) (s₀ : State) (J : ℕ) (c : ℂ) (r : ℝ)
    (hC : ∀ k ≥ J, ∀ z ∈ closedBall c r,
      prescribedNormalizerFrom (Complex.exp z) events (infectious s₀) J k ≠ 0)
    (hpos : ∀ i, 0 < prescribedWalk events (infectious s₀) i)
    (j : ℕ) (hj : J ≤ j) :
    Martingale
      (fun k ω ↦ continuousPrescribedProfile events s₀ J c r hC (j + k) (ω (j + k)))
      (FinitePMF.trajectoryFiltrationFrom j) (prescribedTrajectoryMeasure events s₀) := by
  let E := C(↥(closedBall c r), ℂ)
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  apply FinitePMF.kernelTrajectory_martingale_from
    (fun k ↦ prescribedStep (events k)) (fun _ ↦ measurable_state _)
    (fun k s ↦ finite_support_prescribedStep (events k) s) s₀ j
    (continuousPrescribedProfile events s₀ J c r hC) (fun _ ↦ measurable_state _)
  intro k hk s hs
  apply ContinuousMap.ext
  intro z
  have hi := FinitePMF.integrable_of_finite_support
    (prescribedStep (events k) s) (finite_support_prescribedStep (events k) s)
    (continuousPrescribedProfile events s₀ J c r hC (k + 1))
  have he := (ContinuousMap.evalCLM ℝ z).integral_comp_comm hi
  change (∫ t, prescribedNormalizedProfile (Complex.exp z) events s₀ J (k + 1) t
    ∂(prescribedStep (events k) s).toMeasure) =
    (∫ t, continuousPrescribedProfile events s₀ J c r hC (k + 1) t
      ∂(prescribedStep (events k) s).toMeasure) z at he
  change (∫ t, continuousPrescribedProfile events s₀ J c r hC (k + 1) t
    ∂(prescribedStep (events k) s).toMeasure) z = _
  exact he.symm.trans (prescribedNormalizedProfile_mean (Complex.exp z) events s₀ J k
    (hj.trans hk) (fun i _ ↦ hpos i) (hC (k + 1) (by omega) z z.property) s hs)

theorem continuousMap_tendsto_iff_uniformlyOn {c : ℂ} {r : ℝ}
    (F : ℕ → C(↥(closedBall c r), ℂ)) (L : C(↥(closedBall c r), ℂ)) :
    Tendsto F atTop (𝓝 L) ↔
      TendstoUniformlyOn (fun (k : ℕ) (z : closedBall c r) ↦ F k z) L atTop univ := by
  constructor
  · intro h
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h ε hε
    filter_upwards [eventually_ge_atTop N] with k hk
    intro z _
    rw [dist_comm, dist_eq_norm]
    exact (ContinuousMap.norm_coe_le_norm (F k - L) z).trans_lt
      (by simpa only [dist_eq_norm] using hN k hk)
  · intro h
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have ht := Metric.tendstoUniformlyOn_iff.mp h (ε / 2) (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.mp ht
    refine ⟨N, fun k hk ↦ ?_⟩
    have hb : ‖F k - L‖ ≤ ε / 2 := (ContinuousMap.norm_le _ (by positivity)).mpr
      (fun z ↦ (by
        have ht := hN k hk z (mem_univ _)
        rw [dist_comm, dist_eq_norm] at ht
        exact ht.le))
    rw [dist_eq_norm]
    linarith

end HeightPaper.Model
