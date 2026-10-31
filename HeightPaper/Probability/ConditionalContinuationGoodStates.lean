module

public import HeightPaper.Probability.LateConditionalGoodStates

/-!
# Conditional good cutoff states for a continuation event

This is the statewise square-root extraction used by the paper after an
averaged bad-event estimate. It applies to any cutoff-dependent continuation
event, including the fresh-outgrowth height events of `lem:dangling`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal Classical

namespace HeightPaper.Model

noncomputable def continuationBadAverage (μ : ℕ → PMF State)
    (rates : ℕ → ℝ≥0) (K : ℕ → ℕ) (A : ℕ → Set State)
    (E : ℕ → State → Set State) (n : ℕ) : ℝ :=
  ∫ s, (A n).indicator
    (fun s ↦ (continuationLaw (rates n) s (K n)).toMeasure.real (E n s)) s
    ∂(μ n).toMeasure

noncomputable def continuationGoodThreshold (μ : ℕ → PMF State)
    (rates : ℕ → ℝ≥0) (K : ℕ → ℕ) (A : ℕ → Set State)
    (E : ℕ → State → Set State) (n : ℕ) : ℝ :=
  Real.sqrt (continuationBadAverage μ rates K A E n) +
    1 / ((n + 1 : ℕ) : ℝ)

noncomputable def continuationGoodStates (μ : ℕ → PMF State)
    (rates : ℕ → ℝ≥0) (K : ℕ → ℕ) (A : ℕ → Set State)
    (E : ℕ → State → Set State) (n : ℕ) : Set State :=
  {s | s ∈ A n ∧
    (continuationLaw (rates n) s (K n)).toMeasure.real (E n s) ≤
      continuationGoodThreshold μ rates K A E n}

/-- A vanishing joint bad-event mass and a positive survival mass yield
cutoff states of conditional probability tending to one, with one uniform
vanishing bound on their continuation failure probabilities. -/
theorem continuationGoodStates_conditional_of_bad_tendsto
    (μ : ℕ → PMF State) (hμ : ∀ n, (μ n).support.Finite)
    (rates : ℕ → ℝ≥0) (K : ℕ → ℕ) (A : ℕ → Set State)
    (E : ℕ → State → Set State) {c : ℝ} (hc : 0 < c)
    (hA : Tendsto (fun n ↦ (μ n).toMeasure.real (A n)) atTop (𝓝 c))
    (hbad : Tendsto (fun n ↦
      (continuationSampleLaw (μ n) (rates n) (K n)).toMeasure.real
        {x | x.cutoff ∈ A n ∧ x.final ∈ E n x.cutoff}) atTop (𝓝 0)) :
    Tendsto (continuationGoodThreshold μ rates K A E) atTop (𝓝 0) ∧
    Tendsto (fun n ↦
      (μ n).toMeasure.real (continuationGoodStates μ rates K A E n) /
        (μ n).toMeasure.real (A n)) atTop (𝓝 1) ∧
    ∀ n, ∀ s ∈ continuationGoodStates μ rates K A E n,
      (continuationLaw (rates n) s (K n)).toMeasure.real (E n s) ≤
        continuationGoodThreshold μ rates K A E n := by
  have hmean : Tendsto (continuationBadAverage μ rates K A E) atTop (𝓝 0) := by
    apply hbad.congr'
    apply Eventually.of_forall
    intro n
    simpa only [continuationBadAverage] using
      continuationSampleLaw_restricted_event (μ n) (hμ n)
        (rates n) (K n) (A n) (E n)
  have hsqrt : Tendsto (fun n ↦ Real.sqrt
      (continuationBadAverage μ rates K A E n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hmean
  have hθ : Tendsto (continuationGoodThreshold μ rates K A E) atTop (𝓝 0) := by
    unfold continuationGoodThreshold
    simpa only [Nat.cast_add, Nat.cast_one, zero_add] using
      hsqrt.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmiss : Tendsto (fun n ↦
      (μ n).toMeasure.real (A n \ continuationGoodStates μ rates K A E n))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsqrt
    apply Eventually.of_forall
    intro n
    have hb := finitePMF_goodStates_badMass_le_sqrt (μ n) (hμ n)
      (A n) (fun s ↦
        (continuationLaw (rates n) s (K n)).toMeasure.real (E n s))
      (fun _ ↦ measureReal_nonneg) n
    simpa only [continuationBadAverage, continuationGoodThreshold,
      continuationGoodStates] using hb
  have hG : Tendsto (fun n ↦
      (μ n).toMeasure.real (continuationGoodStates μ rates K A E n))
      atTop (𝓝 c) := by
    have hdiff := hA.sub hmiss
    simpa only [sub_zero] using hdiff.congr' (Eventually.of_forall (by
      intro n
      let ν := (μ n).toMeasure
      let G := continuationGoodStates μ rates K A E n
      have hGA : G ⊆ A n := fun _ hs ↦ hs.1
      have hsd := measureReal_sdiff (μ := ν) hGA
        (show MeasurableSet G from trivial) (measure_ne_top ν _)
      dsimp [ν, G] at hsd ⊢
      linarith))
  have hratio := hG.div hA hc.ne'
  have hratio' : Tendsto (fun n ↦
      (μ n).toMeasure.real (continuationGoodStates μ rates K A E n) /
        (μ n).toMeasure.real (A n)) atTop (𝓝 1) := by
    change Tendsto (fun n ↦
      (μ n).toMeasure.real (continuationGoodStates μ rates K A E n) /
        (μ n).toMeasure.real (A n)) atTop (𝓝 (c / c)) at hratio
    simpa only [div_self hc.ne'] using hratio
  exact ⟨hθ, hratio', fun n s hs ↦ hs.2⟩

end HeightPaper.Model
