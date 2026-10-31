module

public import HeightPaper.Probability.ConditionalContinuationGoodStates
public import HeightPaper.Model.RandomOutgrowthProfile

/-!
# Conditional fresh-outgrowth height from profile and pressure inputs

The paper's dangling-tree argument first proves an averaged height deviation
estimate and then extracts cutoff trees with uniformly small conditional error.
This result performs those two steps for the actual continuation law, given
the two strict geometric comparison pressures and a root-count profile.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal Classical

namespace HeightPaper.Model

def outgrowthHeightDeviationEvent (roots : ℕ → State → Finset ℕ)
    (c ε : ℝ) (n : ℕ) (s : State) : Set State :=
  {t | ε ≤ |(selectedFreshHeight s.vertices s.tree.size_pos
    (roots n s) t : ℝ) / Real.log n - c|}

/-- Two geometric comparison means on opposite sides of the target height
scale yield the paper's conditional good-tree estimate, once the actual
cutoff profile and pressure estimates are supplied. -/
theorem conditionalOutgrowthGoodStates_of_profile
    (μ : ℕ → PMF State) (hμ : ∀ n, (μ n).support.Finite)
    (rates : ℕ → ℝ≥0) (K L : ℕ → ℕ)
    (roots : ℕ → State → Finset ℕ) (A : ℕ → Set State)
    {pU pL : unitInterval} (hpU : 1 / 2 < (pU : ℝ))
    (hpU1 : (pU : ℝ) < 1) (hpL : 1 / 2 < (pL : ℝ))
    (hpL1 : (pL : ℝ) < 1)
    {f c ε mass : ℝ} (hf : 0 < f) (hmass : 0 < mass)
    (hscaleU : f / (-Real.log (Branching.geometricMean pU)) < c + ε)
    (hscaleL : c - ε < f / (-Real.log (Branching.geometricMean pL)))
    (hprofile : ∀ a > (0 : ℝ), Tendsto (fun n ↦
      (μ n).toMeasure.real {s | s ∈ A n ∧
        a ≤ |Real.log (selectedRootCount s (roots n s)) / Real.log n - f|})
        atTop (𝓝 0))
    (hK : ∀ᶠ n in atTop, ∀ s ∈ (μ n).support,
      s ∈ A n → potential s ≤ K n)
    (hpressureU : Tendsto (fun n ↦ (μ n).toMeasure.real
      {s | s ∈ A n ∧
        1 - (infectionProbability (rates n) s.susceptible : ℝ) < (pU : ℝ)})
        atTop (𝓝 0))
    (hpressureL : ∀ᶠ n in atTop,
      1 - (infectionProbability (rates n) (L n) : ℝ) ≤ (pL : ℝ))
    (hbarrier : Tendsto (fun n ↦
      (continuationSampleLaw (μ n) (rates n) (K n)).toMeasure.real
        {x | x.cutoff ∈ A n ∧ x.final.susceptible < L n}) atTop (𝓝 0))
    (hA : Tendsto (fun n ↦ (μ n).toMeasure.real (A n)) atTop (𝓝 mass)) :
    Tendsto (continuationGoodThreshold μ rates K A
      (outgrowthHeightDeviationEvent roots c ε)) atTop (𝓝 0) ∧
    Tendsto (fun n ↦
      (μ n).toMeasure.real
        (continuationGoodStates μ rates K A
          (outgrowthHeightDeviationEvent roots c ε) n) /
      (μ n).toMeasure.real (A n)) atTop (𝓝 1) ∧
    ∀ n, ∀ s ∈ continuationGoodStates μ rates K A
        (outgrowthHeightDeviationEvent roots c ε) n,
      (continuationLaw (rates n) s (K n)).toMeasure.real
        (outgrowthHeightDeviationEvent roots c ε n s) ≤
          continuationGoodThreshold μ rates K A
            (outgrowthHeightDeviationEvent roots c ε) n := by
  let cU := f / (-Real.log (Branching.geometricMean pU))
  let cL := f / (-Real.log (Branching.geometricMean pL))
  let εU := c + ε - cU
  let εL := cL - (c - ε)
  have hεU : 0 < εU := sub_pos.mpr hscaleU
  have hεL : 0 < εL := sub_pos.mpr hscaleL
  have hupper := randomOutgrowth_normalized_upper_of_profile μ hμ rates K roots A
    hpU hpU1 hf hprofile hK hpressureU hεU
  have hlower := randomOutgrowth_normalized_lower_of_profile μ hμ rates K L roots A
    hpL hpL1 hf hprofile hK hpressureL hbarrier hεL
  have hsum := hupper.add hlower
  rw [add_zero] at hsum
  have hbad : Tendsto (fun n ↦
      (continuationSampleLaw (μ n) (rates n) (K n)).toMeasure.real
        {x | x.cutoff ∈ A n ∧
          x.final ∈ outgrowthHeightDeviationEvent roots c ε n x.cutoff})
        atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
    apply Eventually.of_forall
    intro n
    apply le_trans (measureReal_mono (μ := (continuationSampleLaw (μ n)
      (rates n) (K n)).toMeasure) ?_ (measure_ne_top _ _))
      (measureReal_union_le _ _)
    intro x hx
    let v := (selectedFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos
      (roots n x.cutoff) x.final : ℝ) / Real.log n
    have hdev : ε ≤ |v - c| := hx.2
    rcases le_total v c with hvc | hcv
    · apply Or.inr
      refine ⟨hx.1, ?_⟩
      have h := hdev
      rw [abs_of_nonpos (sub_nonpos.mpr hvc)] at h
      change v ≤ cL - εL
      dsimp [εL]
      linarith
    · apply Or.inl
      refine ⟨hx.1, ?_⟩
      have h := hdev
      rw [abs_of_nonneg (sub_nonneg.mpr hcv)] at h
      change cU + εU ≤ v
      dsimp [εU]
      linarith
  exact continuationGoodStates_conditional_of_bad_tendsto
    μ hμ rates K A (outgrowthHeightDeviationEvent roots c ε)
    hmass hA hbad

end HeightPaper.Model
