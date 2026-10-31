module

public import HeightPaper.Probability.ProfileConvergence
public import HeightPaper.Probability.VanishingFilter

/-!
# Weak profile transfer in probability

The deterministic real-Laplace argument applies on the exceptional-probability
filter. This preserves varying sample spaces and permits measures restricted
to the survival event. Only the epidemic Laplace input remains to be proved.
-/

public section

open Filter Set MeasureTheory
open scoped Topology

namespace HeightPaper.Profile

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    {α : Sigma Ω → Type*}

/-- Real logarithmic Laplace convergence in probability yields logarithmic bin
convergence in probability, and also rules out an empty bin with high
probability. The limiting exponent is exactly the paper's profile exponent
when `c=1` and `γ=λ/(λ-1)`. -/
theorem log_binMass_convergence_in_probability
    (s : (i : Sigma Ω) → Finset (α i)) (w d : (i : Sigma Ω) → α i → ℝ)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hw : ∀ i, ∀ v ∈ s i, 0 ≤ w i v)
    {c γ x B : ℝ} (hγ : 0 < γ) (hx : 0 ≤ x) (hB : γ * Real.exp x < B)
    {U : Set ℝ} (hU : IsOpen U) (hxU : x ∈ U)
    (hZ : ∀ t ∈ U, Tendsto (fun n ↦ (μ n).real
      {ω | laplaceSum (s ⟨n, ω⟩) (w ⟨n, ω⟩) (d ⟨n, ω⟩) t ≤ 0}) atTop (𝓝 0))
    (hLap : ∀ t ∈ U, ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (μ n).real
      {ω | ε ≤ |Real.log (laplaceSum (s ⟨n, ω⟩) (w ⟨n, ω⟩) (d ⟨n, ω⟩) t) / L n -
        (c + γ * (Real.exp t - 1))|}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (μ n).real {ω |
      binMass (s ⟨n, ω⟩) (w ⟨n, ω⟩) (d ⟨n, ω⟩) (γ * Real.exp x * L n) (B * L n) ≤ 0})
      atTop (𝓝 0) ∧
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (μ n).real {ω |
      ε ≤ |Real.log (binMass (s ⟨n, ω⟩) (w ⟨n, ω⟩) (d ⟨n, ω⟩)
        (γ * Real.exp x * L n) (B * L n)) / L n -
        (c + γ * (Real.exp x - 1 - x * Real.exp x))|}) atTop (𝓝 0) := by
  have hpos : ∀ t ∈ U, ∀ᶠ i in vanishingProbabilityFilter μ,
      0 < laplaceSum (s i) (w i) (d i) t := by
    intro t ht
    rw [eventually_vanishingProbabilityFilter_iff]
    simpa only [not_lt] using hZ t ht
  have hconv : ∀ t ∈ U, Tendsto
      (fun i ↦ Real.log (laplaceSum (s i) (w i) (d i) t) / L i.1)
      (vanishingProbabilityFilter μ) (𝓝 (c + γ * (Real.exp t - 1))) := by
    intro t ht
    exact (tendsto_vanishingProbabilityFilter_iff μ _ _).mpr (hLap t ht)
  have h := log_binMass_convergence_of_exponential_laplace s w d
    (hL.comp (tendsto_index_vanishingProbabilityFilter μ)) hw hγ hx hB hU hxU hpos hconv
  constructor
  · have hp := (eventually_vanishingProbabilityFilter_iff μ _).mp h.1
    simpa only [not_lt, Function.comp_apply] using hp
  · exact (tendsto_vanishingProbabilityFilter_iff μ
      (fun i : Sigma Ω ↦ Real.log (binMass (s i) (w i) (d i)
        (γ * Real.exp x * L i.1) (B * L i.1)) / L i.1)
      (c + γ * (Real.exp x - 1 - x * Real.exp x))).mp h.2

/-- The same transfer covers bins with infinite upper endpoint, preserving the
source's full weak-profile range. -/
theorem log_tailMass_convergence_in_probability
    (s : (i : Sigma Ω) → Finset (α i)) (w d : (i : Sigma Ω) → α i → ℝ)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hw : ∀ i, ∀ v ∈ s i, 0 ≤ w i v)
    {c γ x : ℝ} (hγ : 0 < γ) (hx : 0 ≤ x)
    {U : Set ℝ} (hU : IsOpen U) (hxU : x ∈ U)
    (hZ : ∀ t ∈ U, Tendsto (fun n ↦ (μ n).real
      {ω | laplaceSum (s ⟨n, ω⟩) (w ⟨n, ω⟩) (d ⟨n, ω⟩) t ≤ 0}) atTop (𝓝 0))
    (hLap : ∀ t ∈ U, ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (μ n).real
      {ω | ε ≤ |Real.log (laplaceSum (s ⟨n, ω⟩) (w ⟨n, ω⟩) (d ⟨n, ω⟩) t) / L n -
        (c + γ * (Real.exp t - 1))|}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (μ n).real {ω |
      tailMass (s ⟨n, ω⟩) (w ⟨n, ω⟩) (d ⟨n, ω⟩) (γ * Real.exp x * L n) ≤ 0})
      atTop (𝓝 0) ∧
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (μ n).real {ω |
      ε ≤ |Real.log (tailMass (s ⟨n, ω⟩) (w ⟨n, ω⟩) (d ⟨n, ω⟩)
        (γ * Real.exp x * L n)) / L n -
        (c + γ * (Real.exp x - 1 - x * Real.exp x))|}) atTop (𝓝 0) := by
  have hpos : ∀ t ∈ U, ∀ᶠ i in vanishingProbabilityFilter μ,
      0 < laplaceSum (s i) (w i) (d i) t := by
    intro t ht
    rw [eventually_vanishingProbabilityFilter_iff]
    simpa only [not_lt] using hZ t ht
  have hconv : ∀ t ∈ U, Tendsto
      (fun i ↦ Real.log (laplaceSum (s i) (w i) (d i) t) / L i.1)
      (vanishingProbabilityFilter μ) (𝓝 (c + γ * (Real.exp t - 1))) := by
    intro t ht
    exact (tendsto_vanishingProbabilityFilter_iff μ _ _).mpr (hLap t ht)
  have h := log_tailMass_convergence_of_exponential_laplace s w d
    (hL.comp (tendsto_index_vanishingProbabilityFilter μ)) hw hγ hx hU hxU hpos hconv
  constructor
  · have hp := (eventually_vanishingProbabilityFilter_iff μ _).mp h.1
    simpa only [not_lt, Function.comp_apply] using hp
  · exact (tendsto_vanishingProbabilityFilter_iff μ
      (fun i : Sigma Ω ↦ Real.log (tailMass (s i) (w i) (d i)
        (γ * Real.exp x * L i.1)) / L i.1)
      (c + γ * (Real.exp x - 1 - x * Real.exp x))).mp h.2

end HeightPaper.Profile
