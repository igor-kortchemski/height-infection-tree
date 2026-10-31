module

public import HeightPaper.Analysis.FluidODE

/-!
# Deterministic late-phase bounds

These estimates justify choosing a sufficiently late fluid cutoff and the
subcritical recovery parameters used in the outgrowth sandwich. Concentration
of the epidemic around this deterministic curve is a separate obligation.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace HeightPaper

theorem tendsto_fluidPressure_at_cutoff {l : ℝ} (hl : 1 < l) :
    Tendsto (fun δ : ℝ ↦ l * fluidSusceptible l ((1 - δ) * fluidExtinctionTime l))
      (𝓝 0) (𝓝 (offspringMean l)) := by
  have hc : ContinuousAt
      (fun δ : ℝ ↦ l * fluidSusceptible l ((1 - δ) * fluidExtinctionTime l)) 0 :=
    ((continuous_fluidSusceptible hl).continuousAt.comp
      ((continuousAt_const.sub continuousAt_id).mul continuousAt_const)).const_mul l
  simpa only [sub_zero, one_mul, parameter_mul_fluidSusceptible_extinction hl] using hc.tendsto

/-- The entire late fluid interval has infection pressure arbitrarily close
to the terminal subcritical mean; the cutoff can be as late as required. -/
theorem exists_lateFluidPressure_bounds {l η δmax : ℝ} (hl : 1 < l)
    (hη : 0 < η) (hδmax : 0 < δmax) :
    ∃ δ ∈ Ioo (0 : ℝ) δmax, ∀ t ∈
      Icc ((1 - δ) * fluidExtinctionTime l) (fluidExtinctionTime l),
      offspringMean l ≤ l * fluidSusceptible l t ∧
        l * fluidSusceptible l t < offspringMean l + η := by
  have hh := (tendsto_fluidPressure_at_cutoff hl).eventually
    (Iio_mem_nhds (show offspringMean l < offspringMean l + η by linarith))
  have he : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo (0 : ℝ) δmax ∧
      l * fluidSusceptible l ((1 - δ) * fluidExtinctionTime l) < offspringMean l + η := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδmax).filter_mono nhdsWithin_le_nhds,
      hh.filter_mono nhdsWithin_le_nhds] with δ hδ hd hu
    exact ⟨⟨hδ, hd⟩, hu⟩
  obtain ⟨δ, hδ, hu⟩ := he.exists
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have hl0 := (lt_trans zero_lt_one hl).le
  constructor
  · rw [← parameter_mul_fluidSusceptible_extinction hl]
    exact mul_le_mul_of_nonneg_left ((fluidSusceptible_strictAnti hl).antitone ht.2) hl0
  · exact (mul_le_mul_of_nonneg_left
      ((fluidSusceptible_strictAnti hl).antitone ht.1) hl0).trans_lt hu

/-- Small perturbations of a subcritical infection pressure give recovery
probabilities strictly between one half and one, in the order needed by the
geometric-tree sandwich. The smallness assumptions rule out the denominator
issue in the literal all-positive-η formulation of `lem:eventE`. -/
theorem subcritical_recovery_bounds {m η x : ℝ}
    (hη : 0 < η) (hηm : η < m) (hη1 : η < 1 - m)
    (hxlo : m - η ≤ x) (hxhi : x ≤ m + η) :
    1 / 2 < 1 / (1 + m + η) ∧
      1 / (1 + m + η) ≤ 1 / (1 + x) ∧
      1 / (1 + x) ≤ 1 / (1 + m - η) ∧
      1 / (1 + m - η) < 1 := by
  have hdlo : 0 < 1 + m - η := by linarith
  have hdx : 0 < 1 + x := by linarith
  have hdhi : 0 < 1 + m + η := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hdhi).mpr
    linarith
  · exact one_div_le_one_div_of_le hdx (by linarith)
  · exact one_div_le_one_div_of_le hdlo (by linarith)
  · exact (div_lt_one hdlo).mpr (by linarith)

end HeightPaper
