module

public import HeightPaper.Model.HeightMeshParameters
public import HeightPaper.Model.ProfileHeightLower
public import HeightPaper.Probability.OutgrowthPressure

/-! # Full-height concentration from the remaining profile inputs

The finite-mesh, outgrowth, pressure, and integer-rounding estimates are
discharged here. Actual real-Laplace asymptotics and the pre-cutoff upper-height
estimate remain explicit hypotheses, so this is not the main theorem.
-/

public section

open Filter Set MeasureTheory
open scoped Topology NNReal

namespace HeightPaper.Model

/-- Every sufficiently late fixed cutoff has the required surviving-height
upper bound, conditional only on actual Laplace asymptotics and the old-tree
height bound. All mesh and geometric comparison parameters are chosen here. -/
theorem eventually_cutoff_fullHeight_upper_of_profile
    (rates : ℕ → ℝ≥0) {l : ℝ} (hl : 1 < l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hLap : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp v) s) / Real.log n -
          (1 + growthFactor l * (Real.exp v - 1))|}) atTop (𝓝 0))
    (hpreHeight : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ b > growthFactor l * Real.exp (profileRoot l),
      Tendsto (fun n ↦ (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real {s |
        s.active.Nonempty ∧ b < (height s : ℝ) / Real.log n}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      Tendsto (fun n ↦ (continuationSampleLaw
        (evolve (rates n) n (sourceCutoff l δ n)) (rates n) (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
        {s | s.cutoff.active.Nonempty ∧ heightCoefficient l + ε ≤
          (height s.final : ℝ) / Real.log n}) atTop (𝓝 0) := by
  obtain ⟨J, x, m, pre, t, a, hx, hinc, hmm, hm1, hprebase, hpre, ht, htu, ha, hgap, hmesh⟩ :=
    exists_upper_height_parameters hl hε
  have hm : 0 < m := (offspringMean_pos hl).trans hmm
  let p := Branching.successParameter m hm.le
  have hp : 1 / 2 < (p : ℝ) ∧ (p : ℝ) < 1 := successParameter_subcritical hm hm1
  have hp0 : 0 < (p : ℝ) := lt_trans (by norm_num) hp.1
  have heq : Branching.geometricMean p = m := Branching.geometricMean_successParameter m hm.le
  obtain ⟨δ₀, hδ₀, hpressure⟩ := eventually_cutoff_recovery_lower_concentration rates hl hp0
    (by rw [heq]; exact hmm) hrates
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ
  have hδ1 : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ.1, hδ.2.trans (hδ₀.2.trans (by norm_num))⟩
  have htime : (1 - δ) * fluidExtinctionTime l ∈ Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ1.2) (fluidExtinctionTime_pos hl)
    · nlinarith [fluidExtinctionTime_pos hl, hδ1.1]
  apply normalized_fullHeight_upper_of_laplace rates (fun n ↦ sourceCutoff l δ n)
    (fun n ↦ 2 * n + 1 - sourceCutoff l δ n) hl htime hpre ht htu hrates
    (tendsto_floor_fraction htime.1.le) x hx hinc (hLap δ hδ1) hp.1 hp.2 a ha
    (fun b ↦ by rw [heq]; exact hgap b) hmesh _ (hpressure δ hδ) (hpreHeight δ hδ1 pre hprebase)
  exact Eventually.of_forall fun _ _ hs ha ↦ evolve_active_potential_le_remaining hs ha

/-- Every fixed interior cutoff has the surviving-height lower bound from the
actual Laplace input. The lower pressure barrier is supplied by the fluid law. -/
theorem cutoff_fullHeight_lower_of_profile
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hLap : ∀ v ∈ Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp v) s) / Real.log n -
          (1 + growthFactor l * (Real.exp v - 1))|}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (continuationSampleLaw
      (evolve (rates n) n (sourceCutoff l δ n)) (rates n) (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
      {s | s.cutoff.active.Nonempty ∧ (height s.final : ℝ) / Real.log n ≤
        heightCoefficient l - ε}) atTop (𝓝 0) := by
  obtain ⟨x, m, a, hx, hm, hmm, ha, htarget, hgap⟩ := exists_lower_height_parameters hl hε
  have hm1 : m < 1 := hmm.trans (offspringMean_lt_one hl)
  let p := Branching.successParameter m hm.le
  have hp : 1 / 2 < (p : ℝ) ∧ (p : ℝ) < 1 := successParameter_subcritical hm hm1
  have hp0 : 0 < (p : ℝ) := lt_trans (by norm_num) hp.1
  have heq : Branching.geometricMean p = m := Branching.geometricMean_successParameter m hm.le
  obtain ⟨L, _, hL, hbarrier⟩ := exists_terminal_outgrowth_lower_pressure_threshold rates hl hp0 hp.2
    (by rw [heq]; exact hmm) hrates
  have hsample : Tendsto (fun n ↦ (continuationSampleLaw
      (evolve (rates n) n (sourceCutoff l δ n)) (rates n) (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
        {s | s.cutoff.active.Nonempty ∧ s.final.susceptible < L n}) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hbarrier
    intro n
    calc
      _ ≤ (continuationSampleLaw (evolve (rates n) n (sourceCutoff l δ n)) (rates n)
          (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real {s | s.final.susceptible < L n} :=
        measureReal_mono (fun _ h ↦ h.2) (measure_ne_top _ _)
      _ = _ := by
        change (continuationSampleLaw _ _ _).toMeasure.real {s | s.final ∈ {s : State | s.susceptible < L n}} = _
        rw [continuationSampleLaw_final_event, ← evolve_add_continuation,
          Nat.add_sub_of_le (sourceCutoff_le_steps hl hδ n)]
  apply normalized_fullHeight_lower_of_laplace rates (fun n ↦ sourceCutoff l δ n)
    (fun n ↦ 2 * n + 1 - sourceCutoff l δ n) L hl hx ha htarget hLap hp.1 hp.2
    (by rw [heq]; exact hgap) _ (hL.mono fun _ hn ↦ hn.2) hsample
  exact Eventually.of_forall fun _ _ hs ha ↦ evolve_active_potential_le_remaining hs ha

/-- Actual full-height concentration on active cutoff samples. All profile
bins, outgrowth bounds, pressure estimates, and mesh choices are discharged. -/
theorem eventually_cutoff_fullHeight_concentration_of_profile
    (rates : ℕ → ℝ≥0) {l : ℝ} (hl : 1 < l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hLap : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp v) s) / Real.log n -
          (1 + growthFactor l * (Real.exp v - 1))|}) atTop (𝓝 0))
    (hpreHeight : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ b > growthFactor l * Real.exp (profileRoot l),
      Tendsto (fun n ↦ (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real {s |
        s.active.Nonempty ∧ b < (height s : ℝ) / Real.log n}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ ∈ Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      Tendsto (fun n ↦ (continuationSampleLaw
        (evolve (rates n) n (sourceCutoff l δ n)) (rates n) (2 * n + 1 - sourceCutoff l δ n)).toMeasure.real
        {s | s.cutoff.active.Nonempty ∧ ε ≤ |(height s.final : ℝ) / Real.log n - heightCoefficient l|})
        atTop (𝓝 0) := by
  obtain ⟨δ₀, hδ₀, hupper⟩ := eventually_cutoff_fullHeight_upper_of_profile rates hl hrates hLap hpreHeight hε
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ
  have hδ1 : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ.1, hδ.2.trans (hδ₀.2.trans (by norm_num))⟩
  have hlower := cutoff_fullHeight_lower_of_profile rates hl hδ1 hrates (hLap δ hδ1) hε
  have hsum := hlower.add (hupper δ hδ)
  rw [add_zero] at hsum
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hsum
  intro n
  apply le_trans (measureReal_mono _ (measure_ne_top _ _)) (measureReal_union_le _ _)
  intro s hs
  by_cases hh : (height s.final : ℝ) / Real.log n ≤ heightCoefficient l
  · left
    refine ⟨hs.1, ?_⟩
    have he := hs.2
    rw [abs_of_nonpos (sub_nonpos.mpr hh)] at he
    linarith
  · right
    refine ⟨hs.1, ?_⟩
    have he := hs.2
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hh))] at he
    linarith

end HeightPaper.Model
