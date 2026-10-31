module

public import HeightPaper.Model.WeakProfile
public import HeightPaper.Probability.FluidLocation
public import HeightPaper.Analysis.LogCounts

/-!
# The low-height profile bin

At a macroscopic time before fluid extinction, the active population is linear
on survival. A high-depth tail of exponent less than one removes a negligible
fraction. Consequently the low bin has exponent one. This establishes the
low-bin transfer without assigning a positive minimum depth to its vertices.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology NNReal

namespace HeightPaper.Model

noncomputable def activeLowBinCount (s : State) (b : ℝ) : ℕ :=
  (s.active.filter fun v ↦ (s.tree.depth v : ℝ) ≤ b).card

theorem activeLowBinCount_le_infectious (s : State) (b : ℝ) :
    activeLowBinCount s b ≤ infectious s := Finset.card_filter_le _ _

theorem infectious_le_low_add_tail (s : State) (b : ℝ) :
    infectious s ≤ activeLowBinCount s b + activeTailCount s b := by
  classical
  let L := s.active.filter fun v ↦ (s.tree.depth v : ℝ) ≤ b
  let U := s.active.filter fun v ↦ b ≤ (s.tree.depth v : ℝ)
  have hsub : s.active ⊆ L ∪ U := by
    intro v hv
    rcases le_total (s.tree.depth v : ℝ) b with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, h⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le L U)

/-- Any sublinear logarithmic tail exponent yields low-bin exponent one on
the actual active event. The positive macroscopic population is proved from
the epidemic rates, rather than assumed as another profile estimate. -/
theorem activeLowBinCount_log_convergence_of_tail
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) (b : ℕ → ℝ) {l T f : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l)) (hf : f < 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    (htail : ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeTailCount s (b n)) / Real.log n - f|})
      atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeLowBinCount s (b n)) / Real.log n - 1|})
      atTop (𝓝 0) := by
  let μ : ℕ → Measure State := fun n ↦ activeStateMeasure (rates n) n (horizon n)
  let ℓ := vanishingProbabilityFilter μ
  let scale : (Σ _ : ℕ, State) → ℝ := fun i ↦ i.1
  have hs : Tendsto scale ℓ atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_index_vanishingProbabilityFilter μ)
  have hi : Tendsto (fun i : Σ _ : ℕ, State ↦ (infectious i.2 : ℝ) / i.1)
      ℓ (𝓝 (fluidInfectiousRaw l T)) := by
    apply (tendsto_vanishingProbabilityFilter_iff μ _ _).mpr
    intro ε hε
    simpa only [μ, activeStateMeasure_real_apply, Set.mem_ofPred_eq] using
      evolve_active_infectious_concentration rates horizon hl hrates hhorizon hε
  have hlogtail : Tendsto
      (fun i : Σ _ : ℕ, State ↦ Real.log (activeTailCount i.2 (b i.1)) / Real.log i.1)
      ℓ (𝓝 f) := by
    apply (tendsto_vanishingProbabilityFilter_iff μ _ _).mpr
    intro ε hε
    simpa only [μ, activeStateMeasure_real_apply, Set.mem_ofPred_eq] using htail ε hε
  have hu : Tendsto (fun i : Σ _ : ℕ, State ↦
      (activeTailCount i.2 (b i.1) : ℝ) / i.1) ℓ (𝓝 0) :=
    tendsto_div_zero_of_log_ratio_lt_one hs
      (Eventually.of_forall fun _ ↦ Nat.cast_nonneg _) hf hlogtail
  have hlower := hi.sub hu
  simp only [sub_zero] at hlower
  have hlow : Tendsto (fun i : Σ _ : ℕ, State ↦
      (activeLowBinCount i.2 (b i.1) : ℝ) / i.1) ℓ (𝓝 (fluidInfectiousRaw l T)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hi
    · filter_upwards [hs.eventually_gt_atTop 0] with i hn
      have hcount : (infectious i.2 : ℝ) ≤
          activeLowBinCount i.2 (b i.1) + activeTailCount i.2 (b i.1) := by
        exact_mod_cast infectious_le_low_add_tail i.2 (b i.1)
      rw [← sub_div]
      exact div_le_div_of_nonneg_right (by linarith) hn.le
    · filter_upwards [hs.eventually_gt_atTop 0] with i hn
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast activeLowBinCount_le_infectious i.2 (b i.1)) hn.le
  have hloglow := tendsto_log_ratio_one_of_div_pos hs (fluidInfectiousRaw_pos hl hT) hlow
  have hprob := (tendsto_vanishingProbabilityFilter_iff μ
    (fun i : Σ _ : ℕ, State ↦ Real.log (activeLowBinCount i.2 (b i.1)) / Real.log i.1) 1).mp hloglow
  intro ε hε
  simpa only [μ, activeStateMeasure_real_apply, Set.mem_ofPred_eq] using hprob ε hε

/-- The low-bin clause of the weak profile follows from the same Laplace
input as the positive-depth bins and tails. -/
theorem activeLowBinCount_log_convergence_of_laplace
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T x : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    (hLap : ∀ t ∈ Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp t) s) / Real.log n -
          (1 + growthFactor l * (Real.exp t - 1))|}) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeLowBinCount s
          (growthFactor l * Real.exp x * Real.log n)) / Real.log n - 1|}) atTop (𝓝 0) := by
  have hf : profileExponent l x < 1 := by
    simpa only [profileExponent_zero] using
      profileExponent_strictAntiOn hl (show (0 : ℝ) ∈ Ici 0 from le_rfl) hx.1.le hx.1
  exact activeLowBinCount_log_convergence_of_tail rates horizon _ hl hT hf hrates hhorizon
    (activeTailCount_log_convergence_of_laplace rates horizon hl hx hLap)

end HeightPaper.Model
