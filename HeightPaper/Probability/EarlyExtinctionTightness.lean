module

public import HeightPaper.Probability.EarlyExtinctionTail
public import HeightPaper.Probability.SourceSurvival

/-!
# Early-extinction tightness and negligible normalized height

The finite geometric extinction tail and the fluid-clock exclusion of
intermediate extinction jointly imply that extinct outbreaks at any time
strictly before fluid extinction have tight genuine event counts.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

/-- Event-count tails at two times split into tails of outbreaks already
extinct earlier and outbreaks that have not yet become extinct. -/
theorem evolve_extinct_tail_le_earlier_add_late (rate : ℝ≥0) (n K : ℕ)
    {i j : ℕ} (hij : i ≤ j) :
    (evolve rate n j).toMeasure.real {s | infectious s = 0 ∧ K < eventCount s} ≤
      (evolve rate n i).toMeasure.real {s | infectious s = 0 ∧ K < eventCount s} +
      (evolve rate n j).toMeasure.real {s | infectious s = 0 ∧ i < eventCount s} := by
  rw [← pathMeasure_event_at rate n j j le_rfl {s | infectious s = 0 ∧ K < eventCount s},
    ← pathMeasure_event_at rate n j i hij {s | infectious s = 0 ∧ K < eventCount s},
    ← pathMeasure_event_at rate n j j le_rfl {s | infectious s = 0 ∧ i < eventCount s}]
  apply le_trans _ (measureReal_union_le _ _)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {p : FinitePath j |
    infectious (p.eval j) = 0 ∧ K < eventCount (p.eval j)} from trivial)
  intro p hp
  have hs := (mem_support_pathLaw_iff p).mp hp.2
  by_cases hi : infectious (p.eval i) = 0
  · apply Or.inl
    have he := hs.absorbed_stable hij le_rfl (Finset.card_eq_zero.mp hi)
    exact ⟨hi, by simpa only [he] using hp.1.2⟩
  · exact Or.inr ⟨hp.1.1, hs.active_earlier_lt_eventCount hij le_rfl
      (Nat.pos_of_ne_zero hi) hp.1.1⟩

/-- The early geometric bound remains valid when the requested tail starts
past the early horizon, because the corresponding event is then impossible. -/
theorem evolve_late_extinction_le_geometric_all (rate : ℝ≥0) (n horizon K : ℕ)
    {R q : ℝ} (hR : 0 ≤ R) (hq : 0 < q) (hq1 : q < 1) (hRq : 1 < R * q)
    (hpressure : R ≤ (rate : ℝ) * (n - horizon : ℕ)) :
    (evolve rate n horizon).toMeasure.real {s | infectious s = 0 ∧ K < eventCount s} ≤
      geometricContraction R q ^ K / (1 - geometricContraction R q) := by
  by_cases hK : K ≤ horizon
  · exact evolve_late_extinction_le_geometric rate n horizon K hR hq hq1 hRq hpressure hK
  · have hz : (evolve rate n horizon).toMeasure {s | infectious s = 0 ∧ K < eventCount s} = 0 := by
      apply (PMF.toMeasure_apply_eq_zero_iff _ (show MeasurableSet {s : State |
        infectious s = 0 ∧ K < eventCount s} from trivial)).mpr
      apply Set.disjoint_left.mpr
      intro s hs he
      have hb := evolve_eventCount_le hs
      have hk : K < eventCount s := he.2
      omega
    simp only [measureReal_def, hz, ENNReal.toReal_zero]
    exact div_nonneg (pow_nonneg (geometricContraction_pos hR hq).le _)
      (sub_pos.mpr (geometricContraction_lt_one hR hq hq1 hRq)).le

/-- Worst possible early infection pressure has its deterministic positive limit. -/
theorem tendsto_early_pressure (rates : ℕ → ℝ≥0) {l δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ ↦ (rates n : ℝ) * (n - ⌊δ * n⌋₊ : ℕ))
      atTop (𝓝 (l * (1 - δ))) := by
  have hfrac : Tendsto (fun n : ℕ ↦ ((n - ⌊δ * n⌋₊ : ℕ) : ℝ) / n)
      atTop (𝓝 (1 - δ)) := by
    apply ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_floor_fraction hδ)).congr'
    filter_upwards [(tendsto_floor_fraction hδ).eventually (Iio_mem_nhds hδ1),
      eventually_gt_atTop 0] with n hn hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hfloor : ⌊δ * n⌋₊ ≤ n := by
      exact_mod_cast ((div_lt_one hnR).mp hn).le
    rw [Nat.cast_sub hfloor, sub_div, div_self hnR.ne']
  apply (hrates.mul hfrac).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- Any diverging genuine-event cutoff captures all early extinct outbreaks
with probability tending to one. No branching coupling is assumed. -/
theorem evolve_extinct_eventCount_tail_tendsto_zero
    (rates : ℕ → ℝ≥0) (horizon cutoff : ℕ → ℕ) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    (hcutoff : Tendsto cutoff atTop atTop) :
    Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
      {s | infectious s = 0 ∧ cutoff n < eventCount s}) atTop (𝓝 0) := by
  have hl0 : 0 < l := zero_lt_one.trans hl
  obtain ⟨R, hR1, hRl⟩ := exists_between hl
  have hR : 0 < R := zero_lt_one.trans hR1
  have hRl' : R / l < 1 := (div_lt_one hl0).mpr hRl
  obtain ⟨c, hRc, hc1⟩ := exists_between hRl'
  have hc0 : 0 < c := (div_pos hR hl0).trans hRc
  let δ := min T (1 - c) / 2
  have hmin : 0 < min T (1 - c) := lt_min hT.1 (sub_pos.mpr hc1)
  have hδ : 0 < δ := half_pos hmin
  have hδT : δ < T := by have := min_le_left T (1 - c); dsimp [δ]; linarith
  have hδc : δ + c < 1 := by have := min_le_right T (1 - c); dsimp [δ]; linarith
  have hδ1 : δ < 1 := by linarith
  have hpressure : R < l * (1 - δ) := by
    have hRc' := (div_lt_iff₀ hl0).mp hRc
    have hh := mul_lt_mul_of_pos_left (show c < 1 - δ by linarith) hl0
    nlinarith
  obtain ⟨q, hqlo, hq1⟩ := exists_between ((div_lt_one hR).mpr hR1)
  have hq : 0 < q := (one_div_pos.mpr hR).trans hqlo
  have hRq : 1 < R * q := by
    have hh := (div_lt_iff₀ hR).mp hqlo
    nlinarith
  have hρ0 := geometricContraction_pos hR.le hq
  have hρ1 := geometricContraction_lt_one hR.le hq hq1 hRq
  have hgeom : Tendsto (fun n ↦ geometricContraction R q ^ cutoff n /
      (1 - geometricContraction R q)) atTop (𝓝 0) := by
    simpa only [zero_div, Function.comp_apply] using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).comp hcutoff).div_const
      (1 - geometricContraction R q)
  have hlate := evolve_late_extinction_tendsto_zero rates horizon hl hδ hT.2 hrates hhorizon
  have hlim := hgeom.add hlate
  simp only [add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hlim
  filter_upwards [(tendsto_early_pressure rates hδ.le hδ1 hrates).eventually (Ioi_mem_nhds hpressure),
    (tendsto_floor_fraction hδ.le).eventually_lt hhorizon hδT, eventually_gt_atTop 0]
    with n hn hp hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have htime : ⌊δ * n⌋₊ ≤ horizon n := by
    exact_mod_cast ((div_lt_div_iff_of_pos_right hnR).mp hp).le
  have hcomp := evolve_extinct_tail_le_earlier_add_late (rates n) n (cutoff n) htime
  have hearly := evolve_late_extinction_le_geometric_all (rates n) n ⌊δ * n⌋₊ (cutoff n)
    hR.le hq hq1 hRq hn.le
  have hlatebound : (evolve (rates n) n (horizon n)).toMeasure.real
      {s | infectious s = 0 ∧ ⌊δ * n⌋₊ < eventCount s} ≤
      (evolve (rates n) n (horizon n)).toMeasure.real
      {s | infectious s = 0 ∧ δ ≤ (eventCount s : ℝ) / n} := by
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro s hs
    refine ⟨hs.1, ?_⟩
    apply (le_div_iff₀ hnR).mpr
    have hh : (⌊δ * n⌋₊ : ℝ) + 1 ≤ eventCount s := by exact_mod_cast hs.2
    exact (Nat.lt_floor_add_one (δ * n)).le.trans hh
  exact hcomp.trans (add_le_add hearly hlatebound)

/-- Tree height never exceeds the number of genuine epidemic events. -/
theorem height_le_eventCount (s : State) : height s ≤ eventCount s := by
  have hh := Tree.height_lt_size s.tree
  change height s < s.vertices at hh
  have hi := infectious_le_vertices s
  unfold eventCount
  omega

/-- The height of an outbreak already extinct before fluid extinction is
negligible at logarithmic population scale. -/
theorem evolve_extinct_height_div_log_tendsto_zero
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real
      {s | infectious s = 0 ∧ ε ≤ |(height s : ℝ) / Real.log n|}) atTop (𝓝 0) := by
  let cutoff : ℕ → ℕ := fun n ↦ ⌊(ε / 2) * Real.log n⌋₊
  have hcutoff : Tendsto cutoff atTop atTop := tendsto_nat_floor_atTop.comp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (half_pos hε))
  have htail := evolve_extinct_eventCount_tail_tendsto_zero rates horizon cutoff hl hT hrates hhorizon hcutoff
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ htail
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos hnR
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro s hs
  refine ⟨hs.1, ?_⟩
  have hh : ε * Real.log n ≤ height s := by
    have hs' : ε ≤ |(height s : ℝ) / Real.log n| := hs.2
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hlog.le)] at hs'
    exact (le_div_iff₀ hlog).mp hs'
  have hfloor := Nat.floor_le (mul_nonneg (half_pos hε).le hlog.le)
  have hhalf : ε / 2 * Real.log n < ε * Real.log n :=
    mul_lt_mul_of_pos_right (half_lt_self hε) hlog
  have hheight : (height s : ℝ) ≤ eventCount s := by exact_mod_cast height_le_eventCount s
  have hk : (cutoff n : ℝ) < eventCount s := (hfloor.trans_lt hhalf).trans_le (hh.trans hheight)
  exact_mod_cast hk

/-- Any terminal observable on the source's early-extinction event equals the
same observable at the state immediately before the cutoff, which is absorbed. -/
theorem terminal_sourceExtinction_event_probability_eq {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (rate : ℝ≥0) (n : ℕ)
    (hcut : 0 < sourceCutoff l δ n) (A : Set State) :
    (terminalStateMeasure rate n).real {s | s ∉ sourceSurvivalEvent l δ n ∧ s ∈ A} =
      (evolve rate n (sourceCutoff l δ n - 1)).toMeasure.real {s | infectious s = 0 ∧ s ∈ A} := by
  have hk : sourceCutoff l δ n - 1 ≤ 2 * n + 1 := by
    have := sourceCutoff_le_steps hl hδ n
    omega
  change (evolve rate n (2 * n + 1)).toMeasure.real _ = _
  rw [← pathMeasure_event_at rate n (2 * n + 1) (2 * n + 1) le_rfl,
    ← pathMeasure_event_at rate n (2 * n + 1) (sourceCutoff l δ n - 1) hk]
  apply measureReal_congr
  filter_upwards [ae_supportedPath rate n (2 * n + 1)] with p hp
  apply propext
  have hiff := sourceSurvivalEvent_iff_active hl hδ hp hcut
  constructor
  · rintro ⟨hs, hA⟩
    have ha : (p.eval (sourceCutoff l δ n - 1)).active = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (fun h ↦ hs (hiff.mpr h))
    have heq := hp.absorbed_stable hk le_rfl ha
    exact ⟨Finset.card_eq_zero.mpr ha, by simpa only [heq] using hA⟩
  · rintro ⟨hz, hA⟩
    have ha : (p.eval (sourceCutoff l δ n - 1)).active = ∅ := Finset.card_eq_zero.mp hz
    have heq := hp.absorbed_stable hk le_rfl ha
    refine ⟨?_, ?_⟩
    · intro hs
      exact (Finset.not_nonempty_iff_eq_empty.mpr ha) (hiff.mp hs)
    · simpa only [heq] using hA

/-- The actual terminal height is negligible on the paper's early-extinction
cutoff event. This supplies the extinction estimate needed for the main height
mixture without assuming a stronger finite weak limit for the unscaled height. -/
theorem sourceExtinction_height_div_log_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (terminalStateMeasure (rates n) n).real
      {s | s ∉ sourceSurvivalEvent l δ n ∧ ε ≤ |(height s : ℝ) / Real.log n|})
      atTop (𝓝 0) := by
  let T := (1 - δ) * fluidExtinctionTime l
  have hT0 : 0 < T := mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
  have hTt : T < fluidExtinctionTime l := by
    dsimp [T]
    nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  have hfloor : Tendsto (fun n : ℕ ↦ (sourceCutoff l δ n : ℝ) / n) atTop (𝓝 T) :=
    tendsto_floor_fraction hT0.le
  have htime : Tendsto (fun n : ℕ ↦ ((sourceCutoff l δ n - 1 : ℕ) : ℝ) / n)
      atTop (𝓝 T) := by
    have hh := hfloor.sub (tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [sourceCutoff_pos_eventually hl hδ] with n hn
    rw [Nat.cast_sub (by omega : 1 ≤ sourceCutoff l δ n), Nat.cast_one, sub_div]
  have h := evolve_extinct_height_div_log_tendsto_zero rates
    (fun n ↦ sourceCutoff l δ n - 1) hl ⟨hT0, hTt⟩ hrates htime hε
  apply h.congr'
  filter_upwards [sourceCutoff_pos_eventually hl hδ] with n hn
  exact (terminal_sourceExtinction_event_probability_eq hl hδ (rates n) n hn
    {s | ε ≤ |(height s : ℝ) / Real.log n|}).symm

end HeightPaper.Model
