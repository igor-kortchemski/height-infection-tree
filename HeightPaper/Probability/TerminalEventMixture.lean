module

public import HeightPaper.Probability.FunctionalFluid
public import HeightPaper.Probability.TerminalFluid
public import HeightPaper.Model.HeightPotentialBounds

/-!
# Macroscopic total event count on the two extinction branches

The source's early-extinction event has a tight unscaled event count.  At the
linear scale this gives a zero branch, paired with the fluid extinction time on
the surviving branch.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal Classical

namespace HeightPaper.Model

/-- A later cutoff (smaller `δ`) gives a smaller terminal survival event. -/
theorem sourceSurvivalEvent_mono_delta {l δ₁ δ₂ : ℝ} (hl : 1 < l)
    (hδ : δ₁ ≤ δ₂) (n : ℕ) :
    sourceSurvivalEvent l δ₁ n ⊆ sourceSurvivalEvent l δ₂ n := by
  have hτ : 0 ≤ fluidExtinctionTime l := (fluidExtinctionTime_pos hl).le
  have hscale : 0 ≤ fluidExtinctionTime l * (n : ℝ) :=
    mul_nonneg hτ (Nat.cast_nonneg n)
  have hfloor : sourceCutoff l δ₂ n ≤ sourceCutoff l δ₁ n := by
    unfold sourceCutoff
    apply Nat.floor_mono
    nlinarith
  intro s hs
  exact hfloor.trans hs

/-- The terminal cutoff classifications for any two admissible parameters
agree in probability. -/
theorem sourceSurvivalEvent_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ₁ δ₂ : ℝ} (hl : 1 < l)
    (hδ₁ : δ₁ ∈ Ioo (0 : ℝ) 1) (hδ₂ : δ₂ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ (terminalStateMeasure (rates n) n).real
      {s | (s ∈ sourceSurvivalEvent l δ₁ n) ≠
        (s ∈ sourceSurvivalEvent l δ₂ n)}) atTop (𝓝 0) := by
  by_cases hδ : δ₁ ≤ δ₂
  · have hsub := sourceSurvivalEvent_mono_delta hl hδ
    have hdiff := (sourceSurvivalEvent_probability_tendsto rates hl hδ₂ hrates).sub
      (sourceSurvivalEvent_probability_tendsto rates hl hδ₁ hrates)
    simp only [sub_self] at hdiff
    apply hdiff.congr'
    filter_upwards [] with n
    have hset : {s : State | (s ∈ sourceSurvivalEvent l δ₁ n) ≠
          (s ∈ sourceSurvivalEvent l δ₂ n)} =
        sourceSurvivalEvent l δ₂ n \ sourceSurvivalEvent l δ₁ n := by
      ext s
      constructor
      · intro hs
        have hnot : s ∉ sourceSurvivalEvent l δ₁ n := by
          intro ha
          exact hs (propext ⟨fun _ ↦ hsub n ha, fun _ ↦ ha⟩)
        have hyes : s ∈ sourceSurvivalEvent l δ₂ n := by
          by_contra hb
          exact hs (propext ⟨fun ha ↦ False.elim (hnot ha),
            fun hb' ↦ False.elim (hb hb')⟩)
        exact ⟨hyes, hnot⟩
      · rintro ⟨hb, ha⟩ heq
        exact ha (heq.mpr hb)
    rw [hset, measureReal_sdiff (hsub n)
      (measurableSet_sourceSurvivalEvent l δ₁ n) (measure_ne_top _ _)]
  · have hδ' : δ₂ ≤ δ₁ := le_of_not_ge hδ
    have hsub := sourceSurvivalEvent_mono_delta hl hδ'
    have hdiff := (sourceSurvivalEvent_probability_tendsto rates hl hδ₁ hrates).sub
      (sourceSurvivalEvent_probability_tendsto rates hl hδ₂ hrates)
    simp only [sub_self] at hdiff
    apply hdiff.congr'
    filter_upwards [] with n
    have hset : {s : State | (s ∈ sourceSurvivalEvent l δ₁ n) ≠
          (s ∈ sourceSurvivalEvent l δ₂ n)} =
        sourceSurvivalEvent l δ₁ n \ sourceSurvivalEvent l δ₂ n := by
      ext s
      constructor
      · intro hs
        have hnot : s ∉ sourceSurvivalEvent l δ₂ n := by
          intro hb
          exact hs (propext ⟨fun _ ↦ hb, fun _ ↦ hsub n hb⟩)
        have hyes : s ∈ sourceSurvivalEvent l δ₁ n := by
          by_contra ha
          exact hs (propext ⟨fun ha' ↦ False.elim (ha ha'),
            fun hb ↦ False.elim (hnot hb)⟩)
        exact ⟨hyes, hnot⟩
      · rintro ⟨ha, hb⟩ heq
        exact hb (heq.mp ha)
    rw [hset, measureReal_sdiff (hsub n)
      (measurableSet_sourceSurvivalEvent l δ₂ n) (measure_ne_top _ _)]

namespace SupportedPath

/-- Susceptible counts decrease along every supported epidemic path. -/
theorem susceptible_antitone {rate : ℝ≥0} {n steps : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n steps path) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ steps) :
    (path j).susceptible ≤ (path i).susceptible := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      exact (step_susceptible_le (hp.2 j (by omega))).trans (ih (by omega))

/-- After any cutoff no later infectious count can exceed the cutoff count
plus the number of genuine events still remaining before extinction. -/
theorem infectious_late_le_terminal_gap {rate : ℝ≥0} {n steps : ℕ}
    {path : ℕ → State} (hp : SupportedPath rate n steps path)
    (hsteps : 2 * n + 1 ≤ steps) {H k : ℕ}
    (hH : H ≤ eventCount (path steps)) (hHk : H ≤ k) (hk : k ≤ steps) :
    infectious (path k) ≤ infectious (path H) +
      (eventCount (path steps) - H) := by
  let τ := eventCount (path steps)
  by_cases hkτ : k ≤ τ
  · have hinc := hp.infectious_abs_sub_le_gap hHk hk
    have hsmall : infectious (path k) ≤ infectious (path H) + (k - H) := by
      have hh := le_abs_self ((infectious (path k) : ℝ) - infectious (path H))
      have hreal : (infectious (path k) : ℝ) ≤ infectious (path H) + ((k - H : ℕ) : ℝ) := by
        rw [Nat.cast_sub hHk]
        linarith
      exact_mod_cast hreal
    omega
  · have hτle : τ ≤ steps := evolve_eventCount_le (hp.mem_evolve le_rfl)
    have habs := hp.absorbed_at_eventCount hsteps
    have heq := hp.absorbed_stable (show τ ≤ k by omega) hk habs
    have hzero : infectious (path τ) = 0 := Finset.card_eq_zero.mpr habs
    rw [heq, hzero]
    omega

end SupportedPath

/-- The infectious count at the exact source cutoff has the deterministic
fluid value on the surviving branch. -/
theorem sourceSurvival_cutoff_infectious_fixed_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        ε ≤ |(infectious (q.eval (sourceCutoff l δ n)) : ℝ) / n -
          fluidInfectiousRaw l ((1 - δ) * fluidExtinctionTime l)|}) atTop (𝓝 0) := by
  let T := (1 - δ) * fluidExtinctionTime l
  have hT0 : 0 < T := mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
  have hfloor : Tendsto (fun n : ℕ ↦ (sourceCutoff l δ n : ℝ) / n)
      atTop (𝓝 T) := tendsto_floor_fraction hT0.le
  have hshift := (continuous_fluidInfectiousRaw hl).tendsto T |>.comp hfloor
  have hbad := sourceSurvival_uniform_infectious_concentration rates hl hδ hrates
    (half_pos hε)
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hbad
  filter_upwards [hshift.eventually (Metric.ball_mem_nhds _ (half_pos hε))] with n hn
  simp only [Real.dist_eq, Function.comp_apply] at hn
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro q hq
  refine ⟨hq.1, sourceCutoff l δ n, le_rfl, ?_⟩
  have htri := abs_add_le
    ((infectious (q.eval (sourceCutoff l δ n)) : ℝ) / n -
      fluidInfectiousRaw l ((sourceCutoff l δ n : ℝ) / n))
    (fluidInfectiousRaw l ((sourceCutoff l δ n : ℝ) / n) - fluidInfectiousRaw l T)
  have heq : (infectious (q.eval (sourceCutoff l δ n)) : ℝ) / n -
      fluidInfectiousRaw l ((sourceCutoff l δ n : ℝ) / n) +
      (fluidInfectiousRaw l ((sourceCutoff l δ n : ℝ) / n) - fluidInfectiousRaw l T) =
      (infectious (q.eval (sourceCutoff l δ n)) : ℝ) / n - fluidInfectiousRaw l T := by ring
  rw [heq] at htri
  have hfirst : ε ≤ |(infectious (q.eval (sourceCutoff l δ n)) : ℝ) / n -
      fluidInfectiousRaw l T| := hq.2
  change ε / 2 ≤ |(infectious (q.eval (sourceCutoff l δ n)) : ℝ) / n -
      fluidInfectiousRaw l ((sourceCutoff l δ n : ℝ) / n)|
  linarith

/-- On source survival, every infectious count after the cutoff is bounded
by its fluid value at the cutoff plus the macroscopic time remaining until
fluid extinction, up to an arbitrarily small error. -/
theorem sourceSurvival_late_infectious_upper
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        ∃ k, sourceCutoff l δ n ≤ k ∧ k ≤ 2 * n + 1 ∧
          fluidInfectiousRaw l ((1 - δ) * fluidExtinctionTime l) +
            (fluidExtinctionTime l - (1 - δ) * fluidExtinctionTime l) + ε ≤
              (infectious (q.eval k) : ℝ) / n}) atTop (𝓝 0) := by
  let T := (1 - δ) * fluidExtinctionTime l
  let H : ℕ → ℕ := sourceCutoff l δ
  have hT0 : 0 < T := mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
  have hfloor : Tendsto (fun n : ℕ ↦ (H n : ℝ) / n) atTop (𝓝 T) :=
    tendsto_floor_fraction hT0.le
  have hA := sourceSurvival_cutoff_infectious_fixed_concentration rates hl hδ hrates
    (show 0 < ε / 4 by positivity)
  have hC : Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        ε / 4 ≤ |(eventCount (q.eval (2 * n + 1)) : ℝ) / n -
          fluidExtinctionTime l|}) atTop (𝓝 0) := by
    have hh := sourceSurvival_eventCount_concentration rates hl hδ hrates
      (show 0 < ε / 4 by positivity)
    apply hh.congr'
    apply Eventually.of_forall
    intro n
    exact (pathMeasure_event_at (rates n) n (2 * n + 1) (2 * n + 1) le_rfl _).symm
  have hsum := hA.add hC
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [hfloor.eventually (Metric.ball_mem_nhds T (show 0 < ε / 4 by positivity)),
    eventually_gt_atTop 0] with n hfloorN hn0
  simp only [Real.dist_eq] at hfloorN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  apply le_trans _ (measureReal_union_le _ _)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {q : FinitePath (2 * n + 1) |
    q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
      ∃ k, H n ≤ k ∧ k ≤ 2 * n + 1 ∧
        fluidInfectiousRaw l T + (fluidExtinctionTime l - T) + ε ≤
          (infectious (q.eval k) : ℝ) / n} from trivial)
  intro q hq
  obtain ⟨hsurv, k, hHk, hk, hbad⟩ := hq.1
  have hpath := (mem_support_pathLaw_iff q).mp hq.2
  have habs := evolve_absorbed le_rfl (hpath.mem_evolve le_rfl)
  have hτeq := eventCount_absorbed habs
  have hHτ : H n ≤ eventCount (q.eval (2 * n + 1)) := by
    rw [hτeq]
    exact hsurv
  have hLate := hpath.infectious_late_le_terminal_gap le_rfl hHτ hHk hk
  have hLateR : (infectious (q.eval k) : ℝ) / n ≤
      (infectious (q.eval (H n)) : ℝ) / n +
        ((eventCount (q.eval (2 * n + 1)) : ℝ) / n - (H n : ℝ) / n) := by
    have hh : (infectious (q.eval k) : ℝ) ≤
        (infectious (q.eval (H n)) : ℝ) +
          ((eventCount (q.eval (2 * n + 1)) - H n : ℕ) : ℝ) := by
      exact_mod_cast hLate
    rw [Nat.cast_sub hHτ] at hh
    apply (div_le_iff₀ hnR).mpr
    calc
      (infectious (q.eval k) : ℝ) ≤
          (infectious (q.eval (H n)) : ℝ) +
            ((eventCount (q.eval (2 * n + 1)) : ℝ) - H n) := hh
      _ = ((infectious (q.eval (H n)) : ℝ) / n +
          ((eventCount (q.eval (2 * n + 1)) : ℝ) / n - (H n : ℝ) / n)) * n := by
        field_simp
  by_contra hnone
  have hnotA : ¬(ε / 4 ≤ |(infectious (q.eval (H n)) : ℝ) / n -
      fluidInfectiousRaw l T|) := by
    intro ha
    exact hnone (Or.inl ⟨hsurv, ha⟩)
  have hnotC : ¬(ε / 4 ≤ |(eventCount (q.eval (2 * n + 1)) : ℝ) / n -
      fluidExtinctionTime l|) := by
    intro hc
    exact hnone (Or.inr ⟨hsurv, hc⟩)
  have hsmallA := abs_lt.mp (lt_of_not_ge hnotA)
  have hsmallC := abs_lt.mp (lt_of_not_ge hnotC)
  have hsmallH := abs_lt.mp hfloorN
  dsimp [T] at hbad hsmallA hsmallH ⊢
  linarith

/-- A source cutoff can be chosen so close to fluid extinction that both the
late-count envelope and the remaining nonnegative fluid curve are small. -/
theorem exists_sourceCutoff_small_late_envelope {l : ℝ} (hl : 1 < l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ ∈ Ioo (0 : ℝ) 1,
      fluidInfectiousRaw l ((1 - δ) * fluidExtinctionTime l) +
        (fluidExtinctionTime l - (1 - δ) * fluidExtinctionTime l) < ε / 2 ∧
      ∀ t, (1 - δ) * fluidExtinctionTime l ≤ t →
        fluidInfectious l t < ε / 2 := by
  let τ := fluidExtinctionTime l
  let f := fluidInfectiousRaw l
  have hτ : 0 < τ := fluidExtinctionTime_pos hl
  have hcont := (continuous_fluidInfectiousRaw hl).tendsto τ
  have hmem := hcont (Metric.ball_mem_nhds (f τ) (show 0 < ε / 4 by positivity))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hmem
  have hnear (t : ℝ) (ht : |t - τ| < r) : |f t| < ε / 4 := by
    have htball : t ∈ Metric.ball τ r := by simpa only [Metric.mem_ball, Real.dist_eq] using ht
    have hf := hball htball
    have hfzero : f τ = 0 := by simpa only [f, τ] using fluidInfectiousRaw_extinction hl
    rw [hfzero] at hf
    simpa only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq, sub_zero] using hf
  let d := min (r / 2) (min (ε / 4) (τ / 2))
  have hd : 0 < d := lt_min (half_pos hr)
    (lt_min (by positivity) (half_pos hτ))
  have hdr : d < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hdε : d ≤ ε / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hdτ : d < τ :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hτ)
  let δ := d / τ
  have hδ0 : 0 < δ := div_pos hd hτ
  have hδ1 : δ < 1 := (div_lt_one hτ).mpr hdτ
  have hT : (1 - δ) * τ = τ - d := by
    dsimp [δ]
    field_simp
  refine ⟨δ, ⟨hδ0, hδ1⟩, ?_, ?_⟩
  · rw [hT]
    have hnearT : |(τ - d) - τ| < r := by
      simpa only [sub_sub_cancel_left, abs_neg, abs_of_pos hd] using hdr
    have hh := hnear (τ - d) hnearT
    have hupper := (abs_lt.mp hh).2
    dsimp [f, τ] at hupper ⊢
    linarith
  · intro t ht
    rw [hT] at ht
    by_cases hafter : τ ≤ t
    · rw [fluidInfectious_eq_zero_after_extinction hl hafter]
      linarith
    · have htτ : t ≤ τ := le_of_not_ge hafter
      have ht0 : 0 ≤ t := by linarith
      have hnearT : |t - τ| < r := by
        rw [abs_of_nonpos (sub_nonpos.mpr htτ)]
        linarith
      have hh := hnear t hnearT
      rw [fluidInfectious_eq_raw hl ⟨ht0, htτ⟩]
      exact (abs_lt.mp hh).2.trans (by linarith)

/-- The total number of events is negligible at linear scale on the paper's
exact early-extinction event. -/
theorem sourceExtinction_eventCount_div_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (terminalStateMeasure (rates n) n).real
      {s | s ∉ sourceSurvivalEvent l δ n ∧
        ε ≤ (eventCount s : ℝ) / n}) atTop (𝓝 0) := by
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
  let K : ℕ → ℕ := fun n ↦ ⌊(ε / 2) * n⌋₊
  have hK : Tendsto K atTop atTop := by
    apply tendsto_nat_floor_atTop.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hε)
  have htail := evolve_extinct_eventCount_tail_tendsto_zero rates
    (fun n ↦ sourceCutoff l δ n - 1) K hl ⟨hT0, hTt⟩ hrates htime hK
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ htail
  filter_upwards [sourceCutoff_pos_eventually hl hδ, eventually_gt_atTop 0]
    with n hcut hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change (terminalStateMeasure (rates n) n).real
    {s | s ∉ sourceSurvivalEvent l δ n ∧
      s ∈ {s | ε ≤ (eventCount s : ℝ) / n}} ≤ _
  rw [terminal_sourceExtinction_event_probability_eq hl hδ (rates n) n hcut
    {s | ε ≤ (eventCount s : ℝ) / n}]
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro s hs
  refine ⟨hs.1, ?_⟩
  have hlarge : ε * n ≤ (eventCount s : ℝ) := (le_div_iff₀ hnR).mp hs.2
  have hKbound : (K n : ℝ) ≤ ε / 2 * n := Nat.floor_le (by positivity)
  exact_mod_cast (show (K n : ℝ) < eventCount s by nlinarith)

/-- On the paper's early-extinction branch, the entire infectious history is
negligible at linear population scale. -/
theorem sourceExtinction_full_infectious_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∉ sourceSurvivalEvent l δ n ∧
        ∃ k ≤ 2 * n + 1, ε ≤ (infectious (q.eval k) : ℝ) / n})
      atTop (𝓝 0) := by
  have hτ := sourceExtinction_eventCount_div_tendsto_zero rates hl hδ hrates
    (half_pos hε)
  have hτpath : Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∉ sourceSurvivalEvent l δ n ∧
        ε / 2 ≤ (eventCount (q.eval (2 * n + 1)) : ℝ) / n}) atTop (𝓝 0) := by
    apply hτ.congr'
    apply Eventually.of_forall
    intro n
    exact (pathMeasure_event_at (rates n) n (2 * n + 1) (2 * n + 1) le_rfl _).symm
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hτpath
  filter_upwards [(tendsto_one_div_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0)).eventually
      (Iio_mem_nhds (half_pos hε)), eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {q : FinitePath (2 * n + 1) |
    q.eval (2 * n + 1) ∉ sourceSurvivalEvent l δ n ∧
      ∃ k ≤ 2 * n + 1, ε ≤ (infectious (q.eval k) : ℝ) / n} from trivial)
  intro q hq
  obtain ⟨hnot, k, hk, hbad⟩ := hq.1
  have hpath := (mem_support_pathLaw_iff q).mp hq.2
  have hupper := hpath.infectious_late_le_terminal_gap le_rfl
    (Nat.zero_le _) (Nat.zero_le _) hk
  have hinit := hpath.1
  rw [hinit, infectious_initial, Nat.sub_zero] at hupper
  have hupperR : (infectious (q.eval k) : ℝ) ≤
      1 + eventCount (q.eval (2 * n + 1)) := by exact_mod_cast hupper
  have hbadR : ε * n ≤ (infectious (q.eval k) : ℝ) :=
    (le_div_iff₀ hnR).mp hbad
  refine ⟨hnot, ?_⟩
  apply (le_div_iff₀ hnR).mpr
  have hsmall : (1 : ℝ) < ε / 2 * n := (div_lt_iff₀ hnR).mp hn
  linarith

/-- The scaled terminal event count has the two macroscopic values prescribed
by the exact source survival event. -/
theorem source_terminal_eventCount_mixture_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (terminalStateMeasure (rates n) n).real
      {s | ε ≤ |(eventCount s : ℝ) / n -
        if s ∈ sourceSurvivalEvent l δ n then fluidExtinctionTime l else 0|})
      atTop (𝓝 0) := by
  have hA := sourceSurvival_eventCount_concentration rates hl hδ hrates hε
  have hE := sourceExtinction_eventCount_div_tendsto_zero rates hl hδ hrates hε
  have hsum := hA.add hE
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  apply le_trans _ (measureReal_union_le _ _)
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro s hs
  change ε ≤ |(eventCount s : ℝ) / n -
    if s ∈ sourceSurvivalEvent l δ n then fluidExtinctionTime l else 0| at hs
  by_cases hsurv : s ∈ sourceSurvivalEvent l δ n
  · simp only [ite_eq_left hsurv] at hs
    exact Or.inl ⟨hsurv, hs⟩
  · simp only [ite_eq_right hsurv, sub_zero] at hs
    have hnonneg : 0 ≤ (eventCount s : ℝ) / n := by positivity
    rw [abs_of_nonneg hnonneg] at hs
    exact Or.inr ⟨hsurv, hs⟩

/-- The terminal susceptible fraction has the final-size value on survival
and remains one on an early extinct outbreak, jointly with the source event. -/
theorem source_terminal_susceptible_mixture_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (terminalStateMeasure (rates n) n).real
      {s | ε ≤ |(s.susceptible : ℝ) / n -
        if s ∈ sourceSurvivalEvent l δ n then finalSusceptibleFraction l else 1|})
      atTop (𝓝 0) := by
  have hτ := source_terminal_eventCount_mixture_concentration rates hl hδ hrates hε
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hτ
  filter_upwards [(tendsto_one_div_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0)).eventually
      (Iio_mem_nhds hε), eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {s : State |
    ε ≤ |(s.susceptible : ℝ) / n -
      if s ∈ sourceSurvivalEvent l δ n then finalSusceptibleFraction l else 1|} from trivial)
  intro s hs
  have hpop := evolve_population hs.2
  have hz : infectious s = 0 :=
    Finset.card_eq_zero.mpr (evolve_absorbed (by omega : 2 * n + 1 ≤ 2 * n + 1) hs.2)
  have hb : 2 * (s.susceptible : ℝ) + eventCount s = 2 * n + 1 := by
    have hh := count_balance hpop
    rw [hz, zero_add] at hh
    exact_mod_cast hh
  let A : ℝ := if s ∈ sourceSurvivalEvent l δ n then fluidExtinctionTime l else 0
  let B : ℝ := if s ∈ sourceSurvivalEvent l δ n then finalSusceptibleFraction l else 1
  have htarget : B = 1 - A / 2 := by
    dsimp [A, B]
    split_ifs
    · unfold fluidExtinctionTime
      ring
    · ring
  have heq : (s.susceptible : ℝ) / n - B =
      -(((eventCount s : ℝ) / n - A) / 2) + 1 / (2 * n) := by
    rw [htarget]
    field_simp
    nlinarith
  have htri := abs_add_le (-(((eventCount s : ℝ) / n - A) / 2)) (1 / (2 * n))
  rw [← heq, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * n))] at htri
  have hdiv : (1 : ℝ) / (2 * n) = (1 / n) / 2 := by ring
  rw [hdiv] at htri
  have hbad : ε ≤ |(s.susceptible : ℝ) / n - B| := hs.1
  change ε ≤ |(eventCount s : ℝ) / n - A|
  linarith

/-- The full finite infectious history follows the nonnegative fluid curve
multiplied by the exact source survival indicator. This is uniform over every
event time available in the terminal history. -/
theorem source_full_infectious_functional_mixture_concentration
    (rates : ℕ → ℝ≥0) {l : ℝ} (hl : 1 < l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
        {q | ∃ k ≤ 2 * n + 1,
          ε ≤ |(infectious (q.eval k) : ℝ) / n -
            if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
              fluidInfectious l ((k : ℝ) / n) else 0|}) atTop (𝓝 0) := by
  classical
  let τ := fluidExtinctionTime l
  obtain ⟨δ₀, hδ₀, henv, hcurve⟩ :=
    exists_sourceCutoff_small_late_envelope hl (half_pos hε)
  let δ := δ₀ / 2
  have hδ : δ ∈ Ioo (0 : ℝ) 1 := by
    dsimp [δ]
    constructor <;> linarith [hδ₀.1, hδ₀.2]
  let T₀ := (1 - δ₀) * τ
  let T := (1 - δ) * τ
  have hτ : 0 < τ := fluidExtinctionTime_pos hl
  have hT₀pos : 0 < T₀ := mul_pos (sub_pos.mpr hδ₀.2) hτ
  have hTpos : 0 < T := mul_pos (sub_pos.mpr hδ.2) hτ
  have hT₀T : T₀ < T := by dsimp [T₀, T, δ]; nlinarith [mul_pos hδ₀.1 hτ]
  have hTτ : T < τ := by dsimp [T, δ]; nlinarith [mul_pos hδ₀.1 hτ]
  have hraw₀ : 0 < fluidInfectiousRaw l T₀ :=
    fluidInfectiousRaw_pos hl ⟨hT₀pos, hT₀T.trans hTτ⟩
  have hgap₀ : τ - T₀ < ε / 4 := by
    have hh : fluidInfectiousRaw l T₀ + (τ - T₀) < ε / 4 := by
      dsimp [T₀, τ] at henv ⊢
      linarith
    linarith
  have hrawT : fluidInfectiousRaw l T < ε / 4 := by
    have hh := hcurve T (by simpa only [T₀, τ] using hT₀T.le)
    rw [fluidInfectious_eq_raw hl ⟨hTpos.le, hTτ.le⟩] at hh
    dsimp [T, τ] at hh ⊢
    linarith
  have hB : fluidInfectiousRaw l T + (τ - T) < ε / 2 := by
    have hgap : τ - T ≤ τ - T₀ := by linarith
    linarith
  let H : ℕ → ℕ := sourceCutoff l δ
  have hfloor : Tendsto (fun n : ℕ ↦ (H n : ℝ) / n) atTop (𝓝 T) :=
    tendsto_floor_fraction hTpos.le
  have hEarly := sourceSurvival_uniform_infectious_mixture_concentration
    rates hl hδ hrates (half_pos hε)
  have hLate := sourceSurvival_late_infectious_upper rates hl hδ hrates
    (show 0 < ε / 4 by positivity)
  have hExt := sourceExtinction_full_infectious_concentration rates hl hδ hrates
    (half_pos hε)
  have hsum := (hEarly.add hLate).add hExt
  simp only [add_zero] at hsum
  refine ⟨δ, hδ, ?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [hfloor.eventually (Ioi_mem_nhds hT₀T), eventually_gt_atTop 0]
    with n hfloorN hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hHupper : (H n : ℝ) / n ≤ τ := by
    have hh : (H n : ℝ) ≤ T * n := Nat.floor_le (by positivity)
    have hh' : (H n : ℝ) / n ≤ T := (div_le_iff₀ hnR).mpr hh
    exact hh'.trans hTτ.le
  let surv : Set (FinitePath (2 * n + 1)) :=
    {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n}
  let A : Set (FinitePath (2 * n + 1)) :=
    {q | ∃ k ≤ H n,
      ε / 2 ≤ |(infectious (q.eval k) : ℝ) / n -
        if q ∈ surv then fluidInfectiousRaw l ((k : ℝ) / n) else 0|}
  let B : Set (FinitePath (2 * n + 1)) :=
    {q | q ∈ surv ∧ ∃ k, H n ≤ k ∧ k ≤ 2 * n + 1 ∧
      fluidInfectiousRaw l T + (τ - T) + ε / 4 ≤ (infectious (q.eval k) : ℝ) / n}
  let C : Set (FinitePath (2 * n + 1)) :=
    {q | q ∉ surv ∧ ∃ k ≤ 2 * n + 1,
      ε / 2 ≤ (infectious (q.eval k) : ℝ) / n}
  have hbound : (pathMeasure (rates n) n (2 * n + 1)).real
      {q | ∃ k ≤ 2 * n + 1,
        ε ≤ |(infectious (q.eval k) : ℝ) / n -
          if q ∈ surv then fluidInfectious l ((k : ℝ) / n) else 0|} ≤
      (pathMeasure (rates n) n (2 * n + 1)).real A +
        (pathMeasure (rates n) n (2 * n + 1)).real B +
        (pathMeasure (rates n) n (2 * n + 1)).real C := by
    calc
      _ ≤ (pathMeasure (rates n) n (2 * n + 1)).real ((A ∪ B) ∪ C) := by
        apply measureReal_mono (h₂ := measure_ne_top _ _)
        intro q hq
        obtain ⟨k, hk, hbad⟩ := hq
        by_cases hkH : k ≤ H n
        · have hkτ : (k : ℝ) / n ≤ τ :=
            (div_le_div_of_nonneg_right (by exact_mod_cast hkH) hnR.le).trans hHupper
          have hf := fluidInfectious_eq_raw hl
            (show (k : ℝ) / n ∈ Icc 0 τ from ⟨by positivity, hkτ⟩)
          rw [hf] at hbad
          have hfirst : ε / 2 ≤ |(infectious (q.eval k) : ℝ) / n -
              if q ∈ surv then fluidInfectiousRaw l ((k : ℝ) / n) else 0| := by
            linarith
          exact Or.inl (Or.inl ⟨k, hkH, hfirst⟩)
        · have hHk : H n ≤ k := by omega
          by_cases hs : q ∈ surv
          · have htime : T₀ ≤ (k : ℝ) / n :=
              hfloorN.le.trans
                (div_le_div_of_nonneg_right (by exact_mod_cast hHk) hnR.le)
            have hcurveK : fluidInfectious l ((k : ℝ) / n) < ε / 4 := by
              have hh := hcurve _ (by simpa only [T₀, τ] using htime)
              linarith
            have hnonnegI : 0 ≤ (infectious (q.eval k) : ℝ) / n := by positivity
            have hnonnegF : 0 ≤ fluidInfectious l ((k : ℝ) / n) :=
              le_max_right _ _
            have htarget : fluidInfectiousRaw l T + (τ - T) + ε / 4 ≤
                (infectious (q.eval k) : ℝ) / n := by
              by_contra hno
              have hi : (infectious (q.eval k) : ℝ) / n <
                  fluidInfectiousRaw l T + (τ - T) + ε / 4 := lt_of_not_ge hno
              have htri := abs_sub_le ((infectious (q.eval k) : ℝ) / n)
                (0 : ℝ) (fluidInfectious l ((k : ℝ) / n))
              simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hnonnegI,
                abs_of_nonneg hnonnegF] at htri
              simp only [ite_eq_left hs] at hbad
              linarith
            exact Or.inl (Or.inr ⟨hs, k, hHk, hk, htarget⟩)
          · have hnonneg : 0 ≤ (infectious (q.eval k) : ℝ) / n := by positivity
            simp only [ite_eq_right hs, sub_zero, abs_of_nonneg hnonneg] at hbad
            exact Or.inr ⟨hs, k, hk, by linarith⟩
      _ ≤ (pathMeasure (rates n) n (2 * n + 1)).real (A ∪ B) +
          (pathMeasure (rates n) n (2 * n + 1)).real C := measureReal_union_le _ _
      _ ≤ _ := by
        have hh : (pathMeasure (rates n) n (2 * n + 1)).real (A ∪ B) ≤
            (pathMeasure (rates n) n (2 * n + 1)).real A +
              (pathMeasure (rates n) n (2 * n + 1)).real B := measureReal_union_le A B
        have hhh := add_le_add_right hh
          ((pathMeasure (rates n) n (2 * n + 1)).real C)
        calc
          _ = (pathMeasure (rates n) n (2 * n + 1)).real C +
              (pathMeasure (rates n) n (2 * n + 1)).real (A ∪ B) := by ac_rfl
          _ ≤ (pathMeasure (rates n) n (2 * n + 1)).real C +
              ((pathMeasure (rates n) n (2 * n + 1)).real A +
                (pathMeasure (rates n) n (2 * n + 1)).real B) := hhh
          _ = _ := by ac_rfl
  exact hbound

/-- The functional infectious mixture holds for each fixed source cutoff,
rather than a cutoff chosen after the error tolerance. -/
theorem source_full_infectious_functional_mixture_concentration_fixed_cutoff
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | ∃ k ≤ 2 * n + 1,
        ε ≤ |(infectious (q.eval k) : ℝ) / n -
          if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
            fluidInfectious l ((k : ℝ) / n) else 0|}) atTop (𝓝 0) := by
  obtain ⟨δ₀, hδ₀, hconv⟩ :=
    source_full_infectious_functional_mixture_concentration rates hl hrates hε
  have hdis₀ := sourceSurvivalEvent_disagreement_tendsto_zero rates hl hδ₀ hδ hrates
  have hdis : Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | (q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ₀ n) ≠
        (q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n)}) atTop (𝓝 0) := by
    apply hdis₀.congr'
    filter_upwards [] with n
    change (evolve (rates n) n (2 * n + 1)).toMeasure.real _ = _
    rw [← pathMeasure_event_at (rates n) n (2 * n + 1) (2 * n + 1) le_rfl]
    rfl
  have hsum := hconv.add hdis
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [] with n
  let μ := pathMeasure (rates n) n (2 * n + 1)
  let A : Set (FinitePath (2 * n + 1)) :=
    {q | ∃ k ≤ 2 * n + 1,
      ε ≤ |(infectious (q.eval k) : ℝ) / n -
        if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ₀ n then
          fluidInfectious l ((k : ℝ) / n) else 0|}
  let B : Set (FinitePath (2 * n + 1)) :=
    {q | (q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ₀ n) ≠
      (q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n)}
  calc
    μ.real {q | ∃ k ≤ 2 * n + 1,
      ε ≤ |(infectious (q.eval k) : ℝ) / n -
        if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
          fluidInfectious l ((k : ℝ) / n) else 0|} ≤ μ.real (A ∪ B) := by
        apply measureReal_mono (h₂ := measure_ne_top _ _)
        intro q hq
        by_cases heq : (q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ₀ n) =
            (q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n)
        · left
          obtain ⟨k, hk, hbad⟩ := hq
          refine ⟨k, hk, ?_⟩
          by_cases hs : q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ₀ n
          · have hs' : q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n :=
              heq.mp hs
            simp only [FinitePath.eval_last] at hs hs' hbad ⊢
            simpa [hs, hs'] using hbad
          · have hs' : q.eval (2 * n + 1) ∉ sourceSurvivalEvent l δ n := by
              intro hs'
              exact hs (heq.mpr hs')
            simp only [FinitePath.eval_last] at hs hs' hbad ⊢
            simpa [hs, hs'] using hbad
        · exact Or.inr heq
    _ ≤ μ.real A + μ.real B := measureReal_union_le A B

/-- A cutoff can be chosen whose fluid susceptible value is arbitrarily close
to the final susceptible fraction. The assertion is made at the actual floored
cutoff time. -/
theorem exists_sourceCutoff_small_susceptible_gap {l : ℝ} (hl : 1 < l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ ∈ Ioo (0 : ℝ) 1,
      ∀ᶠ n : ℕ in atTop,
        fluidSusceptible l ((sourceCutoff l δ n : ℝ) / n) -
          finalSusceptibleFraction l < ε := by
  let τ := fluidExtinctionTime l
  obtain ⟨δ₀, hδ₀, henv, _⟩ :=
    exists_sourceCutoff_small_late_envelope hl hε
  let T₀ := (1 - δ₀) * τ
  have hτ : 0 < τ := fluidExtinctionTime_pos hl
  have hT₀pos : 0 < T₀ := mul_pos (sub_pos.mpr hδ₀.2) hτ
  have hT₀τ : T₀ < τ := by dsimp [T₀]; nlinarith [mul_pos hδ₀.1 hτ]
  have hraw : 0 ≤ fluidInfectiousRaw l T₀ :=
    (fluidInfectiousRaw_pos hl ⟨hT₀pos, hT₀τ⟩).le
  have hidentity : 2 * (fluidSusceptible l T₀ - finalSusceptibleFraction l) =
      τ - T₀ - fluidInfectiousRaw l T₀ := by
    dsimp [τ, fluidExtinctionTime, fluidInfectiousRaw]
    ring
  have hgap : fluidSusceptible l T₀ - finalSusceptibleFraction l < ε := by
    linarith
  let δ := δ₀ / 2
  have hδ : δ ∈ Ioo (0 : ℝ) 1 := by
    dsimp [δ]
    constructor <;> linarith [hδ₀.1, hδ₀.2]
  let T := (1 - δ) * τ
  have hTpos : 0 < T := mul_pos (sub_pos.mpr hδ.2) hτ
  have hT₀T : T₀ < T := by dsimp [T₀, T, δ]; nlinarith [mul_pos hδ₀.1 hτ]
  have hfloor : Tendsto (fun n : ℕ ↦ (sourceCutoff l δ n : ℝ) / n)
      atTop (𝓝 T) := tendsto_floor_fraction hTpos.le
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hfloor.eventually (Ioi_mem_nhds hT₀T)] with n hn
  have hanti := fluidSusceptible_strictAnti hl hn
  linarith

/-- On early extinction, the complete susceptible history stays close to its
initial fraction. -/
theorem sourceExtinction_full_susceptible_one_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∉ sourceSurvivalEvent l δ n ∧
        ∃ k ≤ 2 * n + 1,
          ε ≤ |(q.eval k).susceptible / (n : ℝ) - 1|}) atTop (𝓝 0) := by
  have hterm := source_terminal_susceptible_mixture_concentration
    rates hl hδ hrates hε
  have hpath : Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | ε ≤ |(q.eval (2 * n + 1)).susceptible / (n : ℝ) -
        if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
          finalSusceptibleFraction l else 1|}) atTop (𝓝 0) := by
    apply hterm.congr'
    apply Eventually.of_forall
    intro n
    exact (pathMeasure_event_at (rates n) n (2 * n + 1) (2 * n + 1) le_rfl _).symm
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hpath
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {q : FinitePath (2 * n + 1) |
    q.eval (2 * n + 1) ∉ sourceSurvivalEvent l δ n ∧
      ∃ k ≤ 2 * n + 1,
        ε ≤ |(q.eval k).susceptible / (n : ℝ) - 1|} from trivial)
  intro q hq
  obtain ⟨hnot, k, hk, hbad⟩ := hq.1
  have hp := (mem_support_pathLaw_iff q).mp hq.2
  have hupper : (q.eval k).susceptible ≤ n := by
    have hh := hp.susceptible_antitone (i := 0) (j := k) (Nat.zero_le _) hk
    simpa [hp.1, initial] using hh
  have hlower : (q.eval (2 * n + 1)).susceptible ≤ (q.eval k).susceptible :=
    hp.susceptible_antitone hk le_rfl
  have hfracUpper : (q.eval k).susceptible / (n : ℝ) ≤ 1 :=
    (div_le_one hnR).mpr (by exact_mod_cast hupper)
  have hfracFinal : (q.eval (2 * n + 1)).susceptible / (n : ℝ) ≤ 1 :=
    (div_le_one hnR).mpr (by exact_mod_cast hlower.trans hupper)
  have hfracLower : (q.eval (2 * n + 1)).susceptible / (n : ℝ) ≤
      (q.eval k).susceptible / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hnR.le
    exact_mod_cast hlower
  change ε ≤ |(q.eval (2 * n + 1)).susceptible / (n : ℝ) -
    if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
      finalSusceptibleFraction l else 1|
  simp only [ite_eq_right hnot]
  rw [abs_of_nonpos (sub_nonpos.mpr hfracUpper)] at hbad
  rw [abs_of_nonpos (sub_nonpos.mpr hfracFinal)]
  linarith

/-- Between the cutoff and fluid extinction, monotonicity traps the susceptible
count between its cutoff and terminal values. -/
theorem SupportedPath.susceptible_late_error_of_endpoint_errors
    {rate : ℝ≥0} {l : ℝ} (hl : 1 < l) {n H k : ℕ}
    (hn : 0 < n) (hHk : H ≤ k) (hk : k ≤ 2 * n + 1)
    (htime : (k : ℝ) / n ≤ fluidExtinctionTime l)
    (q : FinitePath (2 * n + 1))
    (hp : SupportedPath rate n (2 * n + 1) q.eval)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : fluidSusceptible l ((H : ℝ) / n) -
      finalSusceptibleFraction l < ε / 4)
    (hbad : ε ≤ |(q.eval k).susceptible / (n : ℝ) -
      fluidSusceptible l ((k : ℝ) / n)|) :
    ε / 4 ≤ |(q.eval H).susceptible / (n : ℝ) -
        fluidSusceptible l ((H : ℝ) / n)| ∨
      ε / 4 ≤ |(q.eval (2 * n + 1)).susceptible / (n : ℝ) -
        finalSusceptibleFraction l| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hHkR : (H : ℝ) / n ≤ (k : ℝ) / n :=
    div_le_div_of_nonneg_right (by exact_mod_cast hHk) hnR.le
  have hGupper := (fluidSusceptible_strictAnti hl).antitone hHkR
  have hGlower := (fluidSusceptible_strictAnti hl).antitone htime
  rw [fluidSusceptible_at_extinction hl] at hGlower
  have hSupper : (q.eval k).susceptible / (n : ℝ) ≤
      (q.eval H).susceptible / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hnR.le
    exact_mod_cast hp.susceptible_antitone hHk hk
  have hSlower : (q.eval (2 * n + 1)).susceptible / (n : ℝ) ≤
      (q.eval k).susceptible / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hnR.le
    exact_mod_cast hp.susceptible_antitone hk le_rfl
  by_contra hnone
  have hnotA : ¬(ε / 4 ≤ |(q.eval H).susceptible / (n : ℝ) -
      fluidSusceptible l ((H : ℝ) / n)|) := by
    intro ha
    exact hnone (Or.inl ha)
  have hnotB : ¬(ε / 4 ≤ |(q.eval (2 * n + 1)).susceptible / (n : ℝ) -
      finalSusceptibleFraction l|) := by
    intro hb
    exact hnone (Or.inr hb)
  have hA := abs_lt.mp (lt_of_not_ge hnotA)
  have hB := abs_lt.mp (lt_of_not_ge hnotB)
  have hC : |(q.eval k).susceptible / (n : ℝ) -
      fluidSusceptible l ((k : ℝ) / n)| < ε :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  exact (not_lt.mpr hbad) hC

/-- The susceptible trajectory follows the paper's mixture uniformly up to
the macroscopic fluid extinction time, for a suitably close auxiliary cutoff. -/
theorem exists_source_full_susceptible_functional_mixture_concentration
    (rates : ℕ → ℝ≥0) {l : ℝ} (hl : 1 < l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
        {q | ∃ k ≤ ⌊fluidExtinctionTime l * n⌋₊,
          ε ≤ |(q.eval k).susceptible / (n : ℝ) -
            if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
              fluidSusceptible l ((k : ℝ) / n) else 1|}) atTop (𝓝 0) := by
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨δ, hδ, hgap⟩ := exists_sourceCutoff_small_susceptible_gap hl hε4
  have hpre := sourceSurvival_uniform_susceptible_mixture_concentration
    rates hl hδ hrates hε4
  have hterminal₀ := source_terminal_susceptible_mixture_concentration
    rates hl hδ hrates hε4
  have hterminal : Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | ε / 4 ≤ |(q.eval (2 * n + 1)).susceptible / (n : ℝ) -
        if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
          finalSusceptibleFraction l else 1|}) atTop (𝓝 0) := by
    apply hterminal₀.congr'
    apply Eventually.of_forall
    intro n
    exact (pathMeasure_event_at (rates n) n (2 * n + 1) (2 * n + 1) le_rfl _).symm
  have hext := sourceExtinction_full_susceptible_one_concentration
    rates hl hδ hrates hε
  have hsum := (hpre.add hterminal).add hext
  simp only [add_zero] at hsum
  refine ⟨δ, hδ, ?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [hgap, eventually_gt_atTop 0] with n hgapN hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let H := sourceCutoff l δ n
  let J := ⌊fluidExtinctionTime l * n⌋₊
  have hJsteps : J ≤ 2 * n + 1 := by
    apply Nat.floor_le_of_le
    have hτ := fluidExtinctionTime_lt_two hl
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hτ.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hJtime : (J : ℝ) / n ≤ fluidExtinctionTime l := by
    have hh : (J : ℝ) ≤ fluidExtinctionTime l * n :=
      Nat.floor_le (mul_nonneg (fluidExtinctionTime_pos hl).le (Nat.cast_nonneg n))
    exact (div_le_iff₀ hnR).mpr hh
  let surv : Set (FinitePath (2 * n + 1)) :=
    {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n}
  let A : Set (FinitePath (2 * n + 1)) :=
    {q | ∃ k ≤ H, ε / 4 ≤ |(q.eval k).susceptible / (n : ℝ) -
      if q ∈ surv then fluidSusceptible l ((k : ℝ) / n) else 1|}
  let B : Set (FinitePath (2 * n + 1)) :=
    {q | ε / 4 ≤ |(q.eval (2 * n + 1)).susceptible / (n : ℝ) -
      if q ∈ surv then finalSusceptibleFraction l else 1|}
  let C : Set (FinitePath (2 * n + 1)) :=
    {q | q ∉ surv ∧ ∃ k ≤ 2 * n + 1,
      ε ≤ |(q.eval k).susceptible / (n : ℝ) - 1|}
  have hbound : (pathMeasure (rates n) n (2 * n + 1)).real
      {q | ∃ k ≤ J, ε ≤ |(q.eval k).susceptible / (n : ℝ) -
        if q ∈ surv then fluidSusceptible l ((k : ℝ) / n) else 1|} ≤
      (pathMeasure (rates n) n (2 * n + 1)).real A +
        (pathMeasure (rates n) n (2 * n + 1)).real B +
        (pathMeasure (rates n) n (2 * n + 1)).real C := by
    calc
      _ ≤ (pathMeasure (rates n) n (2 * n + 1)).real ((A ∪ B) ∪ C) := by
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        apply PMF.toMeasure_mono _ (show MeasurableSet {q : FinitePath (2 * n + 1) |
          ∃ k ≤ J, ε ≤ |(q.eval k).susceptible / (n : ℝ) -
            if q ∈ surv then fluidSusceptible l ((k : ℝ) / n) else 1|} from trivial)
        intro q hq
        obtain ⟨k, hk, hbad⟩ := hq.1
        have hp := (mem_support_pathLaw_iff q).mp hq.2
        have hksteps : k ≤ 2 * n + 1 := hk.trans hJsteps
        by_cases hs : q ∈ surv
        · by_cases hkH : k ≤ H
          · exact Or.inl (Or.inl ⟨k, hkH, by
              simp only [ite_eq_left hs] at hbad ⊢
              linarith⟩)
          · have hHk : H ≤ k := by omega
            have htime : (k : ℝ) / n ≤ fluidExtinctionTime l := by
              have hh : (k : ℝ) / n ≤ (J : ℝ) / n :=
                div_le_div_of_nonneg_right (by exact_mod_cast hk) hnR.le
              exact hh.trans hJtime
            have hbad' : ε ≤ |(q.eval k).susceptible / (n : ℝ) -
                fluidSusceptible l ((k : ℝ) / n)| := by
              simpa only [ite_eq_left hs] using hbad
            rcases SupportedPath.susceptible_late_error_of_endpoint_errors hl hn hHk
                hksteps htime q hp hε hgapN hbad' with ha | hb
            · exact Or.inl (Or.inl ⟨H, le_rfl, by
                simpa only [ite_eq_left hs] using ha⟩)
            · exact Or.inl (Or.inr (show q ∈ B by
                change ε / 4 ≤ |(q.eval (2 * n + 1)).susceptible / (n : ℝ) -
                  if q ∈ surv then finalSusceptibleFraction l else 1|
                simpa only [ite_eq_left hs] using hb))
        · exact Or.inr ⟨hs, k, hksteps, by
            simpa only [ite_eq_right hs] using hbad⟩
      _ ≤ (pathMeasure (rates n) n (2 * n + 1)).real (A ∪ B) +
          (pathMeasure (rates n) n (2 * n + 1)).real C := measureReal_union_le _ _
      _ ≤ _ := by
        have hh := measureReal_union_le A B
          (μ := pathMeasure (rates n) n (2 * n + 1))
        linarith
  exact hbound

/-- The full susceptible functional mixture holds with every fixed admissible
cutoff parameter from the article. -/
theorem source_full_susceptible_functional_mixture_concentration_fixed_cutoff
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | ∃ k ≤ ⌊fluidExtinctionTime l * n⌋₊,
        ε ≤ |(q.eval k).susceptible / (n : ℝ) -
          if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
            fluidSusceptible l ((k : ℝ) / n) else 1|}) atTop (𝓝 0) := by
  obtain ⟨δ₀, hδ₀, hconv⟩ :=
    exists_source_full_susceptible_functional_mixture_concentration rates hl hrates hε
  have hdis₀ := sourceSurvivalEvent_disagreement_tendsto_zero rates hl hδ₀ hδ hrates
  have hdis : Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | (q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ₀ n) ≠
        (q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n)}) atTop (𝓝 0) := by
    apply hdis₀.congr'
    filter_upwards [] with n
    change (evolve (rates n) n (2 * n + 1)).toMeasure.real _ = _
    rw [← pathMeasure_event_at (rates n) n (2 * n + 1) (2 * n + 1) le_rfl]
    rfl
  have hsum := hconv.add hdis
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [] with n
  let μ := pathMeasure (rates n) n (2 * n + 1)
  let A : Set (FinitePath (2 * n + 1)) :=
    {q | ∃ k ≤ ⌊fluidExtinctionTime l * n⌋₊,
      ε ≤ |(q.eval k).susceptible / (n : ℝ) -
        if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ₀ n then
          fluidSusceptible l ((k : ℝ) / n) else 1|}
  let B : Set (FinitePath (2 * n + 1)) :=
    {q | (q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ₀ n) ≠
      (q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n)}
  calc
    μ.real {q | ∃ k ≤ ⌊fluidExtinctionTime l * n⌋₊,
      ε ≤ |(q.eval k).susceptible / (n : ℝ) -
        if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
          fluidSusceptible l ((k : ℝ) / n) else 1|} ≤ μ.real (A ∪ B) := by
        apply measureReal_mono (h₂ := measure_ne_top _ _)
        intro q hq
        by_cases heq : (q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ₀ n) =
            (q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n)
        · left
          obtain ⟨k, hk, hbad⟩ := hq
          refine ⟨k, hk, ?_⟩
          by_cases hs : q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ₀ n
          · have hs' : q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n :=
              heq.mp hs
            simp only [FinitePath.eval_last] at hs hs' hbad ⊢
            simpa [hs, hs'] using hbad
          · have hs' : q.eval (2 * n + 1) ∉ sourceSurvivalEvent l δ n := by
              intro hs'
              exact hs (heq.mpr hs')
            simp only [FinitePath.eval_last] at hs hs' hbad ⊢
            simpa [hs, hs'] using hbad
        · exact Or.inr heq
    _ ≤ μ.real A + μ.real B := measureReal_union_le A B

/-- The infectious functional mixture holds over every nonnegative event time.
Beyond the finite epidemic history both the path and the fluid curve vanish. -/
theorem source_full_infectious_all_event_times_mixture_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | ∃ k : ℕ,
        ε ≤ |(infectious (q.eval k) : ℝ) / n -
          if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
            fluidInfectious l ((k : ℝ) / n) else 0|}) atTop (𝓝 0) := by
  have hfinite := source_full_infectious_functional_mixture_concentration_fixed_cutoff
    rates hl hδ hrates hε
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hfinite
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {q : FinitePath (2 * n + 1) |
    ∃ k : ℕ, ε ≤ |(infectious (q.eval k) : ℝ) / n -
      if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
        fluidInfectious l ((k : ℝ) / n) else 0|} from trivial)
  intro q hq
  obtain ⟨k, hbad⟩ := hq.1
  have hp := (mem_support_pathLaw_iff q).mp hq.2
  by_cases hk : k ≤ 2 * n + 1
  · exact ⟨k, hk, hbad⟩
  · have hkn : 2 * n + 1 ≤ k := by omega
    have hterminal : infectious (q.eval (2 * n + 1)) = 0 := by
      exact Finset.card_eq_zero.mpr
        (evolve_absorbed le_rfl (hp.mem_evolve le_rfl))
    have htime : fluidExtinctionTime l ≤ (k : ℝ) / n := by
      have hτ := fluidExtinctionTime_lt_two hl
      have hcast : (2 * n + 1 : ℕ) < k := by omega
      have hcastR : 2 * (n : ℝ) + 1 < k := by exact_mod_cast hcast
      apply (le_div_iff₀ hnR).mpr
      nlinarith [mul_lt_mul_of_pos_right hτ hnR]
    have hfluid : fluidInfectious l ((k : ℝ) / n) = 0 :=
      fluidInfectious_eq_zero_after_extinction hl htime
    rw [q.eval_of_ge hkn, ← FinitePath.eval_last, hterminal] at hbad
    simp [hfluid] at hbad
    linarith

/-- The two functional process estimates hold jointly on the actual epidemic
path law, with the same terminal-tree survival indicator. -/
theorem source_joint_fluid_event_time_mixture_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | (∃ k : ℕ,
          ε ≤ |(infectious (q.eval k) : ℝ) / n -
            if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
              fluidInfectious l ((k : ℝ) / n) else 0|) ∨
        (∃ k ≤ ⌊fluidExtinctionTime l * n⌋₊,
          ε ≤ |(q.eval k).susceptible / (n : ℝ) -
            if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
              fluidSusceptible l ((k : ℝ) / n) else 1|)}) atTop (𝓝 0) := by
  have hI := source_full_infectious_all_event_times_mixture_concentration
    rates hl hδ hrates hε
  have hS := source_full_susceptible_functional_mixture_concentration_fixed_cutoff
    rates hl hδ hrates hε
  have hsum := hI.add hS
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  exact measureReal_union_le _ _

/-- A continuous real curve is uniformly approximated on a compact interval
by sampling it at the left endpoint of the population-size time mesh. -/
theorem continuous_uniform_floor_time_modulus (f : ℝ → ℝ) (hf : Continuous f)
    {C ε : ℝ} (_hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc (0 : ℝ) C,
      |f ((⌊t * n⌋₊ : ℝ) / n) - f t| < ε := by
  have huc : UniformContinuousOn f (Icc (0 : ℝ) C) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  filter_upwards [(tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0)).eventually
        (Iio_mem_nhds hη), eventually_gt_atTop 0] with n hn hn0 t ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let x : ℝ := (⌊t * n⌋₊ : ℝ) / n
  have hfloor : (⌊t * n⌋₊ : ℝ) ≤ t * n :=
    Nat.floor_le (mul_nonneg ht.1 (Nat.cast_nonneg n))
  have hfloor' : t * n < (⌊t * n⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hxt : x ≤ t := (div_le_iff₀ hnR).mpr hfloor
  have hxmem : x ∈ Icc (0 : ℝ) C := ⟨by positivity, hxt.trans ht.2⟩
  have hgapR : t * n - (⌊t * n⌋₊ : ℝ) < 1 := by linarith
  have hgap : t - x < (1 : ℝ) / n := by
    calc
      t - x = (t * n - (⌊t * n⌋₊ : ℝ)) / n := by
        dsimp [x]
        field_simp
      _ < 1 / n := (div_lt_div_iff_of_pos_right hnR).mpr hgapR
  have hdist : dist x t < η := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxt)]
    exact hgap.trans hn
  simpa only [Real.dist_eq] using hmod x hxmem t ht hdist

/-- Uniform infectious convergence on each compact real-time interval, with
the paper's floor-time interpolation and exact source survival event. -/
theorem source_full_infectious_compact_time_mixture_concentration
    (rates : ℕ → ℝ≥0) {l δ C : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | ∃ t ∈ Icc (0 : ℝ) C,
        ε ≤ |(infectious (q.eval ⌊t * n⌋₊) : ℝ) / n -
          if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
            fluidInfectious l t else 0|}) atTop (𝓝 0) := by
  have hε2 : 0 < ε / 2 := by positivity
  have hmod := continuous_uniform_floor_time_modulus (fluidInfectious l)
    (continuous_fluidInfectious hl) hC hε2
  have hdisc := source_full_infectious_all_event_times_mixture_concentration
    rates hl hδ hrates hε2
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hdisc
  filter_upwards [hmod] with n hmodN
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro q hq
  obtain ⟨t, ht, hbad⟩ := hq
  let k := ⌊t * n⌋₊
  have hnear : |fluidInfectious l ((k : ℝ) / n) - fluidInfectious l t| < ε / 2 :=
    hmodN t ht
  refine ⟨k, ?_⟩
  by_cases hs : q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n
  · simp only [ite_eq_left hs]
    simp only [ite_eq_left hs] at hbad
    have htri := abs_sub_le ((infectious (q.eval k) : ℝ) / n)
      (fluidInfectious l ((k : ℝ) / n)) (fluidInfectious l t)
    linarith
  · simp only [ite_eq_right hs]
    simp only [ite_eq_right hs] at hbad
    linarith

/-- Uniform susceptible convergence in real time through the macroscopic fluid
extinction time, using the paper's floor-time interpolation. -/
theorem source_full_susceptible_compact_time_mixture_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | ∃ t ∈ Icc (0 : ℝ) (fluidExtinctionTime l),
        ε ≤ |(q.eval ⌊t * n⌋₊).susceptible / (n : ℝ) -
          if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
            fluidSusceptible l t else 1|}) atTop (𝓝 0) := by
  have hε2 : 0 < ε / 2 := by positivity
  have hmod := continuous_uniform_floor_time_modulus (fluidSusceptible l)
    (continuous_fluidSusceptible hl) (fluidExtinctionTime_pos hl).le hε2
  have hdisc := source_full_susceptible_functional_mixture_concentration_fixed_cutoff
    rates hl hδ hrates hε2
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hdisc
  filter_upwards [hmod] with n hmodN
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro q hq
  obtain ⟨t, ht, hbad⟩ := hq
  let k := ⌊t * n⌋₊
  have hk : k ≤ ⌊fluidExtinctionTime l * n⌋₊ := by
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_right ht.2 (Nat.cast_nonneg n)
  have hnear : |fluidSusceptible l ((k : ℝ) / n) - fluidSusceptible l t| < ε / 2 :=
    hmodN t ht
  refine ⟨k, hk, ?_⟩
  by_cases hs : q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n
  · simp only [ite_eq_left hs]
    simp only [ite_eq_left hs] at hbad
    have htri := abs_sub_le ((q.eval k).susceptible / (n : ℝ))
      (fluidSusceptible l ((k : ℝ) / n)) (fluidSusceptible l t)
    linarith
  · simp only [ite_eq_right hs]
    simp only [ite_eq_right hs] at hbad
    linarith

/-- Both paper fluid coordinates converge jointly in the uniform-on-compacts
form, on the actual path law and for every fixed auxiliary cutoff. -/
theorem source_joint_fluid_compact_time_mixture_concentration
    (rates : ℕ → ℝ≥0) {l δ C : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | (∃ t ∈ Icc (0 : ℝ) C,
          ε ≤ |(infectious (q.eval ⌊t * n⌋₊) : ℝ) / n -
            if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
              fluidInfectious l t else 0|) ∨
        (∃ t ∈ Icc (0 : ℝ) (fluidExtinctionTime l),
          ε ≤ |(q.eval ⌊t * n⌋₊).susceptible / (n : ℝ) -
            if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
              fluidSusceptible l t else 1|)}) atTop (𝓝 0) := by
  have hI := source_full_infectious_compact_time_mixture_concentration
    rates hl hδ hC hrates hε
  have hS := source_full_susceptible_compact_time_mixture_concentration
    rates hl hδ hrates hε
  have hsum := hI.add hS
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  exact measureReal_union_le _ _

end HeightPaper.Model
