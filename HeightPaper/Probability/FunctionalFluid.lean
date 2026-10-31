module

public import HeightPaper.Probability.UniformActiveCounts
public import HeightPaper.Probability.ActivePathPrefix
public import HeightPaper.Probability.LateCutoffActivity
public import HeightPaper.Probability.EarlyExtinctionTightness

/-!
# Uniform fluid control on a finite epidemic history

The pointwise fluid estimates are upgraded by a deterministic finite-grid
argument.  The active count changes by at most one at each genuine event.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal Classical

namespace HeightPaper.Model

namespace SupportedPath

/-- The infectious count is one-Lipschitz in event time on a supported path. -/
theorem infectious_abs_sub_le_gap {rate : ℝ≥0} {n steps : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n steps path) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps) :
    |(infectious (path j) : ℝ) - infectious (path i)| ≤ (j : ℝ) - i := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have hstep := infectious_increment_abs_le_one (hp.2 j (by omega : j < steps))
    have htri := abs_sub_le (infectious (path (j + 1)) : ℝ)
      (infectious (path j) : ℝ) (infectious (path i) : ℝ)
    have hprev := ih (by omega : j ≤ steps)
    push_cast
    linarith

private theorem grid_mono (grid : ℕ → ℕ) {M : ℕ}
    (h : ∀ j < M, grid j ≤ grid (j + 1)) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ M) : grid i ≤ grid j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (h j (by omega))

/-- A finite grid of small errors controls all intermediate event times. -/
theorem infectious_uniform_error_of_grid {rate : ℝ≥0} {n steps : ℕ}
    {path : ℕ → State} (hp : SupportedPath rate n steps path)
    (hn : 0 < n) (f : ℝ → ℝ) {T ε d : ℝ} (hε : 0 < ε) (hd : 0 ≤ d)
    (grid : ℕ → ℕ) (M : ℕ) (hzero : grid 0 = 0)
    (hend : grid M = steps)
    (horder : ∀ j < M, grid j ≤ grid (j + 1))
    (hgap : ∀ j < M, ((grid (j + 1) : ℝ) - grid j) / n < d)
    (hsteps : (steps : ℝ) / n ≤ T)
    (hmod : ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T,
      |x - y| < d → |f x - f y| < ε)
    (hgrid : ∀ j ≤ M,
      |(infectious (path (grid j)) : ℝ) / n - f ((grid j : ℝ) / n)| < ε) :
    ∀ k ≤ steps,
      |(infectious (path k) : ℝ) / n - f ((k : ℝ) / n)| < 3 * ε + d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgridle (j : ℕ) (hj : j ≤ M) : grid j ≤ steps := by
    rw [← hend]
    exact grid_mono grid horder hj le_rfl
  have hbase (j : ℕ) (hj : j ≤ M) : (grid j : ℝ) / n ∈ Icc 0 T :=
    ⟨by positivity, (div_le_div_of_nonneg_right (by exact_mod_cast hgridle j hj) hnR.le).trans hsteps⟩
  have hkbase (k : ℕ) (hk : k ≤ steps) : (k : ℝ) / n ∈ Icc 0 T :=
    ⟨by positivity, (div_le_div_of_nonneg_right (by exact_mod_cast hk) hnR.le).trans hsteps⟩
  have hmain (m : ℕ) (hm : m ≤ M) :
      ∀ k, grid 0 ≤ k → k ≤ grid m →
        |(infectious (path k) : ℝ) / n - f ((k : ℝ) / n)| < 3 * ε + d := by
    induction m with
    | zero =>
      intro k hk0 hk
      have heq : k = grid 0 := by omega
      subst k
      have hh := hgrid 0 (by omega)
      linarith
    | succ m ih =>
      intro k hk0 hk
      by_cases hkm : k ≤ grid m
      · exact ih (by omega) k hk0 hkm
      · have hmk : grid m ≤ k := by omega
        have hmkM : m < M := by omega
        have hlgap := infectious_abs_sub_le_gap hp hmk
          ((hk.trans (hgridle (m + 1) hm)))
        have hcount : |(infectious (path k) : ℝ) / n -
            (infectious (path (grid m)) : ℝ) / n| < d := by
          rw [← sub_div, abs_div, abs_of_pos hnR]
          have hgap' := hgap m hmkM
          have hgapbound : (k : ℝ) - grid m ≤
              (grid (m + 1) : ℝ) - grid m := by
            have hh : (k : ℝ) ≤ grid (m + 1) := by exact_mod_cast hk
            linarith
          exact (div_le_div_of_nonneg_right hlgap hnR.le).trans_lt
            ((div_le_div_of_nonneg_right hgapbound hnR.le).trans_lt hgap')
        have htime : |((grid m : ℝ) / n) - (k : ℝ) / n| < d := by
          rw [abs_of_nonpos (sub_nonpos.mpr
            (div_le_div_of_nonneg_right (by exact_mod_cast hmk) hnR.le))]
          rw [← sub_div]
          have hneg : -(((grid m : ℝ) - k) / n) =
              ((k : ℝ) - grid m) / n := by ring
          rw [hneg]
          have hgapbound : (k : ℝ) - grid m ≤
              (grid (m + 1) : ℝ) - grid m := by
            have hh : (k : ℝ) ≤ grid (m + 1) := by exact_mod_cast hk
            linarith
          exact (div_le_div_of_nonneg_right hgapbound hnR.le).trans_lt (hgap m hmkM)
        have hfunc := hmod _ (hbase m (by omega)) _
          (hkbase k (hk.trans (hgridle (m + 1) hm))) htime
        have hpoint := hgrid m (by omega)
        have htri := abs_add_le
          ((infectious (path k) : ℝ) / n - (infectious (path (grid m)) : ℝ) / n)
          ((infectious (path (grid m)) : ℝ) / n - f ((grid m : ℝ) / n))
        have htri2 := abs_add_le
          ((infectious (path k) : ℝ) / n - f ((grid m : ℝ) / n))
          (f ((grid m : ℝ) / n) - f ((k : ℝ) / n))
        have heq : (infectious (path k) : ℝ) / n -
            (infectious (path (grid m)) : ℝ) / n +
            ((infectious (path (grid m)) : ℝ) / n - f ((grid m : ℝ) / n)) =
            (infectious (path k) : ℝ) / n - f ((grid m : ℝ) / n) := by ring
        rw [heq] at htri
        have heq2 : (infectious (path k) : ℝ) / n - f ((grid m : ℝ) / n) +
            (f ((grid m : ℝ) / n) - f ((k : ℝ) / n)) =
            (infectious (path k) : ℝ) / n - f ((k : ℝ) / n) := by ring
        rw [heq2] at htri2
        linarith
  intro k hk
  simpa only [hzero, hend, Nat.zero_le, true_imp_iff] using hmain M le_rfl k (by omega) (by rwa [hend])

end SupportedPath

/-- Before deterministic fluid extinction, the full infectious-count history
converges uniformly in probability on the actual finite epidemic path space,
restricted to activity at the endpoint. -/
theorem path_uniform_active_infectious_concentration
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT0 : 0 < T) (_hT : T < fluidExtinctionTime l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n ⌊T * n⌋₊).real
      {p | p.last.active.Nonempty ∧ ∃ k ≤ ⌊T * n⌋₊,
        δ ≤ |(infectious (p.eval k) : ℝ) / n -
          fluidInfectiousRaw l ((k : ℝ) / n)|}) atTop (𝓝 0) := by
  let f := fluidInfectiousRaw l
  let ε := δ / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hcont : ContinuousOn f (Icc (0 : ℝ) T) :=
    (continuous_fluidInfectiousRaw hl).continuousOn
  obtain ⟨r, hr, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hcont) ε hε
  let d := min r (δ / 4)
  have hd : 0 < d := lt_min hr (by positivity)
  have hδbound : 3 * ε + d < δ := by
    have hh := min_le_right r (δ / 4)
    dsimp [d, ε]
    linarith
  have hmod' : ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T,
      |x - y| < d → |f x - f y| < ε := by
    intro x hx y hy hxy
    have hh := hmod x hx y hy (by
      simpa only [Real.dist_eq] using lt_of_lt_of_le hxy (min_le_left r (δ / 4)))
    simpa only [Real.dist_eq] using hh
  obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (T / d))
  have hM0 : 0 < M := by
    have hMR : (1 : ℝ) < M := (le_max_left _ _).trans_lt hM
    exact_mod_cast (zero_lt_one.trans hMR)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  have hstep : T / M < d := by
    have hh : T / d < (M : ℝ) := (le_max_right _ _).trans_lt hM
    have hh' := (div_lt_iff₀ hd).mp hh
    exact (div_lt_iff₀ hMR).mpr (by nlinarith)
  let time : ℕ → ℝ := fun j ↦ T * (j : ℝ) / M
  let grid : ℕ → ℕ → ℕ := fun j n ↦ ⌊time j * n⌋₊
  have htime0 : time 0 = 0 := by simp [time]
  have htimeM : time M = T := by simp [time, ne_of_gt hMR]
  have htime_nonneg (j : ℕ) : 0 ≤ time j := by dsimp [time]; positivity
  have hgrid0 (n : ℕ) : grid 0 n = 0 := by simp [grid, htime0]
  have hgridM (n : ℕ) : grid M n = ⌊T * n⌋₊ := by simp [grid, htimeM]
  have hgridlim (j : ℕ) :
      Tendsto (fun n ↦ (grid j n : ℝ) / n) atTop (𝓝 (time j)) := by
    exact tendsto_floor_fraction (htime_nonneg j)
  have htime_succ (j : ℕ) : time (j + 1) - time j = T / M := by
    dsimp [time]
    push_cast
    ring
  have horder (n j : ℕ) : grid j n ≤ grid (j + 1) n := by
    dsimp [grid]
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
    have hh := htime_succ j
    have hpos : 0 ≤ T / M := by positivity
    linarith
  have hgridle (n j : ℕ) (hj : j ≤ M) : grid j n ≤ ⌊T * n⌋₊ := by
    rw [← hgridM n]
    exact SupportedPath.grid_mono (fun j ↦ grid j n) (fun j _ ↦ horder n j) hj le_rfl
  have hgaps : ∀ᶠ n : ℕ in atTop, ∀ j < M,
      ((grid (j + 1) n : ℝ) - grid j n) / n < d := by
    suffices ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range M,
        ((grid (j + 1) n : ℝ) - grid j n) / n < d by
      simpa only [Finset.mem_range] using this
    apply (eventually_all_finset _).mpr
    intro j hj
    have hlim := (hgridlim (j + 1)).sub (hgridlim j)
    rw [htime_succ] at hlim
    filter_upwards [hlim.eventually (Iio_mem_nhds hstep)] with n hn
    simpa only [← sub_div] using hn
  let bad : ℕ → ℕ → Set State := fun j n ↦
    {s | s.active.Nonempty ∧ ε ≤ |(infectious s : ℝ) / n - f ((grid j n : ℝ) / n)|}
  have hbad (j : ℕ) (hj : j ∈ Finset.range (M + 1)) :
      Tendsto (fun n ↦ (evolve (rates n) n (grid j n)).toMeasure.real (bad j n))
        atTop (𝓝 0) := by
    have hfixed := evolve_active_infectious_concentration rates (grid j) hl hrates
      (hgridlim j) (half_pos hε)
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hfixed
    have hshift := (continuous_fluidInfectiousRaw hl).tendsto (time j) |>.comp (hgridlim j)
    filter_upwards [hshift.eventually (Metric.ball_mem_nhds _ (half_pos hε))] with n hn
    simp only [Real.dist_eq] at hn
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro s hs
    refine ⟨hs.1, ?_⟩
    have htri := abs_add_le
      ((infectious s : ℝ) / n - f (time j))
      (f (time j) - f ((grid j n : ℝ) / n))
    have heq : (infectious s : ℝ) / n - f (time j) +
        (f (time j) - f ((grid j n : ℝ) / n)) =
        (infectious s : ℝ) / n - f ((grid j n : ℝ) / n) := by ring
    rw [heq] at htri
    have hfirst : ε ≤ |(infectious s : ℝ) / n - f ((grid j n : ℝ) / n)| := hs.2
    have hshift' : |f (time j) - f ((grid j n : ℝ) / n)| < ε / 2 := by
      simpa only [f, Function.comp_apply, abs_sub_comm] using hn
    change ε / 2 ≤ |(infectious s : ℝ) / n - fluidInfectiousRaw l (time j)|
    linarith
  have hsum := tendsto_finsetSum (Finset.range (M + 1)) hbad
  simp only [Finset.sum_const_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [hgaps, eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsteps : (⌊T * n⌋₊ : ℝ) / n ≤ T := by
    have hh : (⌊T * n⌋₊ : ℝ) ≤ T * n := Nat.floor_le (by positivity)
    exact (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hh)
  let pathBad : ℕ → Set (FinitePath ⌊T * n⌋₊) :=
    fun j ↦ {p | p.eval (grid j n) ∈ bad j n}
  calc
    (pathMeasure (rates n) n ⌊T * n⌋₊).real
        {p | p.last.active.Nonempty ∧ ∃ k ≤ ⌊T * n⌋₊,
          δ ≤ |(infectious (p.eval k) : ℝ) / n - f ((k : ℝ) / n)|}
      ≤ (pathMeasure (rates n) n ⌊T * n⌋₊).real
          (⋃ j ∈ Finset.range (M + 1), pathBad j) := by
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        apply PMF.toMeasure_mono _ (show MeasurableSet {p : FinitePath ⌊T * n⌋₊ |
          p.last.active.Nonempty ∧ ∃ k ≤ ⌊T * n⌋₊,
            δ ≤ |(infectious (p.eval k) : ℝ) / n - f ((k : ℝ) / n)|} from trivial)
        intro p hp
        have hpath := (mem_support_pathLaw_iff p).mp hp.2
        by_contra hnone
        have hpoint (j : ℕ) (hj : j ≤ M) :
            |(infectious (p.eval (grid j n)) : ℝ) / n -
              f ((grid j n : ℝ) / n)| < ε := by
          have hendactive : (p.eval ⌊T * n⌋₊).active.Nonempty := by
            rw [FinitePath.eval_last]
            exact hp.1.1
          have hactive := hpath.active_of_active_later (hgridle n j hj) le_rfl
            hendactive
          have hnot : ¬p.eval (grid j n) ∈ bad j n := by
            intro h
            exact hnone (mem_iUnion.mpr ⟨j, mem_iUnion.mpr
              ⟨Finset.mem_range.mpr (by omega), h⟩⟩)
          by_contra herr
          exact hnot ⟨hactive, le_of_not_gt herr⟩
        obtain ⟨k, hk, hlarge⟩ := hp.1.2
        have hunif := hpath.infectious_uniform_error_of_grid hn0 f hε hd.le
          (fun j ↦ grid j n) M (hgrid0 n) (hgridM n)
          (fun j _ ↦ horder n j) (fun j hj ↦ hn j hj) hsteps hmod' hpoint k hk
        exact not_lt_of_ge (hδbound.le.trans hlarge) hunif
    _ ≤ ∑ j ∈ Finset.range (M + 1),
          (pathMeasure (rates n) n ⌊T * n⌋₊).real (pathBad j) :=
      measureReal_biUnion_finset_le _ _
    _ = ∑ j ∈ Finset.range (M + 1),
          (evolve (rates n) n (grid j n)).toMeasure.real (bad j n) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact pathMeasure_event_at (rates n) n ⌊T * n⌋₊ (grid j n)
        (hgridle n j (by have hh := Finset.mem_range.mp hj; omega)) (bad j n)

/-- The same pathwise estimate controls the susceptible fraction throughout
the active history, using the exact count balance. -/
theorem path_uniform_active_susceptible_concentration
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT0 : 0 < T) (hT : T < fluidExtinctionTime l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n ⌊T * n⌋₊).real
      {p | p.last.active.Nonempty ∧ ∃ k ≤ ⌊T * n⌋₊,
        ε ≤ |(p.eval k).susceptible / (n : ℝ) -
          fluidSusceptible l ((k : ℝ) / n)|}) atTop (𝓝 0) := by
  have hI := path_uniform_active_infectious_concentration rates hl hT0 hT hrates hε
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hI
  filter_upwards [(tendsto_one_div_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0)).eventually
      (Iio_mem_nhds hε), eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {p : FinitePath ⌊T * n⌋₊ |
    p.last.active.Nonempty ∧ ∃ k ≤ ⌊T * n⌋₊,
      ε ≤ |(p.eval k).susceptible / (n : ℝ) -
        fluidSusceptible l ((k : ℝ) / n)|} from trivial)
  intro p hp
  obtain ⟨hactive, k, hk, hbad⟩ := hp.1
  have hpath := (mem_support_pathLaw_iff p).mp hp.2
  have hendactive : (p.eval ⌊T * n⌋₊).active.Nonempty := by
    rw [FinitePath.eval_last]
    exact hactive
  have hka := hpath.active_of_active_later hk le_rfl hendactive
  have hpop := evolve_population (hpath.mem_evolve hk)
  have he := evolve_eventCount_eq_of_active (hpath.mem_evolve hk) hka
  have hb : (infectious (p.eval k) : ℝ) +
      2 * ((p.eval k).susceptible : ℝ) + k = 2 * n + 1 := by
    exact_mod_cast (he ▸ count_balance hpop)
  have heq : ((p.eval k).susceptible : ℝ) / n -
      fluidSusceptible l ((k : ℝ) / n) =
      -(((infectious (p.eval k) : ℝ) / n -
        fluidInfectiousRaw l ((k : ℝ) / n)) / 2) + 1 / (2 * n) := by
    unfold fluidInfectiousRaw
    field_simp
    nlinarith
  have htri := abs_add_le
    (-(((infectious (p.eval k) : ℝ) / n -
      fluidInfectiousRaw l ((k : ℝ) / n)) / 2)) (1 / (2 * n))
  rw [← heq, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * n))] at htri
  have hdiv : (1 : ℝ) / (2 * n) = (1 / n) / 2 := by ring
  rw [hdiv] at htri
  refine ⟨hactive, k, hk, ?_⟩
  linarith

/-- A vanishing bad-prefix probability under cutoff activity transfers to
the paper's exact terminal-tree survival event. -/
theorem sourceSurvival_cutoff_prefix_tendsto_zero_of_active
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (B : (n : ℕ) → Set (FinitePath (sourceCutoff l δ n)))
    (hbad : Tendsto (fun n ↦ (pathMeasure (rates n) n (sourceCutoff l δ n)).real
      {p | p.last.active.Nonempty ∧ p ∈ B n}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        q.prefixAt (sourceCutoff l δ n) ∈ B n}) atTop (𝓝 0) := by
  have hsum := hbad.add (sourceSurvival_cutoff_inactive_tendsto_zero rates hl hδ hrates)
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  let H := sourceCutoff l δ n
  have hmap : (pathMeasure (rates n) n (2 * n + 1)).real
      {q | (q.prefixAt H).last.active.Nonempty ∧ q.prefixAt H ∈ B n} =
      (pathMeasure (rates n) n H).real
        {p | p.last.active.Nonempty ∧ p ∈ B n} := by
    rw [← pathMeasure_map_prefixAt (rates n) n (2 * n + 1) H
      (sourceCutoff_le_steps hl hδ n)]
    simp only [measureReal_def]
    rw [Measure.map_apply (FinitePath.measurable _)
      (show MeasurableSet {p : FinitePath H | p.last.active.Nonempty ∧ p ∈ B n} from trivial)]
    rfl
  rw [← hmap]
  apply le_trans _ (measureReal_union_le _ _)
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro q hq
  by_cases ha : (q.eval H).active.Nonempty
  · exact Or.inl ⟨by simpa only [FinitePath.prefixAt_last] using ha, hq.2⟩
  · exact Or.inr ⟨hq.1, ha⟩

/-- Uniform infectious fluid convergence on the exact source survival event
up to its preterminal cutoff, on the original terminal history law. -/
theorem sourceSurvival_uniform_infectious_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        ∃ k ≤ sourceCutoff l δ n,
          ε ≤ |(infectious (q.eval k) : ℝ) / n -
            fluidInfectiousRaw l ((k : ℝ) / n)|}) atTop (𝓝 0) := by
  let T := (1 - δ) * fluidExtinctionTime l
  have hT0 : 0 < T := mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
  have hT : T < fluidExtinctionTime l := by
    dsimp [T]
    nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  let B : (n : ℕ) → Set (FinitePath (sourceCutoff l δ n)) := fun n ↦
    {p | ∃ k ≤ sourceCutoff l δ n,
      ε ≤ |(infectious (p.eval k) : ℝ) / n -
        fluidInfectiousRaw l ((k : ℝ) / n)|}
  have hbad : Tendsto (fun n ↦ (pathMeasure (rates n) n (sourceCutoff l δ n)).real
      {p | p.last.active.Nonempty ∧ p ∈ B n}) atTop (𝓝 0) := by
    have heq (n : ℕ) : {p : FinitePath (sourceCutoff l δ n) |
        p.last.active.Nonempty ∧ p ∈ B n} =
        {p | p.last.active.Nonempty ∧ ∃ k ≤ sourceCutoff l δ n,
          ε ≤ |(infectious (p.eval k) : ℝ) / n -
            fluidInfectiousRaw l ((k : ℝ) / n)|} := by rfl
    simp_rw [heq]
    change Tendsto (fun n ↦ (pathMeasure (rates n) n ⌊T * n⌋₊).real
      {p | p.last.active.Nonempty ∧ ∃ k ≤ ⌊T * n⌋₊,
        ε ≤ |(infectious (p.eval k) : ℝ) / n -
          fluidInfectiousRaw l ((k : ℝ) / n)|}) atTop (𝓝 0)
    exact path_uniform_active_infectious_concentration rates hl hT0 hT hrates hε
  have ht := sourceSurvival_cutoff_prefix_tendsto_zero_of_active rates hl hδ hrates B hbad
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  apply measureReal_congr
  apply Eventually.of_forall
  intro q
  simp only [Set.mem_ofPred_eq, B]
  apply propext
  constructor
  · rintro ⟨hs, k, hk, he⟩
    exact ⟨hs, k, hk, by rwa [q.prefixAt_eval hk] at he⟩
  · rintro ⟨hs, k, hk, he⟩
    exact ⟨hs, k, hk, by rwa [q.prefixAt_eval hk]⟩

/-- Uniform susceptible fluid convergence on the same exact source event. -/
theorem sourceSurvival_uniform_susceptible_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        ∃ k ≤ sourceCutoff l δ n,
          ε ≤ |(q.eval k).susceptible / (n : ℝ) -
            fluidSusceptible l ((k : ℝ) / n)|}) atTop (𝓝 0) := by
  let T := (1 - δ) * fluidExtinctionTime l
  have hT0 : 0 < T := mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
  have hT : T < fluidExtinctionTime l := by
    dsimp [T]
    nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  let B : (n : ℕ) → Set (FinitePath (sourceCutoff l δ n)) := fun n ↦
    {p | ∃ k ≤ sourceCutoff l δ n,
      ε ≤ |(p.eval k).susceptible / (n : ℝ) -
        fluidSusceptible l ((k : ℝ) / n)|}
  have hbad : Tendsto (fun n ↦ (pathMeasure (rates n) n (sourceCutoff l δ n)).real
      {p | p.last.active.Nonempty ∧ p ∈ B n}) atTop (𝓝 0) := by
    have heq (n : ℕ) : {p : FinitePath (sourceCutoff l δ n) |
        p.last.active.Nonempty ∧ p ∈ B n} =
        {p | p.last.active.Nonempty ∧ ∃ k ≤ sourceCutoff l δ n,
          ε ≤ |(p.eval k).susceptible / (n : ℝ) -
            fluidSusceptible l ((k : ℝ) / n)|} := by rfl
    simp_rw [heq]
    change Tendsto (fun n ↦ (pathMeasure (rates n) n ⌊T * n⌋₊).real
      {p | p.last.active.Nonempty ∧ ∃ k ≤ ⌊T * n⌋₊,
        ε ≤ |(p.eval k).susceptible / (n : ℝ) -
          fluidSusceptible l ((k : ℝ) / n)|}) atTop (𝓝 0)
    exact path_uniform_active_susceptible_concentration rates hl hT0 hT hrates hε
  have ht := sourceSurvival_cutoff_prefix_tendsto_zero_of_active rates hl hδ hrates B hbad
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  apply measureReal_congr
  apply Eventually.of_forall
  intro q
  simp only [Set.mem_ofPred_eq, B]
  apply propext
  constructor
  · rintro ⟨hs, k, hk, he⟩
    exact ⟨hs, k, hk, by rwa [q.prefixAt_eval hk] at he⟩
  · rintro ⟨hs, k, hk, he⟩
    exact ⟨hs, k, hk, by rwa [q.prefixAt_eval hk]⟩

/-- An outbreak extinct before a fixed pre-extinction fluid time has
uniformly negligible normalized infectious count throughout its history. -/
theorem path_extinct_uniform_infectious_concentration
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n ⌊T * n⌋₊).real
      {p | ¬p.last.active.Nonempty ∧ ∃ k ≤ ⌊T * n⌋₊,
        ε ≤ (infectious (p.eval k) : ℝ) / n}) atTop (𝓝 0) := by
  let K : ℕ → ℕ := fun n ↦ ⌊(ε / 2) * n⌋₊
  have hK : Tendsto K atTop atTop := by
    apply tendsto_nat_floor_atTop.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hε)
  have htail := evolve_extinct_eventCount_tail_tendsto_zero rates
    (fun n ↦ ⌊T * n⌋₊) K hl hT hrates (tendsto_floor_fraction hT.1.le) hK
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ htail
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← pathMeasure_event_at (rates n) n ⌊T * n⌋₊ ⌊T * n⌋₊ le_rfl]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {p : FinitePath ⌊T * n⌋₊ |
    ¬p.last.active.Nonempty ∧ ∃ k ≤ ⌊T * n⌋₊,
      ε ≤ (infectious (p.eval k) : ℝ) / n} from trivial)
  intro p hp
  obtain ⟨hz, k, hk, hbad⟩ := hp.1
  have hpath := (mem_support_pathLaw_iff p).mp hp.2
  have hzI : infectious p.last = 0 := by
    exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hz)
  have hkI : 0 < infectious (p.eval k) := by
    have hh : (0 : ℝ) < (infectious (p.eval k) : ℝ) := by
      have := (le_div_iff₀ hnR).mp hbad
      nlinarith
    exact_mod_cast hh
  have hlate := hpath.active_earlier_lt_eventCount hk le_rfl hkI
    (by simpa only [FinitePath.eval_last] using hzI)
  rw [FinitePath.eval_last] at hlate
  have hinit := hpath.1
  have hinc := hpath.infectious_abs_sub_le_gap (i := 0) (j := k)
    (Nat.zero_le _) hk
  rw [hinit, infectious_initial] at hinc
  norm_num at hinc
  have hIbound : (infectious (p.eval k) : ℝ) ≤ k + 1 := by
    have hh := le_abs_self ((infectious (p.eval k) : ℝ) - 1)
    linarith
  have hfloor : (K n : ℝ) ≤ ε / 2 * n := Nat.floor_le (by positivity)
  have hlarge : ε * n ≤ (infectious (p.eval k) : ℝ) :=
    (le_div_iff₀ hnR).mp hbad
  have hlateR : (k : ℝ) + 1 ≤ eventCount p.last := by
    have hh : k + 1 ≤ eventCount p.last := by omega
    exact_mod_cast hh
  simp only [Set.mem_ofPred_eq, FinitePath.eval_last]
  refine ⟨hzI, ?_⟩
  exact_mod_cast (show (K n : ℝ) < eventCount p.last by nlinarith)

/-- The infectious fluid trajectory and the survival indicator converge
jointly before fluid extinction, in a uniform-in-time probability form. -/
theorem path_uniform_infectious_mixture_concentration
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n ⌊T * n⌋₊).real
      {p | ∃ k ≤ ⌊T * n⌋₊,
        ε ≤ |(infectious (p.eval k) : ℝ) / n -
          if p.last.active.Nonempty then fluidInfectiousRaw l ((k : ℝ) / n) else 0|})
      atTop (𝓝 0) := by
  have hA := path_uniform_active_infectious_concentration rates hl hT.1 hT.2 hrates hε
  have hE := path_extinct_uniform_infectious_concentration rates hl hT hrates hε
  have hsum := hA.add hE
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  apply le_trans _ (measureReal_union_le _ _)
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro p hp
  obtain ⟨k, hk, hbad⟩ := hp
  by_cases ha : p.last.active.Nonempty
  · simp only [ite_eq_left ha] at hbad
    exact Or.inl ⟨ha, k, hk, hbad⟩
  · apply Or.inr
    refine ⟨ha, k, hk, ?_⟩
    simp only [ite_eq_right ha, sub_zero] at hbad
    have hnonneg : 0 ≤ (infectious (p.eval k) : ℝ) / n := by positivity
    rwa [abs_of_nonneg hnonneg] at hbad

theorem susceptible_loss_le_eventCount {n : ℕ} (s : State)
    (hpop : s.vertices + s.susceptible = n + 1) :
    n - s.susceptible ≤ eventCount s := by
  have hv := infectious_le_vertices s
  have hpos := s.tree.size_pos
  unfold eventCount
  omega

/-- Before fluid extinction, every early extinct history has susceptible
fraction uniformly close to one. -/
theorem path_extinct_uniform_susceptible_one_concentration
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n ⌊T * n⌋₊).real
      {p | ¬p.last.active.Nonempty ∧ ∃ k ≤ ⌊T * n⌋₊,
        ε ≤ |(p.eval k).susceptible / (n : ℝ) - 1|}) atTop (𝓝 0) := by
  let K : ℕ → ℕ := fun n ↦ ⌊(ε / 2) * n⌋₊
  have hK : Tendsto K atTop atTop := by
    apply tendsto_nat_floor_atTop.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hε)
  have htail := evolve_extinct_eventCount_tail_tendsto_zero rates
    (fun n ↦ ⌊T * n⌋₊) K hl hT hrates (tendsto_floor_fraction hT.1.le) hK
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ htail
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← pathMeasure_event_at (rates n) n ⌊T * n⌋₊ ⌊T * n⌋₊ le_rfl]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {p : FinitePath ⌊T * n⌋₊ |
    ¬p.last.active.Nonempty ∧ ∃ k ≤ ⌊T * n⌋₊,
      ε ≤ |(p.eval k).susceptible / (n : ℝ) - 1|} from trivial)
  intro p hp
  obtain ⟨hz, k, hk, hbad⟩ := hp.1
  have hpath := (mem_support_pathLaw_iff p).mp hp.2
  have hpop := evolve_population (hpath.mem_evolve hk)
  have hSle : (p.eval k).susceptible ≤ n := by
    have hh := (p.eval k).tree.size_pos
    change 0 < (p.eval k).vertices at hh
    omega
  have hfrac : (p.eval k).susceptible / (n : ℝ) ≤ 1 :=
    (div_le_one hnR).mpr (by exact_mod_cast hSle)
  rw [abs_of_nonpos (sub_nonpos.mpr hfrac)] at hbad
  have hneg : -((p.eval k).susceptible / (n : ℝ) - 1) =
      1 - (p.eval k).susceptible / (n : ℝ) := by ring
  rw [hneg] at hbad
  have hdiff : 1 - (p.eval k).susceptible / (n : ℝ) =
      ((n : ℝ) - (p.eval k).susceptible) / n := by field_simp
  rw [hdiff] at hbad
  have hlarge : ε * n ≤ (n : ℝ) - (p.eval k).susceptible :=
    (le_div_iff₀ hnR).mp hbad
  have hsize := susceptible_loss_le_eventCount (p.eval k) hpop
  have hmono := hpath.eventCount_mono hk le_rfl
  rw [FinitePath.eval_last] at hmono
  have hsizeR : (n : ℝ) - (p.eval k).susceptible ≤ eventCount p.last := by
    rw [← Nat.cast_sub hSle]
    exact_mod_cast hsize.trans hmono
  have hfloor : (K n : ℝ) ≤ ε / 2 * n := Nat.floor_le (by positivity)
  have hzI : infectious p.last = 0 :=
    Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hz)
  simp only [Set.mem_ofPred_eq, FinitePath.eval_last]
  refine ⟨hzI, ?_⟩
  exact_mod_cast (show (K n : ℝ) < eventCount p.last by nlinarith)

/-- The susceptible trajectory has the fluid curve on survival and the
constant-one curve after early extinction. -/
theorem path_uniform_susceptible_mixture_concentration
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n ⌊T * n⌋₊).real
      {p | ∃ k ≤ ⌊T * n⌋₊,
        ε ≤ |(p.eval k).susceptible / (n : ℝ) -
          if p.last.active.Nonempty then fluidSusceptible l ((k : ℝ) / n) else 1|})
      atTop (𝓝 0) := by
  have hA := path_uniform_active_susceptible_concentration rates hl hT.1 hT.2 hrates hε
  have hE := path_extinct_uniform_susceptible_one_concentration rates hl hT hrates hε
  have hsum := hA.add hE
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  apply le_trans _ (measureReal_union_le _ _)
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro p hp
  obtain ⟨k, hk, hbad⟩ := hp
  by_cases ha : p.last.active.Nonempty
  · simp only [ite_eq_left ha] at hbad
    exact Or.inl ⟨ha, k, hk, hbad⟩
  · simp only [ite_eq_right ha] at hbad
    exact Or.inr ⟨ha, k, hk, hbad⟩

/-- The preterminal infectious fluid mixture uses the paper's exact survival
indicator, measured on the complete epidemic history. -/
theorem sourceSurvival_uniform_infectious_mixture_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | ∃ k ≤ sourceCutoff l δ n,
        ε ≤ |(infectious (q.eval k) : ℝ) / n -
          if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
            fluidInfectiousRaw l ((k : ℝ) / n) else 0|}) atTop (𝓝 0) := by
  classical
  let T := (1 - δ) * fluidExtinctionTime l
  have hT0 : 0 < T := mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
  have hT : T < fluidExtinctionTime l := by
    dsimp [T]
    nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  let B : (n : ℕ) → Set (FinitePath (sourceCutoff l δ n)) := fun n ↦
    {p | ∃ k ≤ sourceCutoff l δ n,
      ε ≤ |(infectious (p.eval k) : ℝ) / n -
        if p.last.active.Nonempty then fluidInfectiousRaw l ((k : ℝ) / n) else 0|}
  have hB : Tendsto (fun n ↦
      (pathMeasure (rates n) n (sourceCutoff l δ n)).real (B n)) atTop (𝓝 0) := by
    change Tendsto (fun n ↦ (pathMeasure (rates n) n ⌊T * n⌋₊).real
      {p | ∃ k ≤ ⌊T * n⌋₊,
        ε ≤ |(infectious (p.eval k) : ℝ) / n -
          if p.last.active.Nonempty then fluidInfectiousRaw l ((k : ℝ) / n) else 0|})
      atTop (𝓝 0)
    exact path_uniform_infectious_mixture_concentration rates hl ⟨hT0, hT⟩ hrates hε
  have hdiff := sourceSurvival_cutoff_inactive_tendsto_zero rates hl hδ hrates
  have hsum := hB.add hdiff
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [sourceCutoff_pos_eventually hl hδ] with n hcut
  let H := sourceCutoff l δ n
  have hH : H ≤ 2 * n + 1 := sourceCutoff_le_steps hl hδ n
  have hmap : (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.prefixAt H ∈ B n} =
      (pathMeasure (rates n) n H).real (B n) := by
    rw [← pathMeasure_map_prefixAt (rates n) n (2 * n + 1) H hH]
    simp only [measureReal_def]
    rw [Measure.map_apply (FinitePath.measurable _) (show MeasurableSet (B n) from trivial)]
    rfl
  rw [← hmap]
  apply le_trans _ (measureReal_union_le _ _)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {q : FinitePath (2 * n + 1) |
    ∃ k ≤ H, ε ≤ |(infectious (q.eval k) : ℝ) / n -
      if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
        fluidInfectiousRaw l ((k : ℝ) / n) else 0|} from trivial)
  intro q hq
  obtain ⟨k, hk, hbad⟩ := hq.1
  have hpath := (mem_support_pathLaw_iff q).mp hq.2
  by_cases ha : (q.eval H).active.Nonempty
  · have hpre := hpath.active_of_active_later (Nat.sub_le H 1) hH ha
    have hs : q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n :=
      (sourceSurvivalEvent_iff_active hl hδ hpath hcut).mpr hpre
    apply Or.inl
    change ∃ k ≤ H, ε ≤ |(infectious ((q.prefixAt H).eval k) : ℝ) / n -
      if (q.prefixAt H).last.active.Nonempty then
        fluidInfectiousRaw l ((k : ℝ) / n) else 0|
    refine ⟨k, hk, ?_⟩
    rw [q.prefixAt_eval hk, FinitePath.prefixAt_last]
    simpa only [ite_eq_left ha, ite_eq_left hs] using hbad
  · by_cases hs : q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n
    · exact Or.inr ⟨hs, ha⟩
    · apply Or.inl
      change ∃ k ≤ H, ε ≤ |(infectious ((q.prefixAt H).eval k) : ℝ) / n -
        if (q.prefixAt H).last.active.Nonempty then
          fluidInfectiousRaw l ((k : ℝ) / n) else 0|
      refine ⟨k, hk, ?_⟩
      rw [q.prefixAt_eval hk, FinitePath.prefixAt_last]
      simpa only [ite_eq_right ha, ite_eq_right hs] using hbad

/-- The corresponding susceptible mixture uses the exact source survival
indicator and has the constant-one branch on early extinction. -/
theorem sourceSurvival_uniform_susceptible_mixture_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | ∃ k ≤ sourceCutoff l δ n,
        ε ≤ |(q.eval k).susceptible / (n : ℝ) -
          if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
            fluidSusceptible l ((k : ℝ) / n) else 1|}) atTop (𝓝 0) := by
  classical
  let T := (1 - δ) * fluidExtinctionTime l
  have hT0 : 0 < T := mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
  have hT : T < fluidExtinctionTime l := by
    dsimp [T]
    nlinarith [mul_pos hδ.1 (fluidExtinctionTime_pos hl)]
  let B : (n : ℕ) → Set (FinitePath (sourceCutoff l δ n)) := fun n ↦
    {p | ∃ k ≤ sourceCutoff l δ n,
      ε ≤ |(p.eval k).susceptible / (n : ℝ) -
        if p.last.active.Nonempty then fluidSusceptible l ((k : ℝ) / n) else 1|}
  have hB : Tendsto (fun n ↦
      (pathMeasure (rates n) n (sourceCutoff l δ n)).real (B n)) atTop (𝓝 0) := by
    change Tendsto (fun n ↦ (pathMeasure (rates n) n ⌊T * n⌋₊).real
      {p | ∃ k ≤ ⌊T * n⌋₊,
        ε ≤ |(p.eval k).susceptible / (n : ℝ) -
          if p.last.active.Nonempty then fluidSusceptible l ((k : ℝ) / n) else 1|})
      atTop (𝓝 0)
    exact path_uniform_susceptible_mixture_concentration rates hl ⟨hT0, hT⟩ hrates hε
  have hdiff := sourceSurvival_cutoff_inactive_tendsto_zero rates hl hδ hrates
  have hsum := hB.add hdiff
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [sourceCutoff_pos_eventually hl hδ] with n hcut
  let H := sourceCutoff l δ n
  have hH : H ≤ 2 * n + 1 := sourceCutoff_le_steps hl hδ n
  have hmap : (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.prefixAt H ∈ B n} =
      (pathMeasure (rates n) n H).real (B n) := by
    rw [← pathMeasure_map_prefixAt (rates n) n (2 * n + 1) H hH]
    simp only [measureReal_def]
    rw [Measure.map_apply (FinitePath.measurable _) (show MeasurableSet (B n) from trivial)]
    rfl
  rw [← hmap]
  apply le_trans _ (measureReal_union_le _ _)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet {q : FinitePath (2 * n + 1) |
    ∃ k ≤ H, ε ≤ |(q.eval k).susceptible / (n : ℝ) -
      if q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n then
        fluidSusceptible l ((k : ℝ) / n) else 1|} from trivial)
  intro q hq
  obtain ⟨k, hk, hbad⟩ := hq.1
  have hpath := (mem_support_pathLaw_iff q).mp hq.2
  by_cases ha : (q.eval H).active.Nonempty
  · have hpre := hpath.active_of_active_later (Nat.sub_le H 1) hH ha
    have hs : q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n :=
      (sourceSurvivalEvent_iff_active hl hδ hpath hcut).mpr hpre
    apply Or.inl
    change ∃ k ≤ H, ε ≤ |((q.prefixAt H).eval k).susceptible / (n : ℝ) -
      if (q.prefixAt H).last.active.Nonempty then
        fluidSusceptible l ((k : ℝ) / n) else 1|
    refine ⟨k, hk, ?_⟩
    rw [q.prefixAt_eval hk, FinitePath.prefixAt_last]
    simpa only [ite_eq_left ha, ite_eq_left hs] using hbad
  · by_cases hs : q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n
    · exact Or.inr ⟨hs, ha⟩
    · apply Or.inl
      change ∃ k ≤ H, ε ≤ |((q.prefixAt H).eval k).susceptible / (n : ℝ) -
        if (q.prefixAt H).last.active.Nonempty then
          fluidSusceptible l ((k : ℝ) / n) else 1|
      refine ⟨k, hk, ?_⟩
      rw [q.prefixAt_eval hk, FinitePath.prefixAt_last]
      simpa only [ite_eq_right ha, ite_eq_right hs] using hbad

end HeightPaper.Model
