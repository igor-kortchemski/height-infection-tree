module

public import HeightPaper.Probability.ExtinctionLimit

/-!
# Uniform macroscopic infectious lower bounds

A finite grid of fixed-time fluid estimates and the deterministic one-event
bound on infectious-count losses control the entire intervening history.
Only activity at the final observation is imposed, so earlier grid states are
active automatically.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

namespace SupportedPath

theorem active_of_active_later {rate : ℝ≥0} {n steps : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n steps path) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps)
    (ha : (path j).active.Nonempty) : (path i).active.Nonempty := by
  by_contra hi
  have hz := Finset.not_nonempty_iff_eq_empty.mp hi
  have heq := hp.absorbed_stable hij hj hz
  rw [heq, hz] at ha
  exact Finset.not_nonempty_empty ha

/-- Fixed lower bounds at grid points and bounded grid gaps give a lower
bound at every intervening event time. -/
theorem infectious_lower_of_grid {rate : ℝ≥0} {n steps : ℕ} {path : ℕ → State}
    (hp : SupportedPath rate n steps path) (grid : ℕ → ℕ) (M : ℕ) {b d : ℝ}
    (hd : 0 ≤ d) (horder : ∀ j < M, grid j ≤ grid (j + 1))
    (hend : grid M ≤ steps)
    (hgap : ∀ j < M, (grid (j + 1) : ℝ) - grid j ≤ d)
    (hlower : ∀ j ≤ M, b ≤ infectious (path (grid j))) :
    ∀ k, grid 0 ≤ k → k ≤ grid M → b - d ≤ infectious (path k) := by
  induction M with
  | zero =>
    intro k hk hk'
    have heq : k = grid 0 := Nat.le_antisymm hk' hk
    rw [heq]
    have hh := hlower 0 le_rfl
    linarith
  | succ M ih =>
    intro k hk hk'
    by_cases hkm : k ≤ grid M
    · exact ih (fun j hj ↦ horder j (by omega)) ((horder M (by omega)).trans hend)
        (fun j hj ↦ hgap j (by omega)) (fun j hj ↦ hlower j (by omega)) k hk hkm
    · have hmk : grid M ≤ k := by omega
      have hI := hp.infectious_le_later_add_gap hmk (hk'.trans hend)
      have hIR : (infectious (path (grid M)) : ℝ) ≤ infectious (path k) + ((k - grid M : ℕ) : ℝ) := by
        exact_mod_cast hI
      rw [Nat.cast_sub hmk] at hIR
      have hkn : (k : ℝ) ≤ grid (M + 1) := by exact_mod_cast hk'
      have hG := hgap M (by omega)
      have hL := hlower M (by omega)
      linarith

end SupportedPath

private theorem finite_grid_mono (grid : ℕ → ℕ) {M : ℕ}
    (h : ∀ j < M, grid j ≤ grid (j + 1)) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ M) :
    grid i ≤ grid j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (h j (by omega))

/-- On survival to a fixed time before fluid extinction, the infectious
population is uniformly macroscopic on each positive compact time interval. -/
theorem path_uniform_active_count_lower
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l a T : ℝ} (hl : 1 < l)
    (ha : 0 < a) (haT : a < T) (hT : T < fluidExtinctionTime l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun n ↦ (pathMeasure (rates n) n (horizon n)).real
      {p | (p.eval (horizon n)).active.Nonempty ∧ ∃ k,
        ⌊a * n⌋₊ ≤ k ∧ k ≤ horizon n ∧ (infectious (p.eval k) : ℝ) < c * n})
      atTop (𝓝 0) := by
  let A := a / 2
  have hA : 0 < A := half_pos ha
  have hAT : A < T := (half_lt_self ha).trans haT
  obtain ⟨b, hb, hfluid⟩ := fluidInfectiousRaw_uniform_pos hl hA hT
  obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (8 * (T - A) / b))
  have hM1 : (1 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hM0 : 0 < M := by exact_mod_cast (zero_lt_one.trans hM1)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  let d := (T - A) / M
  have hd : 0 < d := div_pos (sub_pos.mpr hAT) hMR
  have hdsmall : d < b / 8 := by
    have hh := (le_max_right _ _).trans_lt hM
    have hh' := (div_lt_iff₀ hb).mp hh
    apply (div_lt_iff₀ hMR).mpr
    nlinarith
  let time : ℕ → ℝ := fun j ↦ A + j * d
  have htimeM : time M = T := by dsimp [time, d]; field_simp; ring
  have htimeA (j : ℕ) : A ≤ time j := by
    dsimp [time]
    have hh : 0 ≤ (j : ℝ) * d := mul_nonneg (Nat.cast_nonneg j) hd.le
    linarith
  have htimeT (j : ℕ) (hj : j ≤ M) : time j ≤ T := by
    rw [← htimeM]
    dsimp [time]
    have hjR : (j : ℝ) ≤ M := by exact_mod_cast hj
    have hh := mul_le_mul_of_nonneg_right hjR hd.le
    linarith
  have hstep (j : ℕ) : time (j + 1) - time j = d := by dsimp [time]; push_cast; ring
  let grid : ℕ → ℕ → ℕ := fun j n ↦ if j = M then horizon n else ⌊time j * n⌋₊
  have hgridM (n : ℕ) : grid M n = horizon n := by simp [grid]
  have hgridlim (j : ℕ) (hj : j ≤ M) :
      Tendsto (fun n ↦ (grid j n : ℝ) / n) atTop (𝓝 (time j)) := by
    by_cases heq : j = M
    · subst j
      simpa only [hgridM, htimeM] using hhorizon
    · simpa only [grid, heq, ↓reduceIte] using tendsto_floor_fraction (hA.le.trans (htimeA j))
  have hpairs : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range M,
      grid j n ≤ grid (j + 1) n ∧ (grid (j + 1) n : ℝ) - grid j n ≤ (b / 4) * n := by
    apply (eventually_all_finset _).mpr
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    have hdiff := (hgridlim (j + 1) (by omega)).sub (hgridlim j (by omega))
    rw [hstep] at hdiff
    have hstrict : time j < time (j + 1) := by have := hstep j; linarith
    filter_upwards [(hgridlim j (by omega)).eventually_lt (hgridlim (j + 1) (by omega)) hstrict,
      hdiff.eventually (Iio_mem_nhds (show d < b / 4 by linarith)), eventually_gt_atTop 0]
      with n hn hgap hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    refine ⟨?_, ?_⟩
    · exact_mod_cast ((div_lt_div_iff_of_pos_right hnR).mp hn).le
    · rw [← sub_div] at hgap
      exact ((div_lt_iff₀ hnR).mp hgap).le
  let bad : ℕ → ℕ → Set State := fun j n ↦
    {s | s.active.Nonempty ∧ b / 2 ≤ |(infectious s : ℝ) / n - fluidInfectiousRaw l (time j)|}
  have hbad (j : ℕ) (hj : j ∈ Finset.range (M + 1)) :
      Tendsto (fun n ↦ (evolve (rates n) n (grid j n)).toMeasure.real (bad j n)) atTop (𝓝 0) :=
    evolve_active_infectious_concentration rates (grid j) hl hrates
      (hgridlim j (by have hh := Finset.mem_range.mp hj; omega)) (half_pos hb)
  have hsum := tendsto_finsetSum (Finset.range (M + 1)) hbad
  simp only [Finset.sum_const_zero] at hsum
  refine ⟨b / 4, by positivity, ?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [hpairs, eventually_gt_atTop 0] with n hpairs hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hord (j : ℕ) (hj : j < M) : grid j n ≤ grid (j + 1) n := (hpairs j (Finset.mem_range.mpr hj)).1
  have hgap (j : ℕ) (hj : j < M) : (grid (j + 1) n : ℝ) - grid j n ≤ (b / 4) * n :=
    (hpairs j (Finset.mem_range.mpr hj)).2
  have hgridle (j : ℕ) (hj : j ≤ M) : grid j n ≤ horizon n := by
    rw [← hgridM n]
    exact finite_grid_mono (fun j ↦ grid j n) hord hj le_rfl
  let pathBad : ℕ → Set (FinitePath (horizon n)) := fun j ↦ {p | p.eval (grid j n) ∈ bad j n}
  calc
    (pathMeasure (rates n) n (horizon n)).real
        {p | (p.eval (horizon n)).active.Nonempty ∧ ∃ k,
          ⌊a * n⌋₊ ≤ k ∧ k ≤ horizon n ∧ (infectious (p.eval k) : ℝ) < b / 4 * n}
      ≤ (pathMeasure (rates n) n (horizon n)).real (⋃ j ∈ Finset.range (M + 1), pathBad j) := by
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        apply PMF.toMeasure_mono _ (show MeasurableSet {p : FinitePath (horizon n) |
          (p.eval (horizon n)).active.Nonempty ∧ ∃ k, ⌊a * n⌋₊ ≤ k ∧ k ≤ horizon n ∧
            (infectious (p.eval k) : ℝ) < b / 4 * n} from trivial)
        intro p hp
        have hpath := (mem_support_pathLaw_iff p).mp hp.2
        by_contra hnone
        have hlow (j : ℕ) (hj : j ≤ M) : (b / 2) * n ≤ infectious (p.eval (grid j n)) := by
          have hactive := hpath.active_of_active_later (hgridle j hj) le_rfl hp.1.1
          have hnot : ¬(p.eval (grid j n) ∈ bad j n) := by
            intro h
            exact hnone (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), h⟩⟩)
          have herr : |(infectious (p.eval (grid j n)) : ℝ) / n - fluidInfectiousRaw l (time j)| < b / 2 := by
            by_contra he
            exact hnot ⟨hactive, le_of_not_gt he⟩
          have hf := hfluid (time j) ⟨htimeA j, htimeT j hj⟩
          have herr' := (abs_lt.mp herr).1
          apply (le_div_iff₀ hnR).mp
          linarith
        obtain ⟨k, hk0, hkend, hkbad⟩ := hp.1.2
        have hgrid0 : grid 0 n ≤ ⌊a * n⌋₊ := by
          have hMne : (0 : ℕ) ≠ M := Nat.ne_of_lt hM0
          simp only [grid, hMne, ↓reduceIte, time, Nat.cast_zero, zero_mul, add_zero]
          apply Nat.floor_mono
          exact mul_le_mul_of_nonneg_right (half_lt_self ha).le (Nat.cast_nonneg n)
        have hi := hpath.infectious_lower_of_grid (fun j ↦ grid j n) M
          (show 0 ≤ (b / 4) * n by positivity) hord (by rw [hgridM]) hgap hlow
          k (hgrid0.trans hk0) (by rwa [hgridM])
        nlinarith
    _ ≤ ∑ j ∈ Finset.range (M + 1), (pathMeasure (rates n) n (horizon n)).real (pathBad j) :=
      measureReal_biUnion_finset_le _ _
    _ = ∑ j ∈ Finset.range (M + 1), (evolve (rates n) n (grid j n)).toMeasure.real (bad j n) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact pathMeasure_event_at (rates n) n (horizon n) (grid j n)
        (hgridle j (by have hh := Finset.mem_range.mp hj; omega)) (bad j n)

end HeightPaper.Model
