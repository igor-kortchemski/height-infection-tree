module

public import HeightPaper.Probability.FiniteBudgetFluidLocation

/-!
# Functional fluid limit for the continued susceptible budget

Pointwise convergence is upgraded on compact event-time intervals using
monotonicity of both the budget chain and the fluid susceptible curve.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace HeightPaper.CountCoupling

private theorem budget_grid_mono (grid : ℕ → ℕ) {M : ℕ}
    (h : ∀ j < M, grid j ≤ grid (j + 1)) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ M) : grid i ≤ grid j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (h j (by omega))

theorem finiteSusceptible_uniform_error_of_grid
    (l : ℝ) (n H : ℕ) (u : ℕ → ℝ) (hn : 0 < n)
    (f : ℝ → ℝ) (hf : Antitone f) {ε d : ℝ} (hd : 0 ≤ d)
    (grid : ℕ → ℕ) (M : ℕ)
    (hzero : grid 0 = 0) (hend : grid M = H)
    (horder : ∀ j < M, grid j ≤ grid (j + 1))
    (hgap : ∀ j < M,
      f ((grid j : ℝ) / n) - f ((grid (j + 1) : ℝ) / n) < d)
    (hgrid : ∀ j ≤ M,
      |(finiteSusceptible l n u (grid j) : ℝ) / n -
        f ((grid j : ℝ) / n)| < ε) :
    ∀ k ≤ H,
      |(finiteSusceptible l n u k : ℝ) / n - f ((k : ℝ) / n)| < ε + d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgridle (j : ℕ) (hj : j ≤ M) : grid j ≤ H := by
    rw [← hend]
    exact budget_grid_mono grid horder hj le_rfl
  have hmain (m : ℕ) (hm : m ≤ M) :
      ∀ k, grid 0 ≤ k → k ≤ grid m →
        |(finiteSusceptible l n u k : ℝ) / n - f ((k : ℝ) / n)| < ε + d := by
    induction m with
    | zero =>
      intro k hk0 hk
      have heq : k = grid 0 := by omega
      subst k
      have hg := hgrid 0 (by omega)
      linarith
    | succ m ih =>
      intro k hk0 hk
      by_cases hkm : k ≤ grid m
      · exact ih (by omega) k hk0 hkm
      · have hmk : grid m ≤ k := by omega
        have hmkM : m < M := by omega
        have hkg : k ≤ grid (m + 1) := hk
        have hSupper : (finiteSusceptible l n u k : ℝ) / n ≤
            (finiteSusceptible l n u (grid m) : ℝ) / n := by
          apply div_le_div_of_nonneg_right _ hnR.le
          exact_mod_cast finiteSusceptible_antitone_nat l n u hmk
        have hSlower : (finiteSusceptible l n u (grid (m + 1)) : ℝ) / n ≤
            (finiteSusceptible l n u k : ℝ) / n := by
          apply div_le_div_of_nonneg_right _ hnR.le
          exact_mod_cast finiteSusceptible_antitone_nat l n u hkg
        have hfupper : f ((k : ℝ) / n) ≤ f ((grid m : ℝ) / n) :=
          hf (div_le_div_of_nonneg_right (by exact_mod_cast hmk) hnR.le)
        have hflower : f ((grid (m + 1) : ℝ) / n) ≤ f ((k : ℝ) / n) :=
          hf (div_le_div_of_nonneg_right (by exact_mod_cast hkg) hnR.le)
        have hg0 := abs_lt.mp (hgrid m (by omega))
        have hg1 := abs_lt.mp (hgrid (m + 1) hm)
        have hfg := hgap m hmkM
        apply abs_lt.mpr
        constructor <;> linarith
  intro k hk
  simpa only [hzero, hend, Nat.zero_le, true_imp_iff] using
    hmain M le_rfl k (by omega) (by rwa [hend])

theorem finiteSusceptible_uniform_fluid_concentration
    (a : ℝ≥0) {T : ℝ} (ha : 1 < (a : ℝ)) (hT : 0 < T)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ uniformLaw.real
      {u | ∃ k ≤ ⌊T * n⌋₊,
        δ ≤ |(finiteSusceptible (a : ℝ) n u k : ℝ) / n -
          fluidSusceptible (a : ℝ) ((k : ℝ) / n)|}) atTop (𝓝 0) := by
  let f := fluidSusceptible (a : ℝ)
  let ε := δ / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hcont : ContinuousOn f (Icc (0 : ℝ) T) :=
    (continuous_fluidSusceptible ha).continuousOn
  obtain ⟨r, hr, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hcont) ε hε
  let d := min r (δ / 4)
  have hd : 0 < d := lt_min hr (by positivity)
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
  let bad : ℕ → ℕ → Set (ℕ → ℝ) := fun j n ↦
    {u | ε ≤ |(finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n -
      f ((grid j n : ℝ) / n)|}
  have hbad (j : ℕ) (hj : j ∈ Finset.range (M + 1)) :
      Tendsto (fun n ↦ uniformLaw.real (bad j n)) atTop (𝓝 0) := by
    obtain ⟨c, hc, hc1, hbar⟩ := Model.exists_ghostBudget_fluidBarrier
      (a : ℝ) (time j) (zero_lt_one.trans ha) (htime_nonneg j)
    have hfixed := finiteSusceptible_pointwise_fluid_concentration a (grid j)
      ha hc hc1 hbar (hgridlim j) (half_pos hε)
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hfixed
    have hshift := (continuous_fluidSusceptible ha).tendsto (time j) |>.comp (hgridlim j)
    filter_upwards [hshift.eventually (Metric.ball_mem_nhds _ (half_pos hε))]
      with n hn
    simp only [Real.dist_eq] at hn
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro u hu
    have htri := abs_add_le
      ((finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n - f (time j))
      (f (time j) - f ((grid j n : ℝ) / n))
    have heq : (finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n - f (time j) +
        (f (time j) - f ((grid j n : ℝ) / n)) =
        (finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n -
          f ((grid j n : ℝ) / n) := by ring
    rw [heq] at htri
    change ε / 2 ≤ |(finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n -
      f (time j)|
    have hu' : ε ≤ |(finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n -
      f ((grid j n : ℝ) / n)| := hu
    have hn' : |f (time j) - f ((grid j n : ℝ) / n)| < ε / 2 := by
      simpa only [f, Function.comp_def, abs_sub_comm] using hn
    linarith only [htri, hu', hn']
  have hsum := tendsto_finsetSum (Finset.range (M + 1)) hbad
  simp only [Finset.sum_const_zero] at hsum
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [hgaps, eventually_gt_atTop 0] with n hgap hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsteps : (⌊T * n⌋₊ : ℝ) / n ≤ T := by
    have hh : (⌊T * n⌋₊ : ℝ) ≤ T * n := Nat.floor_le (by positivity)
    exact (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hh)
  have hgridle (j : ℕ) (hj : j ≤ M) : grid j n ≤ ⌊T * n⌋₊ := by
    rw [← hgridM n]
    exact budget_grid_mono (fun j ↦ grid j n) (fun j _ ↦ horder n j) hj le_rfl
  have hbase (j : ℕ) (hj : j ≤ M) : (grid j n : ℝ) / n ∈ Icc 0 T :=
    ⟨by positivity,
      (div_le_div_of_nonneg_right (by exact_mod_cast hgridle j hj) hnR.le).trans hsteps⟩
  have hfgap (j : ℕ) (hj : j < M) :
      f ((grid j n : ℝ) / n) - f ((grid (j + 1) n : ℝ) / n) < ε := by
    have htime : |((grid j n : ℝ) / n) - ((grid (j + 1) n : ℝ) / n)| < d := by
      rw [abs_of_nonpos (sub_nonpos.mpr
        (div_le_div_of_nonneg_right (by exact_mod_cast horder n j) hnR.le))]
      rw [← sub_div]
      have heq : -(((grid j n : ℝ) - grid (j + 1) n) / n) =
          ((grid (j + 1) n : ℝ) - grid j n) / n := by ring
      rw [heq]
      exact hgap j hj
    have hm := hmod _ (hbase j (by omega)) _
      (hbase (j + 1) (by omega)) (by
        simpa only [Real.dist_eq] using lt_of_lt_of_le htime (min_le_left r (δ / 4)))
    have hm' : |f ((grid j n : ℝ) / n) -
        f ((grid (j + 1) n : ℝ) / n)| < ε := by
      simpa only [Real.dist_eq] using hm
    exact (le_abs_self _).trans_lt hm'
  calc
    uniformLaw.real {u | ∃ k ≤ ⌊T * n⌋₊,
        δ ≤ |(finiteSusceptible (a : ℝ) n u k : ℝ) / n -
          f ((k : ℝ) / n)|}
      ≤ uniformLaw.real (⋃ j ∈ Finset.range (M + 1), bad j n) := by
        apply measureReal_mono (h₂ := measure_ne_top _ _)
        intro u hu
        by_contra hnone
        have hpoint (j : ℕ) (hj : j ≤ M) :
            |(finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n -
              f ((grid j n : ℝ) / n)| < ε := by
          have hnot : ¬u ∈ bad j n := by
            intro hh
            exact hnone (mem_iUnion.mpr ⟨j,
              mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), hh⟩⟩)
          exact lt_of_not_ge hnot
        obtain ⟨k, hk, hkbad⟩ := hu
        have hall := finiteSusceptible_uniform_error_of_grid (a : ℝ) n ⌊T * n⌋₊
          u hn0 f (fluidSusceptible_strictAnti ha).antitone (by positivity : 0 ≤ ε)
          (fun j ↦ grid j n) M (hgrid0 n) (hgridM n)
          (fun j _ ↦ horder n j) hfgap hpoint k hk
        have heq : ε + ε < δ := by dsimp [ε]; linarith
        exact (not_le_of_gt (hall.trans heq)) hkbad
    _ ≤ ∑ j ∈ Finset.range (M + 1), uniformLaw.real (bad j n) :=
      measureReal_biUnion_finset_le _ _

theorem finiteWalk_uniform_fluid_concentration
    (a : ℝ≥0) {T : ℝ} (ha : 1 < (a : ℝ)) (hT : 0 < T)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ uniformLaw.real
      {u | ∃ k ≤ ⌊T * n⌋₊,
        δ ≤ |(finiteWalk (a : ℝ) n u k : ℝ) / n -
          fluidInfectiousRaw (a : ℝ) ((k : ℝ) / n)|}) atTop (𝓝 0) := by
  have hs := finiteSusceptible_uniform_fluid_concentration a ha hT
    (show 0 < δ / 4 by positivity)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hs
  filter_upwards [eventually_gt_atTop 0,
    tendsto_one_div_atTop_nhds_zero_nat.eventually
      (Iio_mem_nhds (half_pos hδ))] with n hn hsmall
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro u hu
  obtain ⟨k, hk, hbad⟩ := hu
  refine ⟨k, hk, ?_⟩
  by_contra hnot
  have hs' : |(finiteSusceptible (a : ℝ) n u k : ℝ) / n -
      fluidSusceptible (a : ℝ) ((k : ℝ) / n)| < δ / 4 := lt_of_not_ge hnot
  have hw := finiteWalk_fluid_error_le (a : ℝ) n u k hn
  linarith only [hw, hs', hbad, hsmall]

end HeightPaper.CountCoupling
