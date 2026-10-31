module

public import HeightPaper.Probability.FiniteBudgetCompactFluidLocation

/-!
# Functional fluid limit uniformly over a bounded rate interval

The inverse fluid clock makes the susceptible curve one-Lipschitz in event
time, uniformly in the rate. A single finite time grid therefore suffices
for every rate in the interval.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace HeightPaper.CountCoupling

theorem fluidSusceptible_lipschitz_time (a : ℝ) (ha : 1 < a) (t u : ℝ) :
    |fluidSusceptible a t - fluidSusceptible a u| ≤ |t - u| := by
  have h := abs_sub_le_abs_fluidClock_sub (zero_lt_one.trans ha)
    (fluidSusceptible_pos (t := t) ha) (fluidSusceptible_pos (t := u) ha)
  simpa only [fluidClock_fluidSusceptible ha] using h

theorem finiteSusceptible_compact_uniform_fluid_concentration
    (a₀ L : ℝ≥0) (ha₀ : 1 < (a₀ : ℝ)) (haL : a₀ ≤ L)
    {T δ η : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℝ≥0, a₀ ≤ a → a ≤ L →
      uniformLaw.real {u | ∃ k ≤ ⌊T * n⌋₊,
        δ ≤ |(finiteSusceptible (a : ℝ) n u k : ℝ) / n -
          fluidSusceptible (a : ℝ) ((k : ℝ) / n)|} < η := by
  let ε := δ / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨c, hc, hc1, hbar⟩ := Model.exists_ghostBudget_fluidBarrier
    (L : ℝ) T (zero_lt_one.trans (ha₀.trans_le (by exact_mod_cast haL))) hT.le
  obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (T / ε))
  have hM0 : 0 < M := by
    have hMR : (1 : ℝ) < M := (le_max_left _ _).trans_lt hM
    exact_mod_cast (zero_lt_one.trans hMR)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  have hstep : T / M < ε := by
    have hh : T / ε < (M : ℝ) := (le_max_right _ _).trans_lt hM
    have hh' := (div_lt_iff₀ hε).mp hh
    exact (div_lt_iff₀ hMR).mpr (by nlinarith)
  let time : ℕ → ℝ := fun j ↦ T * (j : ℝ) / M
  let grid : ℕ → ℕ → ℕ := fun j n ↦ ⌊time j * n⌋₊
  have htime0 : time 0 = 0 := by simp [time]
  have htimeM : time M = T := by simp [time, ne_of_gt hMR]
  have htime_nonneg (j : ℕ) : 0 ≤ time j := by dsimp [time]; positivity
  have htime_le (j : ℕ) (hj : j ≤ M) : time j ≤ T := by
    dsimp [time]
    have hjR : (j : ℝ) ≤ M := by exact_mod_cast hj
    apply (div_le_iff₀ hMR).mpr
    nlinarith
  have hgrid0 (n : ℕ) : grid 0 n = 0 := by simp [grid, htime0]
  have hgridM (n : ℕ) : grid M n = ⌊T * n⌋₊ := by simp [grid, htimeM]
  have hgridlim (j : ℕ) :
      Tendsto (fun n ↦ (grid j n : ℝ) / n) atTop (𝓝 (time j)) :=
    tendsto_floor_fraction (htime_nonneg j)
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
      ((grid (j + 1) n : ℝ) - grid j n) / n < ε := by
    suffices ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range M,
        ((grid (j + 1) n : ℝ) - grid j n) / n < ε by
      simpa only [Finset.mem_range] using this
    apply (eventually_all_finset _).mpr
    intro j hj
    have hlim := (hgridlim (j + 1)).sub (hgridlim j)
    rw [htime_succ] at hlim
    filter_upwards [hlim.eventually (Iio_mem_nhds hstep)] with n hn
    simpa only [← sub_div] using hn
  let ηgrid : ℝ := η / (2 * (M + 1))
  have hηgrid : 0 < ηgrid := by dsimp [ηgrid]; positivity
  let bad : ℝ≥0 → ℕ → ℕ → Set (ℕ → ℝ) := fun a j n ↦
    {u | ε ≤ |(finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n -
      fluidSusceptible (a : ℝ) ((grid j n : ℝ) / n)|}
  have hbad (j : ℕ) (hj : j ∈ Finset.range (M + 1)) :
      ∀ᶠ n : ℕ in atTop, ∀ a : ℝ≥0, a₀ ≤ a → a ≤ L →
        uniformLaw.real (bad a j n) < ηgrid := by
    have hjM : j ≤ M := by have hh := Finset.mem_range.mp hj; omega
    obtain ⟨Nj, hNj⟩ := finiteSusceptible_pointwise_fluid_uniform
      a₀ L (grid j) ha₀ haL hc hc1 (lt_of_le_of_lt (htime_le j hjM) hbar)
      (hgridlim j) (half_pos hε) hηgrid
    have hshift := (hgridlim j).eventually
      (Metric.ball_mem_nhds (time j) (half_pos hε))
    filter_upwards [eventually_ge_atTop Nj, hshift] with n hn hs
    intro a haa₀ haL'
    have ha : 1 < (a : ℝ) := ha₀.trans_le (by exact_mod_cast haa₀)
    have hS := hNj n hn a haa₀ haL'
    apply (measureReal_mono (h₂ := measure_ne_top _ _) ?_).trans_lt hS
    intro u hu
    have htime : |(grid j n : ℝ) / n - time j| < ε / 2 := by
      simpa only [Real.dist_eq] using hs
    have hfluid := fluidSusceptible_lipschitz_time (a : ℝ) ha
      ((grid j n : ℝ) / n) (time j)
    have htri := abs_add_le
      ((finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n -
        fluidSusceptible (a : ℝ) (time j))
      (fluidSusceptible (a : ℝ) (time j) -
        fluidSusceptible (a : ℝ) ((grid j n : ℝ) / n))
    have heq : (finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n -
        fluidSusceptible (a : ℝ) (time j) +
        (fluidSusceptible (a : ℝ) (time j) -
          fluidSusceptible (a : ℝ) ((grid j n : ℝ) / n)) =
        (finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n -
          fluidSusceptible (a : ℝ) ((grid j n : ℝ) / n) := by ring
    rw [heq] at htri
    have hfluid' : |fluidSusceptible (a : ℝ) (time j) -
        fluidSusceptible (a : ℝ) ((grid j n : ℝ) / n)| < ε / 2 := by
      rw [abs_sub_comm]
      exact hfluid.trans_lt htime
    have hu' : ε ≤ |(finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n -
      fluidSusceptible (a : ℝ) ((grid j n : ℝ) / n)| := hu
    change ε / 2 ≤ |(finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n -
      fluidSusceptible (a : ℝ) (time j)|
    linarith only [htri, hfluid', hu']
  have hall := (eventually_all_finset (Finset.range (M + 1))).mpr hbad
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hall.and (hgaps.and (eventually_gt_atTop 0)))
  refine ⟨N, ?_⟩
  intro n hn a haa₀ haL'
  obtain ⟨hpoints, hgap, hn0⟩ := hN n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have ha : 1 < (a : ℝ) := ha₀.trans_le (by exact_mod_cast haa₀)
  have hfgap (j : ℕ) (hj : j < M) :
      fluidSusceptible (a : ℝ) ((grid j n : ℝ) / n) -
        fluidSusceptible (a : ℝ) ((grid (j + 1) n : ℝ) / n) < ε := by
    have htime : |((grid j n : ℝ) / n) - ((grid (j + 1) n : ℝ) / n)| < ε := by
      rw [abs_of_nonpos (sub_nonpos.mpr
        (div_le_div_of_nonneg_right (by exact_mod_cast horder n j) hnR.le))]
      rw [← sub_div]
      have heq : -(((grid j n : ℝ) - grid (j + 1) n) / n) =
          ((grid (j + 1) n : ℝ) - grid j n) / n := by ring
      rw [heq]
      exact hgap j hj
    exact (le_abs_self _).trans_lt
      ((fluidSusceptible_lipschitz_time (a : ℝ) ha _ _).trans_lt htime)
  have hsubset : {u | ∃ k ≤ ⌊T * n⌋₊,
      δ ≤ |(finiteSusceptible (a : ℝ) n u k : ℝ) / n -
        fluidSusceptible (a : ℝ) ((k : ℝ) / n)|} ⊆
      ⋃ j ∈ Finset.range (M + 1), bad a j n := by
    intro u hu
    by_contra hnone
    have hpoint (j : ℕ) (hj : j ≤ M) :
        |(finiteSusceptible (a : ℝ) n u (grid j n) : ℝ) / n -
          fluidSusceptible (a : ℝ) ((grid j n : ℝ) / n)| < ε := by
      have hnot : ¬u ∈ bad a j n := by
        intro hh
        exact hnone (mem_iUnion.mpr ⟨j,
          mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), hh⟩⟩)
      exact lt_of_not_ge hnot
    obtain ⟨k, hk, hkbad⟩ := hu
    have hall' := finiteSusceptible_uniform_error_of_grid (a : ℝ) n ⌊T * n⌋₊
      u hn0 (fluidSusceptible (a : ℝ))
      (fluidSusceptible_strictAnti ha).antitone (by positivity : 0 ≤ ε)
      (fun j ↦ grid j n) M (hgrid0 n) (hgridM n)
      (fun j _ ↦ horder n j) hfgap hpoint k hk
    have hsmall : ε + ε < δ := by dsimp [ε]; linarith
    exact (not_le_of_gt (hall'.trans hsmall)) hkbad
  have hsum : ∑ j ∈ Finset.range (M + 1),
      uniformLaw.real (bad a j n) ≤ η / 2 := by
    have hh : ∑ j ∈ Finset.range (M + 1),
        uniformLaw.real (bad a j n) ≤ ∑ j ∈ Finset.range (M + 1), ηgrid := by
      apply Finset.sum_le_sum
      intro j hj
      exact (hpoints j hj a haa₀ haL').le
    have hconst : ∑ j ∈ Finset.range (M + 1), ηgrid = η / 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [ηgrid]
      have hMpos : (0 : ℝ) < M + 1 := by positivity
      field_simp
      push_cast
      ring
    rwa [hconst] at hh
  calc
    uniformLaw.real {u | ∃ k ≤ ⌊T * n⌋₊,
        δ ≤ |(finiteSusceptible (a : ℝ) n u k : ℝ) / n -
          fluidSusceptible (a : ℝ) ((k : ℝ) / n)|}
      ≤ uniformLaw.real (⋃ j ∈ Finset.range (M + 1), bad a j n) :=
        measureReal_mono (h₂ := measure_ne_top _ _) hsubset
    _ ≤ ∑ j ∈ Finset.range (M + 1), uniformLaw.real (bad a j n) :=
      measureReal_biUnion_finset_le _ _
    _ < η := by linarith only [hsum, hη]

theorem finiteWalk_bounded_uniform_fluid_concentration
    (a₀ L : ℝ≥0) (ha₀ : 1 < (a₀ : ℝ)) (haL : a₀ ≤ L)
    {T δ η : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℝ≥0, a₀ ≤ a → a ≤ L →
      uniformLaw.real {u | ∃ k ≤ ⌊T * n⌋₊,
        δ ≤ |(finiteWalk (a : ℝ) n u k : ℝ) / n -
          fluidInfectiousRaw (a : ℝ) ((k : ℝ) / n)|} < η := by
  obtain ⟨Ns, hNs⟩ := finiteSusceptible_compact_uniform_fluid_concentration
    a₀ L ha₀ haL hT (show 0 < δ / 4 by positivity) hη
  obtain ⟨Nsmall, hNsmall⟩ := eventually_atTop.mp
    (tendsto_one_div_atTop_nhds_zero_nat.eventually
      (Iio_mem_nhds (half_pos hδ)))
  refine ⟨max (max Ns Nsmall) 1, ?_⟩
  intro n hn a haa₀ haL'
  have hn0 : 0 < n := by omega
  have hsmall := hNsmall n (by omega : Nsmall ≤ n)
  have hs := hNs n (by omega : Ns ≤ n) a haa₀ haL'
  apply (measureReal_mono (h₂ := measure_ne_top _ _) ?_).trans_lt hs
  intro u hu
  obtain ⟨k, hk, hbad⟩ := hu
  refine ⟨k, hk, ?_⟩
  by_contra hnot
  have hs' : |(finiteSusceptible (a : ℝ) n u k : ℝ) / n -
      fluidSusceptible (a : ℝ) ((k : ℝ) / n)| < δ / 4 := lt_of_not_ge hnot
  have hw := finiteWalk_fluid_error_le (a : ℝ) n u k hn0
  linarith only [hw, hs', hbad, hsmall]

theorem finiteWalk_compact_parameter_grid_fluid
    {I : Set ℝ≥0} (hI : IsCompact I)
    (hparams : ∀ a ∈ I, 1 < (a : ℝ))
    {T δ η : ℝ} (_hT : 0 ≤ T) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a ∈ I,
      uniformLaw.real {u | ∃ k ≤ ⌊T * n⌋₊,
        δ ≤ |(finiteWalk (a : ℝ) n u k : ℝ) / n -
          fluidInfectiousRaw (a : ℝ) ((k : ℝ) / n)|} < η := by
  classical
  by_cases hne : I.Nonempty
  · obtain ⟨a₀, hleast⟩ := hI.exists_isLeast hne
    obtain ⟨L, hgreatest⟩ := hI.exists_isGreatest hne
    have ha₀ := hparams a₀ hleast.1
    have haL : a₀ ≤ L := hleast.2 hgreatest.1
    let T' := max 1 T
    have hT' : 0 < T' := by dsimp [T']; exact zero_lt_one.trans_le (le_max_left _ _)
    obtain ⟨N, hN⟩ := finiteWalk_bounded_uniform_fluid_concentration
      a₀ L ha₀ haL hT' hδ hη
    refine ⟨N, ?_⟩
    intro n hn a ha
    have hlow : a₀ ≤ a := hleast.2 ha
    have hupp : a ≤ L := hgreatest.2 ha
    apply (measureReal_mono (h₂ := measure_ne_top _ _) ?_).trans_lt
      (hN n hn a hlow hupp)
    intro u hu
    obtain ⟨k, hk, hbad⟩ := hu
    refine ⟨k, hk.trans ?_, hbad⟩
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_right (le_max_right 1 T) (Nat.cast_nonneg n)
  · exact ⟨0, fun _ _ a ha ↦ (hne ⟨a, ha⟩).elim⟩

theorem fluidInfectiousRaw_lipschitz_time (a : ℝ) (ha : 1 < a) (t u : ℝ) :
    |fluidInfectiousRaw a t - fluidInfectiousRaw a u| ≤ 3 * |t - u| := by
  have hg := fluidSusceptible_lipschitz_time a ha t u
  have heq : fluidInfectiousRaw a t - fluidInfectiousRaw a u =
      -(2 * (fluidSusceptible a t - fluidSusceptible a u)) - (t - u) := by
    unfold fluidInfectiousRaw
    ring
  rw [heq]
  have htri := abs_add_le
    (-(2 * (fluidSusceptible a t - fluidSusceptible a u))) (-(t - u))
  have hrewrite : -(2 * (fluidSusceptible a t - fluidSusceptible a u)) + -(t - u) =
      -(2 * (fluidSusceptible a t - fluidSusceptible a u)) - (t - u) := by ring
  rw [hrewrite] at htri
  simp only [abs_neg, abs_mul] at htri
  norm_num at htri
  linarith only [hg, htri]

theorem floor_time_distance_lt (n : ℕ) (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    |(⌊t * n⌋₊ : ℝ) / n - t| < 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor : (⌊t * n⌋₊ : ℝ) ≤ t * n := Nat.floor_le (mul_nonneg ht hnR.le)
  have hfloor' : t * n < (⌊t * n⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hnonpos : (⌊t * n⌋₊ : ℝ) / n - t ≤ 0 := by
    apply sub_nonpos.mpr
    exact (div_le_iff₀ hnR).mpr hfloor
  rw [abs_of_nonpos hnonpos]
  have heq : -((⌊t * n⌋₊ : ℝ) / n - t) =
      (t * n - ⌊t * n⌋₊) / n := by
    field_simp
    ring
  rw [heq]
  apply (div_lt_iff₀ hnR).mpr
  have hcancel : (1 / (n : ℝ)) * n = 1 := one_div_mul_cancel (ne_of_gt hnR)
  rw [hcancel]
  linarith only [hfloor']

theorem finiteWalk_compact_parameter_real_time_fluid
    {I : Set ℝ≥0} (hI : IsCompact I)
    (hparams : ∀ a ∈ I, 1 < (a : ℝ))
    {t₁ t₂ δ η : ℝ} (ht₁ : 0 ≤ t₁) (ht₁₂ : t₁ ≤ t₂)
    (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a ∈ I,
      uniformLaw.real {u | ∃ t ∈ Icc t₁ t₂,
        δ ≤ |(finiteWalk (a : ℝ) n u ⌊t * n⌋₊ : ℝ) / n -
          fluidInfectiousRaw (a : ℝ) t|} < η := by
  obtain ⟨Ngrid, hgrid⟩ := finiteWalk_compact_parameter_grid_fluid hI hparams
    (ht₁.trans ht₁₂) (half_pos hδ) hη
  obtain ⟨Ntime, hNtime⟩ := eventually_atTop.mp
    (tendsto_one_div_atTop_nhds_zero_nat.eventually
      (Iio_mem_nhds (show 0 < δ / 6 by positivity)))
  refine ⟨max (max Ngrid Ntime) 1, ?_⟩
  intro n hn a ha
  have hn0 : 0 < n := by omega
  have hsmall := hNtime n (by omega : Ntime ≤ n)
  have hgrid' := hgrid n (by omega : Ngrid ≤ n) a ha
  apply (measureReal_mono (h₂ := measure_ne_top _ _) ?_).trans_lt hgrid'
  intro u hu
  obtain ⟨t, ht, hbad⟩ := hu
  have ht0 : 0 ≤ t := ht₁.trans ht.1
  have hk : ⌊t * n⌋₊ ≤ ⌊t₂ * n⌋₊ := by
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_right ht.2 (Nat.cast_nonneg n)
  refine ⟨⌊t * n⌋₊, hk, ?_⟩
  have ha' := hparams a ha
  have htime := floor_time_distance_lt n hn0 ht0
  have hfluid := fluidInfectiousRaw_lipschitz_time (a : ℝ) ha'
    ((⌊t * n⌋₊ : ℝ) / n) t
  have htri := abs_add_le
    ((finiteWalk (a : ℝ) n u ⌊t * n⌋₊ : ℝ) / n -
      fluidInfectiousRaw (a : ℝ) ((⌊t * n⌋₊ : ℝ) / n))
    (fluidInfectiousRaw (a : ℝ) ((⌊t * n⌋₊ : ℝ) / n) -
      fluidInfectiousRaw (a : ℝ) t)
  have heq : (finiteWalk (a : ℝ) n u ⌊t * n⌋₊ : ℝ) / n -
      fluidInfectiousRaw (a : ℝ) ((⌊t * n⌋₊ : ℝ) / n) +
      (fluidInfectiousRaw (a : ℝ) ((⌊t * n⌋₊ : ℝ) / n) -
        fluidInfectiousRaw (a : ℝ) t) =
      (finiteWalk (a : ℝ) n u ⌊t * n⌋₊ : ℝ) / n -
        fluidInfectiousRaw (a : ℝ) t := by ring
  rw [heq] at htri
  change δ / 2 ≤ |(finiteWalk (a : ℝ) n u ⌊t * n⌋₊ : ℝ) / n -
    fluidInfectiousRaw (a : ℝ) ((⌊t * n⌋₊ : ℝ) / n)|
  linarith only [hbad, hfluid, htime, hsmall, htri]

end HeightPaper.CountCoupling
