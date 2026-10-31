module

public import HeightPaper.Probability.EpidemicLaplace
public import HeightPaper.Probability.SourceSurvivalTransfer
public import HeightPaper.Model.WeakProfile
public import HeightPaper.Probability.PrecutoffHeight
public import HeightPaper.Probability.LimitLaw

/-!
# The source weak-profile proposition at its exact survival cutoff

The finite-bin and infinite-tail estimates retain the manuscript's event
`τ' ≥ floor(nt)`, including extinction exactly at the cutoff. The discrepancy
from activity at the cutoff has vanishing probability. The profile input is
the inherited real-Laplace proof; these exports do not certify the paper's
stronger complex local-profile argument.
-/

public section

open MeasureTheory Filter Set
open scoped Topology NNReal Asymptotics

namespace HeightPaper.Model

/-- Any cutoff-state estimate on activity transfers to the exact source
survival event, on the original joint history space. -/
theorem sourceSurvival_cutoff_event_tendsto_zero_of_active
    (rates : ℕ → ℝ≥0) (B : ℕ → Set State) {l δ : ℝ}
    (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hbad : Tendsto (fun n ↦ (evolve (rates n) n (sourceCutoff l δ n)).toMeasure.real
      {s | s.active.Nonempty ∧ s ∈ B n}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        q.eval (sourceCutoff l δ n) ∈ B n}) atTop (𝓝 0) := by
  have hsum := hbad.add (sourceSurvival_cutoff_inactive_tendsto_zero rates hl hδ hrates)
  simp only [add_zero] at hsum
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hsum
  intro n
  rw [← pathMeasure_event_at (rates n) n (2 * n + 1) (sourceCutoff l δ n)
    (sourceCutoff_le_steps hl hδ n)]
  apply le_trans _ (measureReal_union_le _ _)
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro q hq
  by_cases ha : (q.eval (sourceCutoff l δ n)).active.Nonempty
  · exact Or.inl ⟨ha, hq.2⟩
  · exact Or.inr ⟨hq.1, ha⟩

/-- `prop: profil faible`, finite upper endpoint, at the source cutoff.
The upper endpoint may exceed the positive-profile edge. -/
theorem sourceCutoff_activeBinCount_log_concentration
    (rates : ℕ → ℝ≥0) {l δ x y : ℝ}
    (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (hxy : x < y)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        ε ≤ |Real.log (activeBinCount (q.eval (sourceCutoff l δ n))
          (growthFactor l * Real.exp x * Real.log n)
          (growthFactor l * Real.exp y * Real.log n)) / Real.log n -
            profileExponent l x|}) atTop (𝓝 0) := by
  intro ε hε
  refine sourceSurvival_cutoff_event_tendsto_zero_of_active rates
    (fun n ↦ {s | ε ≤ |Real.log (activeBinCount s
      (growthFactor l * Real.exp x * Real.log n)
      (growthFactor l * Real.exp y * Real.log n)) / Real.log n -
        profileExponent l x|}) hl hδ hrates ?_
  exact activeBinCount_log_convergence_of_laplace rates (sourceCutoff l δ) hl hx hxy
    (fun z hz ↦ sourceCutoff_activeWeight_log_concentration rates (x := z) hl hδ hz hrates) ε hε

/-- The infinite-upper-endpoint case of the same proposition. -/
theorem sourceCutoff_activeTailCount_log_concentration
    (rates : ℕ → ℝ≥0) {l δ x : ℝ}
    (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        ε ≤ |Real.log (activeTailCount (q.eval (sourceCutoff l δ n))
          (growthFactor l * Real.exp x * Real.log n)) / Real.log n -
            profileExponent l x|}) atTop (𝓝 0) := by
  intro ε hε
  refine sourceSurvival_cutoff_event_tendsto_zero_of_active rates
    (fun n ↦ {s | ε ≤ |Real.log (activeTailCount s
      (growthFactor l * Real.exp x * Real.log n)) / Real.log n -
        profileExponent l x|}) hl hδ hrates ?_
  exact activeTailCount_log_convergence_of_laplace rates (sourceCutoff l δ) hl hx
    (fun z hz ↦ sourceCutoff_activeWeight_log_concentration rates (x := z) hl hδ hz hrates) ε hε

/-- Empty bins on source survival have vanishing probability. This makes the
totalized real logarithm harmless for the paper's strictly positive exponent. -/
theorem sourceCutoff_activeBinCount_zero_tendsto
    (rates : ℕ → ℝ≥0) {l δ x y : ℝ}
    (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (hxy : x < y)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        activeBinCount (q.eval (sourceCutoff l δ n))
          (growthFactor l * Real.exp x * Real.log n)
          (growthFactor l * Real.exp y * Real.log n) = 0}) atTop (𝓝 0) := by
  have hf := profileExponent_pos hl hx.1.le hx.2
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _
    (sourceCutoff_activeBinCount_log_concentration rates hl hδ hx hxy hrates _ hf)
  intro n
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro q hq
  refine ⟨hq.1, ?_⟩
  simp only [hq.2, Nat.cast_zero, Real.log_zero, zero_div, zero_sub, abs_neg,
    abs_of_pos hf, le_refl]

/-- The exact finite-endpoint source proposition for arbitrary pre-extinction
time and the printed rate-asymptotic hypothesis. Terminal size represents the
first extinction time by the already proved supported-path identity. -/
theorem source_weakProfile_bin
    (rates : ℕ → ℝ≥0) {l T x y : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (hxy : x < y)
    (hrates : (fun n ↦ (rates n : ℝ)) ~[atTop] (fun n : ℕ ↦ l / n)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | ⌊T * n⌋₊ ≤ 2 * (q.eval (2 * n + 1)).vertices - 1 ∧
        ε ≤ |Real.log (activeBinCount (q.eval ⌊T * n⌋₊)
          (growthFactor l * Real.exp x * Real.log n)
          (growthFactor l * Real.exp y * Real.log n)) / Real.log n -
            profileExponent l x|}) atTop (𝓝 0) := by
  let δ := 1 - T / fluidExtinctionTime l
  have ht := fluidExtinctionTime_pos hl
  have hδ : δ ∈ Ioo (0 : ℝ) 1 := by
    dsimp [δ]
    constructor
    · have := (div_lt_one ht).mpr hT.2
      linarith
    · have := div_pos hT.1 ht
      linarith
  have he : (1 - δ) * fluidExtinctionTime l = T := by
    dsimp [δ]
    field_simp [ht.ne']
    ring
  have hr := (rate_asymptotic_iff_scaled_tendsto (ne_of_gt (by linarith : 0 < l))).mp hrates
  have hr' : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l) := by
    simpa only [mul_comm] using hr
  simpa only [sourceSurvivalEvent, sourceCutoff, he, Set.mem_ofPred_eq] using
    sourceCutoff_activeBinCount_log_concentration rates hl hδ hx hxy hr'

/-- The exact source proposition when the upper endpoint is infinity. -/
theorem source_weakProfile_tail
    (rates : ℕ → ℝ≥0) {l T x : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l))
    (hrates : (fun n ↦ (rates n : ℝ)) ~[atTop] (fun n : ℕ ↦ l / n)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | ⌊T * n⌋₊ ≤ 2 * (q.eval (2 * n + 1)).vertices - 1 ∧
        ε ≤ |Real.log (activeTailCount (q.eval ⌊T * n⌋₊)
          (growthFactor l * Real.exp x * Real.log n)) / Real.log n -
            profileExponent l x|}) atTop (𝓝 0) := by
  let δ := 1 - T / fluidExtinctionTime l
  have ht := fluidExtinctionTime_pos hl
  have hδ : δ ∈ Ioo (0 : ℝ) 1 := by
    dsimp [δ]
    constructor
    · have := (div_lt_one ht).mpr hT.2
      linarith
    · have := div_pos hT.1 ht
      linarith
  have he : (1 - δ) * fluidExtinctionTime l = T := by
    dsimp [δ]
    field_simp [ht.ne']
    ring
  have hr := (rate_asymptotic_iff_scaled_tendsto (ne_of_gt (by linarith : 0 < l))).mp hrates
  have hr' : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l) := by
    simpa only [mul_comm] using hr
  simpa only [sourceSurvivalEvent, sourceCutoff, he, Set.mem_ofPred_eq] using
    sourceCutoff_activeTailCount_log_concentration rates hl hδ hx hr'


/-- Every coefficient strictly below the profile edge is exceeded by an
interior tilt. This avoids using the weak profile at its excluded endpoint. -/
theorem exists_interior_profile_height {l b : ℝ} (hl : 1 < l)
    (hb : b < growthFactor l * Real.exp (profileRoot l)) :
    ∃ x ∈ Ioo (0 : ℝ) (profileRoot l), b < growthFactor l * Real.exp x := by
  have hc : Continuous (fun x : ℝ ↦ growthFactor l * Real.exp x) :=
    continuous_const.mul Real.continuous_exp
  have he := hc.continuousAt.eventually (lt_mem_nhds hb)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  let d := min (r / 2) (profileRoot l / 2)
  have hd : 0 < d := lt_min (by linarith) (by linarith [profileRoot_pos hl])
  have hdr : d < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdz : d < profileRoot l := lt_of_le_of_lt (min_le_right _ _)
    (by linarith [profileRoot_pos hl])
  refine ⟨profileRoot l - d, ⟨by linarith, by linarith⟩, hball ?_⟩
  rw [Real.dist_eq]
  have habs : |profileRoot l - d - profileRoot l| = d := by
    rw [show profileRoot l - d - profileRoot l = -d by ring, abs_neg, abs_of_pos hd]
  rwa [habs]

/-- If the entire tree is shorter than the lower endpoint, its active bin is empty. -/
theorem activeBinCount_eq_zero_of_height_lt (s : State) {a b : ℝ}
    (ha : (height s : ℝ) < a) : activeBinCount s a b = 0 := by
  classical
  unfold activeBinCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have hlo := (Finset.mem_filter.mp hv).2.1
  have hhi : (s.tree.depth v : ℝ) ≤ height s := by
    exact_mod_cast Tree.depth_le_height s.tree v
  linarith

/-- The lower preterminal-height estimate uses only interior profile bins,
as in the paper's passage from weak profile to height. -/
theorem sourceCutoff_height_lower
    (rates : ℕ → ℝ≥0) {l δ b : ℝ}
    (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hb : b < growthFactor l * Real.exp (profileRoot l)) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        (height (q.eval (sourceCutoff l δ n)) : ℝ) / Real.log n ≤ b})
      atTop (𝓝 0) := by
  obtain ⟨x, hx, hbx⟩ := exists_interior_profile_height hl hb
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _
    (sourceCutoff_activeBinCount_zero_tendsto rates hl hδ hx
      (show x < x + 1 by linarith) hrates)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro q hq
  refine ⟨hq.1, activeBinCount_eq_zero_of_height_lt _ ?_⟩
  exact (div_lt_iff₀ hlog).mp (hq.2.trans_lt hbx)

/-- The preterminal tree height has the source coefficient on the exact
survival event. This is the surviving-height component of `eq:limHbefore`;
it does not assert that formula's joint unscaled early-extinction limit. -/
theorem sourceCutoff_height_log_concentration
    (rates : ℕ → ℝ≥0) {l δ : ℝ}
    (hl : 1 < l) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (pathMeasure (rates n) n (2 * n + 1)).real
      {q | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
        ε ≤ |(height (q.eval (sourceCutoff l δ n)) : ℝ) / Real.log n -
          growthFactor l * Real.exp (profileRoot l)|}) atTop (𝓝 0) := by
  intro ε hε
  let c := growthFactor l * Real.exp (profileRoot l)
  have htime : (1 - δ) * fluidExtinctionTime l ∈ Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) (fluidExtinctionTime_pos hl)
    · nlinarith [fluidExtinctionTime_pos hl, hδ.1]
  have hu := sourceSurvival_cutoff_event_tendsto_zero_of_active rates
    (fun n ↦ {s | c + ε ≤ (height s : ℝ) / Real.log n}) hl hδ hrates
    (evolve_height_div_log_upper rates (sourceCutoff l δ) hl htime hrates
      (tendsto_floor_fraction htime.1.le) ε hε)
  have hd := sourceCutoff_height_lower rates hl hδ hrates
    (show c - ε < growthFactor l * Real.exp (profileRoot l) by dsimp [c]; linarith)
  have hs := hd.add hu
  simp only [add_zero] at hs
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hs
  intro n
  apply le_trans _ (measureReal_union_le _ _)
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro q hq
  rcases le_abs.mp hq.2 with h | h
  · exact Or.inr ⟨hq.1, by dsimp [c]; linarith⟩
  · exact Or.inl ⟨hq.1, by dsimp [c]; linarith⟩

end HeightPaper.Model
