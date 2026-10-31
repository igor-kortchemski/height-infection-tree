module

public import HeightPaper.Model.RandomOutgrowthLimits
public import HeightPaper.Analysis.PowerGeometricScale

/-!
# Random-cutoff outgrowth tails from probabilistic profile exponents

Logarithmic root-count concentration is converted to polynomial upper and
lower counts on good cutoff states. The quantitative finite bounds then give
the height tails, with pressure and barrier errors kept explicit.
-/

public section

open Filter MeasureTheory
open scoped Topology NNReal

namespace HeightPaper.Model

/-- Random-cutoff upper height bound from a weak profile exponent and a
strict logarithmic height gap. -/
theorem randomOutgrowth_upper_of_profile
    (μ : ℕ → PMF State) (hμ : ∀ n, (μ n).support.Finite) (rate : ℕ → ℝ≥0)
    (K H : ℕ → ℕ) (roots : ℕ → State → Finset ℕ) (A : ℕ → Set State)
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {f a : ℝ} (hf : 0 < f) (ha : 0 < a)
    (hprofile : ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (μ n).toMeasure.real {s | s ∈ A n ∧
      ε ≤ |Real.log (selectedRootCount s (roots n s)) / Real.log n - f|}) atTop (𝓝 0))
    (hH : Tendsto (fun n ↦ (H n : ℝ) / Real.log n) atTop (𝓝 a))
    (hK : ∀ᶠ n in atTop, ∀ s ∈ (μ n).support, s ∈ A n → potential s ≤ K n)
    (hpressure : Tendsto (fun n ↦ (μ n).toMeasure.real {s | s ∈ A n ∧
      1 - (infectionProbability (rate n) s.susceptible : ℝ) < (p : ℝ)}) atTop (𝓝 0))
    (hgap : f + a * Real.log (Branching.geometricMean p) < 0) :
    Tendsto (fun n ↦ (continuationSampleLaw (μ n) (rate n) (K n)).toMeasure.real
      {x | x.cutoff ∈ A n ∧ ¬belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos
        (roots n x.cutoff) (H n) x.final}) atTop (𝓝 0) := by
  let m := Branching.geometricMean p
  let η := min (f / 2) (-(f + a * Real.log m) / 2)
  have hm : 0 < m := Branching.geometricMean_pos (by linarith) hp1
  have hη : 0 < η := lt_min (half_pos hf) (half_pos (neg_pos.mpr hgap))
  have hηf : η < f := (min_le_left _ _).trans_lt (half_lt_self hf)
  have hgapη : f + η + a * Real.log m < 0 := by
    have he : η ≤ -(f + a * Real.log m) / 2 := min_le_right _ _
    linarith
  let G : ℕ → Set State := fun n ↦ {s |
    |Real.log (selectedRootCount s (roots n s)) / Real.log n - f| < η ∧
      (p : ℝ) ≤ 1 - (infectionProbability (rate n) s.susceptible : ℝ)}
  let M : ℕ → ℝ := fun n ↦ (n : ℝ) ^ (f + η)
  have hscale : Tendsto (fun n ↦ M n * m ^ H n) atTop (𝓝 0) :=
    tendsto_power_geometric_scale_zero H hm hH hgapη
  have hbad : Tendsto (fun n ↦ (μ n).toMeasure.real (A n \ G n)) atTop (𝓝 0) := by
    have ht := (hprofile η hη).add hpressure
    rw [add_zero] at ht
    apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ ht
    intro n
    apply le_trans ?_ (measureReal_union_le _ _)
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro s hs
    simp only [Set.mem_sdiff] at hs
    by_cases hprof : |Real.log (selectedRootCount s (roots n s)) / Real.log n - f| < η
    · apply Or.inr
      refine ⟨hs.1, lt_of_not_ge ?_⟩
      intro hpr
      exact hs.2 ⟨hprof, hpr⟩
    · exact Or.inl ⟨hs.1, le_of_not_gt hprof⟩
  apply tendsto_randomOutgrowth_upper_zero μ hμ rate K H roots A G hp hp1 M ?_ hscale hbad
  filter_upwards [eventually_ge_atTop 2, hK, hH.eventually (lt_mem_nhds ha)]
    with n hn hKn hHn
  have hHpos : 0 < H n := by
    by_contra hbad
    have hz : H n = 0 := Nat.eq_zero_of_not_pos hbad
    simp only [hz, Nat.cast_zero, zero_div, lt_self_iff_false] at hHn
  refine ⟨hHpos, Real.rpow_nonneg (Nat.cast_nonneg n) _, ?_⟩
  intro s hs hA hG
  exact ⟨hKn s hs hA, hG.2,
    (nat_count_rpow_bounds_of_log_error (by omega : 1 < n) hη hηf hG.1).2⟩

/-- Random-cutoff lower height bound from a weak profile exponent, the
terminal barrier error, and a strict logarithmic height gap. -/
theorem randomOutgrowth_lower_of_profile
    (μ : ℕ → PMF State) (hμ : ∀ n, (μ n).support.Finite) (rate : ℕ → ℝ≥0)
    (K H L : ℕ → ℕ) (roots : ℕ → State → Finset ℕ) (A : ℕ → Set State)
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {f a : ℝ} (hf : 0 < f) (ha : 0 < a)
    (hprofile : ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (μ n).toMeasure.real {s | s ∈ A n ∧
      ε ≤ |Real.log (selectedRootCount s (roots n s)) / Real.log n - f|}) atTop (𝓝 0))
    (hH : Tendsto (fun n ↦ (H n : ℝ) / Real.log n) atTop (𝓝 a))
    (hK : ∀ᶠ n in atTop, ∀ s ∈ (μ n).support, s ∈ A n → potential s ≤ K n)
    (hpressure : ∀ᶠ n in atTop, 1 - (infectionProbability (rate n) (L n) : ℝ) ≤ (p : ℝ))
    (hbarrier : Tendsto (fun n ↦ (continuationSampleLaw (μ n) (rate n) (K n)).toMeasure.real
      {x | x.cutoff ∈ A n ∧ x.final.susceptible < L n}) atTop (𝓝 0))
    (hgap : 0 < f + a * Real.log (Branching.geometricMean p)) :
    Tendsto (fun n ↦ (continuationSampleLaw (μ n) (rate n) (K n)).toMeasure.real
      {x | x.cutoff ∈ A n ∧ belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos
        (roots n x.cutoff) (H n) x.final}) atTop (𝓝 0) := by
  let m := Branching.geometricMean p
  let η := min (f / 2) ((f + a * Real.log m) / 2)
  have hm : 0 < m := Branching.geometricMean_pos (by linarith) hp1
  have hη : 0 < η := lt_min (half_pos hf) (half_pos hgap)
  have hηf : η < f := (min_le_left _ _).trans_lt (half_lt_self hf)
  have hgapη : 0 < f - η + a * Real.log m := by
    have he : η ≤ (f + a * Real.log m) / 2 := min_le_right _ _
    linarith
  let G : ℕ → Set State := fun n ↦
    {s | |Real.log (selectedRootCount s (roots n s)) / Real.log n - f| < η}
  let M : ℕ → ℝ := fun n ↦ (n : ℝ) ^ (f - η)
  have hscale : Tendsto (fun n ↦ M n * m ^ H n) atTop atTop :=
    tendsto_power_geometric_scale_atTop H hm hH hgapη
  have hbad : Tendsto (fun n ↦ (μ n).toMeasure.real (A n \ G n)) atTop (𝓝 0) := by
    convert hprofile η hη using 1
    funext n
    congr 1
    ext s
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, G, not_lt]
  apply tendsto_randomOutgrowth_lower_zero μ hμ rate K H L roots A G hp hp1 M
    ?_ hscale hbad hbarrier
  filter_upwards [eventually_ge_atTop 2, hK, hpressure, hH.eventually (lt_mem_nhds ha)]
    with n hn hKn hpn hHn
  have hHpos : 0 < H n := by
    by_contra hbad
    have hz : H n = 0 := Nat.eq_zero_of_not_pos hbad
    simp only [hz, Nat.cast_zero, zero_div, lt_self_iff_false] at hHn
  refine ⟨hHpos, hpn, ?_⟩
  intro s hs hA hG
  exact ⟨hKn s hs hA,
    (nat_count_rpow_bounds_of_log_error (by omega : 1 < n) hη hηf hG).1⟩

/-- Upper concentration at the normalized geometric height scale on a random
cutoff event, obtained from the profile exponent and pressure comparison. -/
theorem randomOutgrowth_normalized_upper_of_profile
    (μ : ℕ → PMF State) (hμ : ∀ n, (μ n).support.Finite) (rate : ℕ → ℝ≥0)
    (K : ℕ → ℕ) (roots : ℕ → State → Finset ℕ) (A : ℕ → Set State)
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {f : ℝ} (hf : 0 < f)
    (hprofile : ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (μ n).toMeasure.real {s | s ∈ A n ∧
      ε ≤ |Real.log (selectedRootCount s (roots n s)) / Real.log n - f|}) atTop (𝓝 0))
    (hK : ∀ᶠ n in atTop, ∀ s ∈ (μ n).support, s ∈ A n → potential s ≤ K n)
    (hpressure : Tendsto (fun n ↦ (μ n).toMeasure.real {s | s ∈ A n ∧
      1 - (infectionProbability (rate n) s.susceptible : ℝ) < (p : ℝ)}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (continuationSampleLaw (μ n) (rate n) (K n)).toMeasure.real
      {x | x.cutoff ∈ A n ∧ f / (-Real.log (Branching.geometricMean p)) + ε ≤
        (selectedFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos (roots n x.cutoff) x.final : ℝ) /
          Real.log n}) atTop (𝓝 0) := by
  let m := Branching.geometricMean p
  let c := f / (-Real.log m)
  let a := c + ε / 2
  let H : ℕ → ℕ := fun n ↦ ⌈a * Real.log n⌉₊
  have hm : 0 < m := Branching.geometricMean_pos (by linarith) hp1
  have hm1 : m < 1 := Branching.geometricMean_lt_one hp
  have hlog := Real.log_neg hm hm1
  have hc : 0 < c := div_pos hf (neg_pos.mpr hlog)
  have hcf : c * (-Real.log m) = f := div_mul_cancel₀ f (neg_ne_zero.mpr hlog.ne)
  have ha : 0 < a := by dsimp [a]; linarith
  have hca : c < a := by dsimp [a]; linarith
  have haε : a < c + ε := by dsimp [a]; linarith
  have hgap : f + a * Real.log m < 0 := by
    have hb := mul_lt_mul_of_pos_right hca (neg_pos.mpr hlog)
    nlinarith only [hb, hcf]
  have hH : Tendsto (fun n ↦ (H n : ℝ) / Real.log n) atTop (𝓝 a) :=
    tendsto_ceil_log_ratio ha.le
  have ht := randomOutgrowth_upper_of_profile μ hμ rate K H roots A hp hp1 hf ha
    hprofile hH hK hpressure hgap
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ ht
  filter_upwards [eventually_ge_atTop 2, hH.eventually (gt_mem_nhds haε)] with n hn hHn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hln : 0 < Real.log n := Real.log_pos hn'
  have hHpos : 0 < H n := Nat.ceil_pos.mpr (mul_pos ha hln)
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  refine ⟨hx.1, ?_⟩
  rw [belowFreshHeight_iff_selectedFreshHeight_lt _ _ _ hHpos]
  apply not_lt.mpr
  have hle : (H n : ℝ) ≤
      selectedFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos (roots n x.cutoff) x.final :=
    (div_le_div_iff_of_pos_right hln).mp (hHn.le.trans hx.2)
  exact_mod_cast hle

/-- Lower concentration at the normalized geometric height scale on a random
cutoff event, with the actual terminal susceptible-barrier error. -/
theorem randomOutgrowth_normalized_lower_of_profile
    (μ : ℕ → PMF State) (hμ : ∀ n, (μ n).support.Finite) (rate : ℕ → ℝ≥0)
    (K L : ℕ → ℕ) (roots : ℕ → State → Finset ℕ) (A : ℕ → Set State)
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {f : ℝ} (hf : 0 < f)
    (hprofile : ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (μ n).toMeasure.real {s | s ∈ A n ∧
      ε ≤ |Real.log (selectedRootCount s (roots n s)) / Real.log n - f|}) atTop (𝓝 0))
    (hK : ∀ᶠ n in atTop, ∀ s ∈ (μ n).support, s ∈ A n → potential s ≤ K n)
    (hpressure : ∀ᶠ n in atTop, 1 - (infectionProbability (rate n) (L n) : ℝ) ≤ (p : ℝ))
    (hbarrier : Tendsto (fun n ↦ (continuationSampleLaw (μ n) (rate n) (K n)).toMeasure.real
      {x | x.cutoff ∈ A n ∧ x.final.susceptible < L n}) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (continuationSampleLaw (μ n) (rate n) (K n)).toMeasure.real
      {x | x.cutoff ∈ A n ∧
        (selectedFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos (roots n x.cutoff) x.final : ℝ) /
          Real.log n ≤ f / (-Real.log (Branching.geometricMean p)) - ε}) atTop (𝓝 0) := by
  let m := Branching.geometricMean p
  let c := f / (-Real.log m)
  let a := max (c - ε / 2) (c / 2)
  let H : ℕ → ℕ := fun n ↦ ⌈a * Real.log n⌉₊
  have hm : 0 < m := Branching.geometricMean_pos (by linarith) hp1
  have hm1 : m < 1 := Branching.geometricMean_lt_one hp
  have hlog := Real.log_neg hm hm1
  have hc : 0 < c := div_pos hf (neg_pos.mpr hlog)
  have hcf : c * (-Real.log m) = f := div_mul_cancel₀ f (neg_ne_zero.mpr hlog.ne)
  have ha : 0 < a := (half_pos hc).trans_le (le_max_right _ _)
  have hac : a < c := max_lt (by linarith) (by linarith)
  have hεa : c - ε < a := (by linarith : c - ε < c - ε / 2).trans_le (le_max_left _ _)
  have hgap : 0 < f + a * Real.log m := by
    have hb := mul_lt_mul_of_pos_right hac (neg_pos.mpr hlog)
    nlinarith only [hb, hcf]
  have hH : Tendsto (fun n ↦ (H n : ℝ) / Real.log n) atTop (𝓝 a) :=
    tendsto_ceil_log_ratio ha.le
  have ht := randomOutgrowth_lower_of_profile μ hμ rate K H L roots A hp hp1 hf ha
    hprofile hH hK hpressure hbarrier hgap
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ ht
  filter_upwards [eventually_ge_atTop 2, hH.eventually (lt_mem_nhds hεa)] with n hn hHn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hln : 0 < Real.log n := Real.log_pos hn'
  have hHpos : 0 < H n := Nat.ceil_pos.mpr (mul_pos ha hln)
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  refine ⟨hx.1, ?_⟩
  rw [belowFreshHeight_iff_selectedFreshHeight_lt _ _ _ hHpos]
  have hlt : (selectedFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos
      (roots n x.cutoff) x.final : ℝ) < H n :=
    (div_lt_div_iff_of_pos_right hln).mp (hx.2.trans_lt hHn)
  exact_mod_cast hlt

end HeightPaper.Model
