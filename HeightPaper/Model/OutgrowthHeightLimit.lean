module

public import HeightPaper.Model.HeightPotentialGeometry
public import HeightPaper.Model.HeightPotentialLimits
public import HeightPaper.Analysis.GeometricScale

/-!
# Logarithmic concentration of actual selected outgrowth maxima

The root-count exponent and infection-pressure limits are explicit inputs.
The geometric tail limits are derived here from the actual finite SIR bounds.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology NNReal

namespace HeightPaper.Model

/-- Number of selected infectious roots at the fresh-outgrowth cutoff. -/
def selectedRootCount (s : State) (roots : Finset ℕ) : ℕ :=
  (s.active.filter (fun v ↦ v.val ∈ roots)).card

/-- Maximum fresh height among the components selected by root label. -/
def selectedFreshHeight (cutoff : ℕ) (hcutoff : 0 < cutoff) (roots : Finset ℕ)
    (s : State) : ℕ :=
  (Finset.univ.filter (fun r : Fin s.vertices ↦ r.val ∈ roots)).sup
    (Tree.outgrowthHeight s.tree cutoff hcutoff)

theorem belowFreshHeight_iff_selectedFreshHeight_lt (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) {h : ℕ} (hh : 0 < h) (s : State) :
    belowFreshHeight cutoff hcutoff roots h s ↔ selectedFreshHeight cutoff hcutoff roots s < h :=
  belowFreshHeight_iff_sup_outgrowthHeight_lt cutoff hcutoff roots hh s

theorem successParameter_subcritical {m : ℝ} (hm : 0 < m) (hm1 : m < 1) :
    1 / 2 < (Branching.successParameter m hm.le : ℝ) ∧
      (Branching.successParameter m hm.le : ℝ) < 1 := by
  change 1 / 2 < 1 / (1 + m) ∧ 1 / (1 + m) < 1
  constructor
  · apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity)).mpr
    linarith
  · exact (div_lt_one (by positivity : 0 < 1 + m)).mpr (by linarith)

/-- The exact initial infection pressure is an admissible upper comparison mean. -/
theorem continuation_freshHeight_tail_le_initialPressure (rate : ℝ≥0) (s₀ : State)
    (roots : Finset ℕ) {h k : ℕ} (hh : 0 < h) (hk : potential s₀ ≤ k)
    (hm : 0 < (rate : ℝ) * s₀.susceptible) (hm1 : (rate : ℝ) * s₀.susceptible < 1) :
    (continuationLaw rate s₀ k).toMeasure.real
      {s | ¬belowFreshHeight s₀.vertices s₀.tree.size_pos roots h s} ≤
        (selectedRootCount s₀ roots : ℝ) * ((rate : ℝ) * s₀.susceptible) ^ h := by
  have hp := successParameter_subcritical hm hm1
  have hb := continuation_freshHeight_tail_le_geometric hp.1 hp.2 rate s₀ roots hh
    (show (Branching.successParameter ((rate : ℝ) * s₀.susceptible) hm.le : ℝ) ≤
      1 - (infectionProbability rate s₀.susceptible : ℝ) by
        rw [recoveryProbability_real]; exact le_rfl) hk
  simpa only [Branching.geometricMean_successParameter, selectedRootCount] using hb

theorem continuation_freshHeight_cdf_le_thresholdPressure (rate : ℝ≥0) (s₀ : State)
    (roots : Finset ℕ) {h k : ℕ} (hh : 0 < h) (hk : potential s₀ ≤ k) (threshold : ℕ)
    (hm : 0 < (rate : ℝ) * threshold) (hm1 : (rate : ℝ) * threshold < 1) :
    (continuationLaw rate s₀ k).toMeasure.real
      {s | belowFreshHeight s₀.vertices s₀.tree.size_pos roots h s} ≤
        Real.exp (-(selectedRootCount s₀ roots : ℝ) *
          ((1 - (rate : ℝ) * threshold) * ((rate : ℝ) * threshold) ^ h)) +
        (continuationLaw rate s₀ k).toMeasure.real {s | s.susceptible < threshold} := by
  have hp := successParameter_subcritical hm hm1
  have hb := continuation_freshHeight_cdf_le_geometric_exp hp.1 hp.2 rate s₀ roots hh threshold
    (show 1 - (infectionProbability rate threshold : ℝ) ≤
      (Branching.successParameter ((rate : ℝ) * threshold) hm.le : ℝ) by
        rw [recoveryProbability_real]; exact le_rfl) hk
  simpa only [Branching.geometricMean_successParameter, selectedRootCount] using hb

/-- Any level whose logarithmic slope lies above the geometric maximum scale
has vanishing actual upper tail. -/
theorem tendsto_outgrowth_upperTail_of_log_gap
    (rate : ℕ → ℝ≥0) (s₀ : ℕ → State) (roots : ℕ → Finset ℕ) (H K : ℕ → ℕ)
    {f a m : ℝ} (hf : 0 < f) (ha : 0 < a) (hm : 0 < m) (hm1 : m < 1)
    (hN : Tendsto (fun n ↦ Real.log (selectedRootCount (s₀ n) (roots n)) / Real.log n)
      atTop (𝓝 f))
    (hH : Tendsto (fun n ↦ (H n : ℝ) / Real.log n) atTop (𝓝 a))
    (hpressure : Tendsto (fun n ↦ (rate n : ℝ) * (s₀ n).susceptible) atTop (𝓝 m))
    (hK : ∀ᶠ n in atTop, potential (s₀ n) ≤ K n)
    (hgap : f + a * Real.log m < 0) :
    Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
      {s | ¬belowFreshHeight (s₀ n).vertices (s₀ n).tree.size_pos (roots n) (H n) s})
        atTop (𝓝 0) := by
  have hscale := tendsto_geometric_scale_zero
    (fun n ↦ selectedRootCount (s₀ n) (roots n)) H
    (fun n ↦ (rate n : ℝ) * (s₀ n).susceptible) hf hm hN hH hpressure hgap
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hscale
  filter_upwards [hK, hH.eventually (lt_mem_nhds ha),
    hpressure.eventually (lt_mem_nhds hm), hpressure.eventually (gt_mem_nhds hm1)]
    with n hkn hHn hmn hm1n
  have hHpos : 0 < H n := by
    by_contra hbad
    have hz : H n = 0 := Nat.eq_zero_of_not_pos hbad
    simp only [hz, Nat.cast_zero, zero_div, lt_self_iff_false] at hHn
  exact continuation_freshHeight_tail_le_initialPressure (rate n) (s₀ n) (roots n)
    hHpos hkn hmn hm1n

/-- Any level below the lower comparison scale is reached with high probability,
provided the actual terminal susceptible barrier error vanishes. -/
theorem tendsto_outgrowth_lowerTail_of_log_gap
    (rate : ℕ → ℝ≥0) (s₀ : ℕ → State) (roots : ℕ → Finset ℕ) (H K L : ℕ → ℕ)
    {f a m : ℝ} (hf : 0 < f) (ha : 0 < a) (hm : 0 < m) (hm1 : m < 1)
    (hN : Tendsto (fun n ↦ Real.log (selectedRootCount (s₀ n) (roots n)) / Real.log n)
      atTop (𝓝 f))
    (hH : Tendsto (fun n ↦ (H n : ℝ) / Real.log n) atTop (𝓝 a))
    (hpressure : Tendsto (fun n ↦ (rate n : ℝ) * L n) atTop (𝓝 m))
    (hK : ∀ᶠ n in atTop, potential (s₀ n) ≤ K n)
    (hbarrier : Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
      {s | s.susceptible < L n}) atTop (𝓝 0))
    (hgap : 0 < f + a * Real.log m) :
    Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
      {s | belowFreshHeight (s₀ n).vertices (s₀ n).tree.size_pos (roots n) (H n) s})
        atTop (𝓝 0) := by
  have hscale := tendsto_geometric_scale_atTop
    (fun n ↦ selectedRootCount (s₀ n) (roots n)) H
    (fun n ↦ (rate n : ℝ) * L n) hf hm hN hH hpressure hgap
  have hprod := hscale.atTop_mul_pos (sub_pos.mpr hm1) (tendsto_const_nhds.sub hpressure)
  have hexp := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hprod)
  have hsum := hexp.add hbarrier
  rw [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hsum
  filter_upwards [hK, hH.eventually (lt_mem_nhds ha),
    hpressure.eventually (lt_mem_nhds hm), hpressure.eventually (gt_mem_nhds hm1)]
    with n hkn hHn hmn hm1n
  have hHpos : 0 < H n := by
    by_contra hbad
    have hz : H n = 0 := Nat.eq_zero_of_not_pos hbad
    simp only [hz, Nat.cast_zero, zero_div, lt_self_iff_false] at hHn
  have hb := continuation_freshHeight_cdf_le_thresholdPressure (rate n) (s₀ n) (roots n)
    hHpos hkn (L n) hmn hm1n
  have heq : -(selectedRootCount (s₀ n) (roots n) : ℝ) *
      ((1 - (rate n : ℝ) * L n) * ((rate n : ℝ) * L n) ^ H n) =
      -(((selectedRootCount (s₀ n) (roots n) : ℝ) * ((rate n : ℝ) * L n) ^ H n) *
        (1 - (rate n : ℝ) * L n)) := by ring
  simpa only [Function.comp_apply, heq] using hb

/-- The normalized maximum has no upper tail beyond the scale fixed by the
limiting initial infection pressure. -/
theorem tendsto_normalized_outgrowth_upperTail
    (rate : ℕ → ℝ≥0) (s₀ : ℕ → State) (roots : ℕ → Finset ℕ) (K : ℕ → ℕ)
    {f m : ℝ} (hf : 0 < f) (hm : 0 < m) (hm1 : m < 1)
    (hN : Tendsto (fun n ↦ Real.log (selectedRootCount (s₀ n) (roots n)) / Real.log n)
      atTop (𝓝 f))
    (hpressure : Tendsto (fun n ↦ (rate n : ℝ) * (s₀ n).susceptible) atTop (𝓝 m))
    (hK : ∀ᶠ n in atTop, potential (s₀ n) ≤ K n) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
      {s | f / (-Real.log m) + ε ≤
        (selectedFreshHeight (s₀ n).vertices (s₀ n).tree.size_pos (roots n) s : ℝ) /
          Real.log n}) atTop (𝓝 0) := by
  let c := f / (-Real.log m)
  let a := c + ε / 2
  let H : ℕ → ℕ := fun n ↦ ⌈a * Real.log n⌉₊
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
  have ht := tendsto_outgrowth_upperTail_of_log_gap rate s₀ roots H K hf ha hm hm1
    hN hH hpressure hK hgap
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ ht
  filter_upwards [eventually_ge_atTop 2, hH.eventually (gt_mem_nhds haε)] with n hn hHn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hln : 0 < Real.log n := Real.log_pos hn'
  have hHpos : 0 < H n := Nat.ceil_pos.mpr (mul_pos ha hln)
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs ⊢
  rw [belowFreshHeight_iff_selectedFreshHeight_lt _ _ _ hHpos]
  apply not_lt.mpr
  have hle : (H n : ℝ) ≤
      selectedFreshHeight (s₀ n).vertices (s₀ n).tree.size_pos (roots n) s :=
    (div_le_div_iff_of_pos_right hln).mp (hHn.le.trans hs)
  exact_mod_cast hle

/-- The normalized maximum has no lower tail below the scale fixed by any
terminal susceptible barrier whose failure probability vanishes. -/
theorem tendsto_normalized_outgrowth_lowerTail
    (rate : ℕ → ℝ≥0) (s₀ : ℕ → State) (roots : ℕ → Finset ℕ) (K L : ℕ → ℕ)
    {f m : ℝ} (hf : 0 < f) (hm : 0 < m) (hm1 : m < 1)
    (hN : Tendsto (fun n ↦ Real.log (selectedRootCount (s₀ n) (roots n)) / Real.log n)
      atTop (𝓝 f))
    (hpressure : Tendsto (fun n ↦ (rate n : ℝ) * L n) atTop (𝓝 m))
    (hK : ∀ᶠ n in atTop, potential (s₀ n) ≤ K n)
    (hbarrier : Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
      {s | s.susceptible < L n}) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
      {s | (selectedFreshHeight (s₀ n).vertices (s₀ n).tree.size_pos (roots n) s : ℝ) /
        Real.log n ≤ f / (-Real.log m) - ε}) atTop (𝓝 0) := by
  let c := f / (-Real.log m)
  let a := max (c - ε / 2) (c / 2)
  let H : ℕ → ℕ := fun n ↦ ⌈a * Real.log n⌉₊
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
  have ht := tendsto_outgrowth_lowerTail_of_log_gap rate s₀ roots H K L hf ha hm hm1
    hN hH hpressure hK hbarrier hgap
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ ht
  filter_upwards [eventually_ge_atTop 2, hH.eventually (lt_mem_nhds hεa)] with n hn hHn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hln : 0 < Real.log n := Real.log_pos hn'
  have hHpos : 0 < H n := Nat.ceil_pos.mpr (mul_pos ha hln)
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs ⊢
  rw [belowFreshHeight_iff_selectedFreshHeight_lt _ _ _ hHpos]
  have hlt : (selectedFreshHeight (s₀ n).vertices (s₀ n).tree.size_pos (roots n) s : ℝ) < H n :=
    (div_lt_div_iff_of_pos_right hln).mp (hs.trans_lt hHn)
  exact_mod_cast hlt

/-- Convergence in probability of the actual maximum fresh height divided by
`log n`. Both pressure limits and the terminal barrier error are explicit;
the geometric forest asymptotics are proved dependencies, not hypotheses. -/
theorem normalized_outgrowthHeight_concentration
    (rate : ℕ → ℝ≥0) (s₀ : ℕ → State) (roots : ℕ → Finset ℕ) (K L : ℕ → ℕ)
    {f m : ℝ} (hf : 0 < f) (hm : 0 < m) (hm1 : m < 1)
    (hN : Tendsto (fun n ↦ Real.log (selectedRootCount (s₀ n) (roots n)) / Real.log n)
      atTop (𝓝 f))
    (hinitial : Tendsto (fun n ↦ (rate n : ℝ) * (s₀ n).susceptible) atTop (𝓝 m))
    (hthreshold : Tendsto (fun n ↦ (rate n : ℝ) * L n) atTop (𝓝 m))
    (hK : ∀ᶠ n in atTop, potential (s₀ n) ≤ K n)
    (hbarrier : Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
      {s | s.susceptible < L n}) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
      {s | ε ≤ |(selectedFreshHeight (s₀ n).vertices (s₀ n).tree.size_pos (roots n) s : ℝ) /
        Real.log n - f / (-Real.log m)|}) atTop (𝓝 0) := by
  have hlow := tendsto_normalized_outgrowth_lowerTail rate s₀ roots K L hf hm hm1
    hN hthreshold hK hbarrier hε
  have hupp := tendsto_normalized_outgrowth_upperTail rate s₀ roots K hf hm hm1
    hN hinitial hK hε
  have hsum := hlow.add hupp
  rw [add_zero] at hsum
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hsum
  intro n
  apply le_trans ?_ (measureReal_union_le _ _)
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro s hs
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hs ⊢
  rcases le_abs.mp hs with h | h
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)

/-- The lower comparison pressure only needs to approach the desired limiting
pressure from below. Each selected barrier retains its own vanishing error. -/
theorem tendsto_normalized_outgrowth_lowerTail_of_near_barriers
    (rate : ℕ → ℝ≥0) (s₀ : ℕ → State) (roots : ℕ → Finset ℕ) (K : ℕ → ℕ)
    {f m : ℝ} (hf : 0 < f) (hm : 0 < m) (hm1 : m < 1)
    (hN : Tendsto (fun n ↦ Real.log (selectedRootCount (s₀ n) (roots n)) / Real.log n)
      atTop (𝓝 f))
    (hK : ∀ᶠ n in atTop, potential (s₀ n) ≤ K n)
    (hbarriers : ∀ b : ℝ, 0 < b → b < m → ∃ m' : ℝ, ∃ L : ℕ → ℕ,
      b < m' ∧ m' < m ∧
      Tendsto (fun n ↦ (rate n : ℝ) * L n) atTop (𝓝 m') ∧
      Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
        {s | s.susceptible < L n}) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
      {s | (selectedFreshHeight (s₀ n).vertices (s₀ n).tree.size_pos (roots n) s : ℝ) /
        Real.log n ≤ f / (-Real.log m) - ε}) atTop (𝓝 0) := by
  let c := f / (-Real.log m)
  let a := max (c - ε / 2) (c / 2)
  have hlog := Real.log_neg hm hm1
  have hc : 0 < c := div_pos hf (neg_pos.mpr hlog)
  have hcf : c * (-Real.log m) = f := div_mul_cancel₀ f (neg_ne_zero.mpr hlog.ne)
  have ha : 0 < a := (half_pos hc).trans_le (le_max_right _ _)
  have hac : a < c := max_lt (by linarith) (by linarith)
  have hεa : c - ε < a := (by linarith : c - ε < c - ε / 2).trans_le (le_max_left _ _)
  have hgap : 0 < f + a * Real.log m := by
    have hb := mul_lt_mul_of_pos_right hac (neg_pos.mpr hlog)
    nlinarith only [hb, hcf]
  let b := Real.exp (-f / a)
  have hb : 0 < b := Real.exp_pos _
  have hbm : b < m := by
    rw [show m = Real.exp (Real.log m) from (Real.exp_log hm).symm]
    apply Real.exp_lt_exp.mpr
    exact (div_lt_iff₀ ha).mpr (by nlinarith only [hgap])
  obtain ⟨m', L, hbm', hm'm, hpressure, hbarrier⟩ := hbarriers b hb hbm
  have hm' : 0 < m' := hb.trans hbm'
  have hm'1 : m' < 1 := hm'm.trans hm1
  have hlog' := Real.log_neg hm' hm'1
  have hgap' : 0 < f + a * Real.log m' := by
    have ht := Real.log_lt_log hb hbm'
    change Real.log (Real.exp (-f / a)) < Real.log m' at ht
    rw [Real.log_exp] at ht
    have hh := (div_lt_iff₀ ha).mp ht
    nlinarith only [hh]
  have hac' : a < f / (-Real.log m') :=
    (lt_div_iff₀ (neg_pos.mpr hlog')).mpr (by nlinarith only [hgap'])
  have hε' : 0 < f / (-Real.log m') - (c - ε) := sub_pos.mpr (hεa.trans hac')
  have ht := tendsto_normalized_outgrowth_lowerTail rate s₀ roots K L hf hm' hm'1
    hN hpressure hK hbarrier hε'
  simpa only [sub_sub_cancel] using ht

/-- Convergence in probability using arbitrarily close lower susceptible
barriers, rather than assuming a barrier at the limiting pressure itself. -/
theorem normalized_outgrowthHeight_concentration_of_near_barriers
    (rate : ℕ → ℝ≥0) (s₀ : ℕ → State) (roots : ℕ → Finset ℕ) (K : ℕ → ℕ)
    {f m : ℝ} (hf : 0 < f) (hm : 0 < m) (hm1 : m < 1)
    (hN : Tendsto (fun n ↦ Real.log (selectedRootCount (s₀ n) (roots n)) / Real.log n)
      atTop (𝓝 f))
    (hinitial : Tendsto (fun n ↦ (rate n : ℝ) * (s₀ n).susceptible) atTop (𝓝 m))
    (hK : ∀ᶠ n in atTop, potential (s₀ n) ≤ K n)
    (hbarriers : ∀ b : ℝ, 0 < b → b < m → ∃ m' : ℝ, ∃ L : ℕ → ℕ,
      b < m' ∧ m' < m ∧
      Tendsto (fun n ↦ (rate n : ℝ) * L n) atTop (𝓝 m') ∧
      Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
        {s | s.susceptible < L n}) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (continuationLaw (rate n) (s₀ n) (K n)).toMeasure.real
      {s | ε ≤ |(selectedFreshHeight (s₀ n).vertices (s₀ n).tree.size_pos (roots n) s : ℝ) /
        Real.log n - f / (-Real.log m)|}) atTop (𝓝 0) := by
  have hlow := tendsto_normalized_outgrowth_lowerTail_of_near_barriers rate s₀ roots K
    hf hm hm1 hN hK hbarriers hε
  have hupp := tendsto_normalized_outgrowth_upperTail rate s₀ roots K hf hm hm1
    hN hinitial hK hε
  have hsum := hlow.add hupp
  rw [add_zero] at hsum
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hsum
  intro n
  apply le_trans ?_ (measureReal_union_le _ _)
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro s hs
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hs ⊢
  rcases le_abs.mp hs with h | h
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)

end HeightPaper.Model
