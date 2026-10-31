module

public import HeightPaper.Model.RandomOutgrowth

/-! # Finite-bin and limiting estimates after random-cutoff averaging -/

public section

open Filter MeasureTheory
open scoped Topology NNReal BigOperators

namespace HeightPaper.Model

/-- A finite family of upper height bounds shares one exceptional-cutoff
error. Neither independence of the bins nor conditioning normalization is used. -/
theorem randomOutgrowth_finite_union_upper_bound {ι : Type*} (bins : Finset ι)
    (μ : PMF State) (hμ : μ.support.Finite) (rate : ℝ≥0) (K : ℕ)
    (roots : ι → State → Finset ℕ) (A G : Set State)
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (H : ι → ℕ) (hH : ∀ b ∈ bins, 0 < H b) (M : ι → ℝ)
    (hM : ∀ b ∈ bins, 0 ≤ M b)
    (hgood : ∀ s ∈ μ.support, s ∈ A → s ∈ G →
      potential s ≤ K ∧ (p : ℝ) ≤ 1 - (infectionProbability rate s.susceptible : ℝ) ∧
        ∀ b ∈ bins, (selectedRootCount s (roots b s) : ℝ) ≤ M b) :
    (continuationSampleLaw μ rate K).toMeasure.real {x | x.cutoff ∈ A ∧
      ∃ b ∈ bins, ¬belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos
        (roots b x.cutoff) (H b) x.final} ≤
      (∑ b ∈ bins, M b * Branching.geometricMean p ^ H b) + μ.toMeasure.real (A \ G) := by
  classical
  have hm : 0 ≤ Branching.geometricMean p := (Branching.geometricMean_pos
    (by linarith : 0 < (p : ℝ)) hp1).le
  have hC : 0 ≤ ∑ b ∈ bins, M b * Branching.geometricMean p ^ H b :=
    Finset.sum_nonneg fun b hb ↦ mul_nonneg (hM b hb) (pow_nonneg hm _)
  have hb := continuationSampleLaw_restricted_bound μ hμ rate K A G
    (fun s ↦ {t | ∃ b ∈ bins, ¬belowFreshHeight s.vertices s.tree.size_pos (roots b s) (H b) t})
    (fun _ ↦ 0) hC (fun _ ↦ le_rfl) ?_
  · have hz : A.indicator (fun _ : State ↦ (0 : ℝ)) = fun _ ↦ 0 := by
      funext s
      simp [Set.indicator]
    simpa only [hz, integral_zero, add_zero, Set.mem_ofPred_eq] using hb
  · intro s hs hA hG
    obtain ⟨hK, hpr, hN⟩ := hgood s hs hA hG
    have heq : {t | ∃ b ∈ bins, ¬belowFreshHeight s.vertices s.tree.size_pos (roots b s) (H b) t} =
        ⋃ b ∈ bins, {t | ¬belowFreshHeight s.vertices s.tree.size_pos (roots b s) (H b) t} := by
      ext t
      simp
    rw [heq, add_zero]
    apply (measureReal_biUnion_finset_le bins _).trans
    apply Finset.sum_le_sum
    intro b hb
    apply (continuation_freshHeight_tail_le_geometric hp hp1 rate s (roots b s)
      (hH b hb) hpr hK).trans
    exact mul_le_mul_of_nonneg_right (hN b hb) (pow_nonneg hm _)

theorem tendsto_randomOutgrowth_upper_zero
    (μ : ℕ → PMF State) (hμ : ∀ n, (μ n).support.Finite) (rate : ℕ → ℝ≥0)
    (K H : ℕ → ℕ) (roots : ℕ → State → Finset ℕ) (A G : ℕ → Set State)
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (M : ℕ → ℝ)
    (hvalid : ∀ᶠ n in atTop, 0 < H n ∧ 0 ≤ M n ∧
      ∀ s ∈ (μ n).support, s ∈ A n → s ∈ G n →
        potential s ≤ K n ∧ (p : ℝ) ≤ 1 - (infectionProbability (rate n) s.susceptible : ℝ) ∧
          (selectedRootCount s (roots n s) : ℝ) ≤ M n)
    (hscale : Tendsto (fun n ↦ M n * Branching.geometricMean p ^ H n) atTop (𝓝 0))
    (hbad : Tendsto (fun n ↦ (μ n).toMeasure.real (A n \ G n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (continuationSampleLaw (μ n) (rate n) (K n)).toMeasure.real
      {x | x.cutoff ∈ A n ∧ ¬belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos
        (roots n x.cutoff) (H n) x.final}) atTop (𝓝 0) := by
  have ht := hscale.add hbad
  rw [add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ ht
  filter_upwards [hvalid] with n hn
  exact randomOutgrowth_upper_bound (μ n) (hμ n) (rate n) (K n) (roots n) (A n) (G n)
    hp hp1 hn.1 hn.2.1 hn.2.2

theorem tendsto_randomOutgrowth_lower_zero
    (μ : ℕ → PMF State) (hμ : ∀ n, (μ n).support.Finite) (rate : ℕ → ℝ≥0)
    (K H L : ℕ → ℕ) (roots : ℕ → State → Finset ℕ) (A G : ℕ → Set State)
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (M : ℕ → ℝ)
    (hvalid : ∀ᶠ n in atTop, 0 < H n ∧
      1 - (infectionProbability (rate n) (L n) : ℝ) ≤ (p : ℝ) ∧
      ∀ s ∈ (μ n).support, s ∈ A n → s ∈ G n →
        potential s ≤ K n ∧ M n ≤ (selectedRootCount s (roots n s) : ℝ))
    (hscale : Tendsto (fun n ↦ M n * Branching.geometricMean p ^ H n) atTop atTop)
    (hbad : Tendsto (fun n ↦ (μ n).toMeasure.real (A n \ G n)) atTop (𝓝 0))
    (hbarrier : Tendsto (fun n ↦ (continuationSampleLaw (μ n) (rate n) (K n)).toMeasure.real
      {x | x.cutoff ∈ A n ∧ x.final.susceptible < L n}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (continuationSampleLaw (μ n) (rate n) (K n)).toMeasure.real
      {x | x.cutoff ∈ A n ∧ belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos
        (roots n x.cutoff) (H n) x.final}) atTop (𝓝 0) := by
  have hm1 := Branching.geometricMean_lt_one hp
  have hexp := Real.tendsto_exp_atBot.comp
    (hscale.const_mul_atTop_of_neg (by linarith : -(1 - Branching.geometricMean p) < 0))
  have ht := (hexp.add hbad).add hbarrier
  simp only [add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ ht
  filter_upwards [hvalid] with n hn
  have heq : -(M n) * ((1 - Branching.geometricMean p) * Branching.geometricMean p ^ H n) =
      -(1 - Branching.geometricMean p) * (M n * Branching.geometricMean p ^ H n) := by ring
  simpa only [Function.comp_apply, heq] using randomOutgrowth_lower_bound
    (μ n) (hμ n) (rate n) (K n) (roots n) (A n) (G n) hp hp1 hn.1 (L n) hn.2.1 hn.2.2

/-- A fixed finite mesh of height thresholds has vanishing joint failure
probability once every numerical geometric upper count and the common
exceptional-cutoff probability vanish. -/
theorem tendsto_randomOutgrowth_finite_union_upper_zero {ι : Type*} (bins : Finset ι)
    (μ : ℕ → PMF State) (hμ : ∀ n, (μ n).support.Finite) (rate : ℕ → ℝ≥0)
    (K : ℕ → ℕ) (H : ι → ℕ → ℕ) (roots : ι → ℕ → State → Finset ℕ)
    (A G : ℕ → Set State) {p : unitInterval}
    (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (M : ι → ℕ → ℝ)
    (hvalid : ∀ᶠ n in atTop, (∀ b ∈ bins, 0 < H b n ∧ 0 ≤ M b n) ∧
      ∀ s ∈ (μ n).support, s ∈ A n → s ∈ G n →
        potential s ≤ K n ∧ (p : ℝ) ≤ 1 - (infectionProbability (rate n) s.susceptible : ℝ) ∧
          ∀ b ∈ bins, (selectedRootCount s (roots b n s) : ℝ) ≤ M b n)
    (hscale : ∀ b ∈ bins, Tendsto
      (fun n ↦ M b n * Branching.geometricMean p ^ H b n) atTop (𝓝 0))
    (hbad : Tendsto (fun n ↦ (μ n).toMeasure.real (A n \ G n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (continuationSampleLaw (μ n) (rate n) (K n)).toMeasure.real
      {x | x.cutoff ∈ A n ∧ ∃ b ∈ bins, ¬belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos
        (roots b n x.cutoff) (H b n) x.final}) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n ↦ ∑ b ∈ bins, M b n * Branching.geometricMean p ^ H b n)
      atTop (𝓝 0) := by simpa using tendsto_finsetSum bins hscale
  have ht := hsum.add hbad
  rw [add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ ht
  filter_upwards [hvalid] with n hn
  exact randomOutgrowth_finite_union_upper_bound bins (μ n) (hμ n) (rate n) (K n)
    (fun b ↦ roots b n) (A n) (G n) hp hp1 (fun b ↦ H b n) (fun b hb ↦ (hn.1 b hb).1)
    (fun b ↦ M b n) (fun b hb ↦ (hn.1 b hb).2) hn.2

end HeightPaper.Model
