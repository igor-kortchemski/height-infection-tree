module

public import HeightPaper.Model.HeightMeshBounds
public import HeightPaper.Model.RandomOutgrowthProfile

/-! # Full-height mesh limits derived from active profile exponents -/

public section

open Filter MeasureTheory
open scoped Topology NNReal BigOperators

namespace HeightPaper.Model

private theorem eventually_height_pos_of_ratio (H : ℕ → ℕ) {a : ℝ} (ha : 0 < a)
    (hH : Tendsto (fun n ↦ (H n : ℝ) / Real.log n) atTop (𝓝 a)) :
    ∀ᶠ n in atTop, 0 < H n := by
  filter_upwards [hH.eventually (lt_mem_nhds ha)] with n hn
  by_contra hbad
  have hz : H n = 0 := Nat.eq_zero_of_not_pos hbad
  simp only [hz, Nat.cast_zero, zero_div, lt_self_iff_false] at hn

/-- A fixed finite mesh gives the full-height upper bound from actual profile
exponents and pressure estimates. Fresh-height tail limits are derived here. -/
theorem fullHeight_upper_mesh_of_profiles
    (rate : ℕ → ℝ≥0) (j K T : ℕ → ℕ) {ι : Type*} (bins : Finset ι)
    (roots : ι → ℕ → State → Finset ℕ) (D H : ι → ℕ → ℕ) (A G : ℕ → Set State)
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (f a : ι → ℝ) (hf : ∀ b ∈ bins, 0 < f b) (ha : ∀ b ∈ bins, 0 < a b)
    (hprofile : ∀ b ∈ bins, ∀ ε > (0 : ℝ), Tendsto (fun n ↦
      (evolve (rate n) n (j n)).toMeasure.real {s | s ∈ A n ∧
        ε ≤ |Real.log (selectedRootCount s (roots b n s)) / Real.log n - f b|}) atTop (𝓝 0))
    (hH : ∀ b ∈ bins, Tendsto (fun n ↦ (H b n : ℝ) / Real.log n) atTop (𝓝 (a b)))
    (hK : ∀ᶠ n in atTop, ∀ s ∈ (evolve (rate n) n (j n)).support,
      s ∈ A n → potential s ≤ K n)
    (hpressure : Tendsto (fun n ↦ (evolve (rate n) n (j n)).toMeasure.real {s | s ∈ A n ∧
      1 - (infectionProbability (rate n) s.susceptible : ℝ) < (p : ℝ)}) atTop (𝓝 0))
    (hgap : ∀ b ∈ bins, f b + a b * Real.log (Branching.geometricMean p) < 0)
    (hgeom : ∀ᶠ n in atTop, (∀ b ∈ bins, D b n + H b n ≤ T n) ∧
      ∀ s ∈ (evolve (rate n) n (j n)).support, s ∈ A n → s ∈ G n →
        height s ≤ T n ∧
        (∀ b ∈ bins, roots b n s ⊆ activeLabels s) ∧
        (∀ v ∈ s.active, ∃ b ∈ bins, v.val ∈ roots b n s) ∧
        (∀ b ∈ bins, ∀ v : Fin s.vertices, v.val ∈ roots b n s → s.tree.depth v ≤ D b n))
    (hbad : Tendsto (fun n ↦ (evolve (rate n) n (j n)).toMeasure.real (A n \ G n))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ (continuationSampleLaw (evolve (rate n) n (j n)) (rate n) (K n)).toMeasure.real
      {x | x.cutoff ∈ A n ∧ T n < height x.final}) atTop (𝓝 0) := by
  have hbin : ∀ b ∈ bins, Tendsto (fun n ↦
      (continuationSampleLaw (evolve (rate n) n (j n)) (rate n) (K n)).toMeasure.real
        {x | x.cutoff ∈ A n ∧ ¬belowFreshHeight x.cutoff.vertices x.cutoff.tree.size_pos
          (roots b n x.cutoff) (H b n) x.final}) atTop (𝓝 0) := by
    intro b hb
    exact randomOutgrowth_upper_of_profile (fun n ↦ evolve (rate n) n (j n))
      (fun n ↦ evolve_support_finite _ _ _) rate K (H b) (roots b) A hp hp1
      (hf b hb) (ha b hb) (hprofile b hb) (hH b hb) hK hpressure (hgap b hb)
  have hsum := tendsto_finsetSum bins hbin
  simp only [Finset.sum_const_zero] at hsum
  have ht := hbad.add hsum
  rw [add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ ht
  have hpos : ∀ᶠ n in atTop, ∀ b ∈ bins, 0 < H b n :=
    (eventually_all_finset bins).mpr fun b hb ↦ eventually_height_pos_of_ratio (H b) (ha b hb) (hH b hb)
  filter_upwards [hgeom, hpos] with n hn hpn
  exact fullHeight_upper_mesh_bound (rate n) n (j n) (K n) (T n) bins (fun b ↦ roots b n)
    (fun b ↦ D b n) (fun b ↦ H b n) (A n) (G n) hpn hn.1 hn.2

/-- One positive profile bin gives the full-height lower bound. Its positive
root count is derived in probability from the profile exponent. -/
theorem fullHeight_lower_bin_of_profile
    (rate : ℕ → ℝ≥0) (j K d H L : ℕ → ℕ) (roots : ℕ → State → Finset ℕ) (A : ℕ → Set State)
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {f a : ℝ} (hf : 0 < f) (ha : 0 < a)
    (hprofile : ∀ ε > (0 : ℝ), Tendsto (fun n ↦
      (evolve (rate n) n (j n)).toMeasure.real {s | s ∈ A n ∧
        ε ≤ |Real.log (selectedRootCount s (roots n s)) / Real.log n - f|}) atTop (𝓝 0))
    (hH : Tendsto (fun n ↦ (H n : ℝ) / Real.log n) atTop (𝓝 a))
    (hK : ∀ᶠ n in atTop, ∀ s ∈ (evolve (rate n) n (j n)).support,
      s ∈ A n → potential s ≤ K n)
    (hpressure : ∀ᶠ n in atTop, 1 - (infectionProbability (rate n) (L n) : ℝ) ≤ (p : ℝ))
    (hbarrier : Tendsto (fun n ↦
      (continuationSampleLaw (evolve (rate n) n (j n)) (rate n) (K n)).toMeasure.real
        {x | x.cutoff ∈ A n ∧ x.final.susceptible < L n}) atTop (𝓝 0))
    (hgap : 0 < f + a * Real.log (Branching.geometricMean p))
    (hgeom : ∀ᶠ n in atTop, ∀ s ∈ (evolve (rate n) n (j n)).support, s ∈ A n →
      roots n s ⊆ activeLabels s ∧
        ∀ v : Fin s.vertices, v.val ∈ roots n s → d n ≤ s.tree.depth v) :
    Tendsto (fun n ↦ (continuationSampleLaw (evolve (rate n) n (j n)) (rate n) (K n)).toMeasure.real
      {x | x.cutoff ∈ A n ∧ height x.final < d n + H n}) atTop (𝓝 0) := by
  let G : ℕ → Set State := fun n ↦ {s | 0 < selectedRootCount s (roots n s)}
  have hbad : Tendsto (fun n ↦ (evolve (rate n) n (j n)).toMeasure.real (A n \ G n))
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ (hprofile (f / 2) (half_pos hf))
    intro n
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro s hs
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, G] at hs ⊢
    have hz : selectedRootCount s (roots n s) = 0 := Nat.eq_zero_of_not_pos hs.2
    refine ⟨hs.1, ?_⟩
    simp only [hz, Nat.cast_zero, Real.log_zero, zero_div, zero_sub, abs_neg, abs_of_pos hf]
    exact (half_lt_self hf).le
  have hbin := randomOutgrowth_lower_of_profile (fun n ↦ evolve (rate n) n (j n))
    (fun n ↦ evolve_support_finite _ _ _) rate K H L roots A hp hp1 hf ha hprofile hH
    hK hpressure hbarrier hgap
  have ht := hbad.add hbin
  rw [add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ ht
  filter_upwards [hgeom, eventually_height_pos_of_ratio H ha hH] with n hgn hHn
  apply fullHeight_lower_bin_bound (rate n) n (j n) (K n) (d n) (H n) (roots n) (A n) (G n) hHn
  intro s hs hA hG
  exact ⟨(hgn s hs hA).1, hG, (hgn s hs hA).2⟩

end HeightPaper.Model
