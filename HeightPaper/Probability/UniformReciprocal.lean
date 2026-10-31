module

public import HeightPaper.Probability.UniformActiveCounts

/-!
# Reciprocal sums on macroscopic surviving intervals

Uniform infectious lower bounds make the late reciprocal sum bounded in
probability and its squared counterpart negligible. These estimates are the
macroscopic part of the profile-normalizer control.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

/-- Deterministic reciprocal-sum bound from a uniform count lower bound. -/
theorem reciprocal_sum_le_of_count_lower (path : ℕ → State) {n lo hi : ℕ}
    {c : ℝ} (hc : 0 < c) (hn : 0 < n)
    (hcount : ∀ k ∈ Finset.Ico lo hi, c * n ≤ infectious (path k)) :
    (∑ k ∈ Finset.Ico lo hi, 1 / (infectious (path k) : ℝ)) ≤
      (hi : ℝ) / (c * n) := by
  have hd : 0 < c * n := by positivity
  calc
    (∑ k ∈ Finset.Ico lo hi, 1 / (infectious (path k) : ℝ)) ≤
        ∑ _k ∈ Finset.Ico lo hi, 1 / (c * n) := by
          apply Finset.sum_le_sum
          intro k hk
          exact one_div_le_one_div_of_le hd (hcount k hk)
    _ = ((hi - lo : ℕ) : ℝ) / (c * n) := by simp [div_eq_mul_inv]
    _ ≤ (hi : ℝ) / (c * n) :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le hi lo) hd.le

/-- Deterministic squared-reciprocal bound from the same lower bound. -/
theorem reciprocal_square_sum_le_of_count_lower (path : ℕ → State) {n lo hi : ℕ}
    {c : ℝ} (hc : 0 < c) (hn : 0 < n)
    (hcount : ∀ k ∈ Finset.Ico lo hi, c * n ≤ infectious (path k)) :
    (∑ k ∈ Finset.Ico lo hi, 1 / (infectious (path k) : ℝ) ^ 2) ≤
      (hi : ℝ) / (c * n) ^ 2 := by
  have hd : 0 < c * n := by positivity
  calc
    (∑ k ∈ Finset.Ico lo hi, 1 / (infectious (path k) : ℝ) ^ 2) ≤
        ∑ _k ∈ Finset.Ico lo hi, 1 / (c * n) ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          apply one_div_le_one_div_of_le (sq_pos_of_pos hd)
          exact pow_le_pow_left₀ hd.le (hcount k hk) 2
    _ = ((hi - lo : ℕ) : ℝ) / (c * n) ^ 2 := by simp [div_eq_mul_inv]
    _ ≤ (hi : ℝ) / (c * n) ^ 2 :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le hi lo) (sq_nonneg _)

/-- The reciprocal count sum over a macroscopic interval is bounded by a
fixed constant with probability tending to one, on survival to its endpoint. -/
theorem path_late_reciprocal_sum_bounded
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l a T : ℝ} (hl : 1 < l)
    (ha : 0 < a) (haT : a < T) (hT : T < fluidExtinctionTime l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun n ↦ (pathMeasure (rates n) n (horizon n)).real
      {p | (p.eval (horizon n)).active.Nonempty ∧
        C ≤ ∑ k ∈ Finset.Ico ⌊a * n⌋₊ (horizon n), 1 / (infectious (p.eval k) : ℝ)})
      atTop (𝓝 0) := by
  obtain ⟨c, hc, hbad⟩ := path_uniform_active_count_lower rates horizon hl ha haT hT hrates hhorizon
  let C := (T + 1) / c + 1
  have hC : 0 < C := by dsimp [C]; have hT0 := ha.trans haT; positivity
  refine ⟨C, hC, ?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hbad
  filter_upwards [hhorizon.eventually (Iio_mem_nhds (show T < T + 1 by linarith)),
    eventually_gt_atTop 0] with n hn hn0
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro p hp
  refine ⟨hp.1, ?_⟩
  by_contra hnone
  have hcount (k : ℕ) (hk : k ∈ Finset.Ico ⌊a * n⌋₊ (horizon n)) :
      c * n ≤ infectious (p.eval k) := by
    by_contra hh
    exact hnone ⟨k, (Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2.le, lt_of_not_ge hh⟩
  have hsum := reciprocal_sum_le_of_count_lower p.eval hc hn0 hcount
  have hden : (horizon n : ℝ) / (c * n) = ((horizon n : ℝ) / n) / c := by ring
  rw [hden] at hsum
  have hdiv := (div_lt_div_iff_of_pos_right hc).mpr hn
  have hpbound : C ≤ ∑ k ∈ Finset.Ico ⌊a * n⌋₊ (horizon n), 1 / (infectious (p.eval k) : ℝ) := hp.2
  dsimp [C] at hpbound
  linarith

/-- The quadratic reciprocal error on a macroscopic interval vanishes in
probability on survival. -/
theorem path_late_reciprocal_square_sum_tendsto_zero
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l a T : ℝ} (hl : 1 < l)
    (ha : 0 < a) (haT : a < T) (hT : T < fluidExtinctionTime l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (pathMeasure (rates n) n (horizon n)).real
      {p | (p.eval (horizon n)).active.Nonempty ∧
        ε ≤ ∑ k ∈ Finset.Ico ⌊a * n⌋₊ (horizon n), 1 / (infectious (p.eval k) : ℝ) ^ 2})
      atTop (𝓝 0) := by
  obtain ⟨c, hc, hbad⟩ := path_uniform_active_count_lower rates horizon hl ha haT hT hrates hhorizon
  have hbound : Tendsto (fun n : ℕ ↦ (horizon n : ℝ) / (c * n) ^ 2) atTop (𝓝 0) := by
    have hh := (hhorizon.mul (tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))).div_const (c ^ 2)
    simp only [mul_zero, zero_div] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hbad
  filter_upwards [hbound.eventually (Iio_mem_nhds hε), eventually_gt_atTop 0] with n hn hn0
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro p hp
  refine ⟨hp.1, ?_⟩
  by_contra hnone
  have hcount (k : ℕ) (hk : k ∈ Finset.Ico ⌊a * n⌋₊ (horizon n)) :
      c * n ≤ infectious (p.eval k) := by
    by_contra hh
    exact hnone ⟨k, (Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2.le, lt_of_not_ge hh⟩
  have hsum := reciprocal_square_sum_le_of_count_lower p.eval hc hn0 hcount
  have hpbound : ε ≤ ∑ k ∈ Finset.Ico ⌊a * n⌋₊ (horizon n), 1 / (infectious (p.eval k) : ℝ) ^ 2 := hp.2
  linarith

end HeightPaper.Model
