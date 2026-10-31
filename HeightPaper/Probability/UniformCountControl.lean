module

public import HeightPaper.Analysis.CompactUniform
public import HeightPaper.Probability.GoodEventWords

/-!
# Whole-horizon count-ratio tightness, weakly uniform in the parameter

The actual epidemic path law satisfies the first count control in the strong
profile proof. The entire time interval lies inside the bad event, and the
constant is independent of the parameter on a compact set. The proof uses
the inherited finite-population count estimates and a compactness argument.
It does not assume a joint coupling with the local random walk.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

/-- Upper tail of the largest count ratio, killed unless the epidemic is
still active at the full observation horizon. -/
def survivingCountRatioTail (M : ℝ) (H : ℕ) : Set (FinitePath H) :=
  {p | p.last.active.Nonempty ∧ ∃ k ≤ H, M < (k : ℝ) / infectious (p.eval k)}

theorem survivingCountRatioTail_antitone (H : ℕ) :
    Antitone (fun M : ℝ ↦ survivingCountRatioTail M H) := by
  intro M N h p hp
  obtain ⟨ha, k, hk, hb⟩ := hp
  exact ⟨ha, k, hk, h.trans_lt hb⟩

/-- Whole-horizon tightness along every convergent sequence of rates. -/
theorem path_surviving_count_ratio_tight
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ᶠ n in atTop, (pathMeasure (rates n) n (horizon n)).real
      (survivingCountRatioTail M (horizon n)) < ε := by
  let d := (l - 1) / (l + 1)
  have hd : 0 < d := div_pos (by linarith) (by linarith)
  obtain ⟨early, a, c, B, ha, hc, hB, hgood⟩ :=
    exists_goodCountWord_probability_control rates horizon hl hT (half_pos hd)
      (half_lt_self hd) (show d < d + 1 by linarith) hrates hhorizon
  obtain ⟨K, hK, hprob⟩ := hgood ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (max (K : ℝ) (1 / c))
  refine ⟨M, ?_⟩
  filter_upwards [hprob] with n hn
  apply lt_of_le_of_lt _ hn.2.2.2
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet (survivingCountRatioTail M (horizon n)) from trivial)
  intro p hp
  have hs := (mem_support_pathLaw_iff p).mp hp.2
  refine ⟨hp.1.1, ?_⟩
  intro hg
  obtain ⟨k, hk, hbad⟩ := hp.1.2
  have hactive : (p.eval (horizon n)).active.Nonempty := by
    rw [FinitePath.eval_last]
    exact hp.1.1
  have hi : (1 : ℝ) ≤ infectious (p.eval k) := by
    exact_mod_cast (hs.active_of_active_later hk le_rfl hactive).card_pos
  have hbound : (k : ℝ) / infectious (p.eval k) ≤ max (K : ℝ) (1 / c) := by
    by_cases hkK : k < K
    · exact (div_le_self (Nat.cast_nonneg k) hi).trans
        ((by exact_mod_cast hkK.le : (k : ℝ) ≤ K).trans (le_max_left _ _))
    · have hlow := hg.2.1 k (by omega) hk
      rw [hs.observedWalk_eq hactive hk] at hlow
      apply le_trans _ (le_max_right _ _)
      apply (div_le_iff₀ (zero_lt_one.trans_le hi)).mpr
      rw [one_div_mul_eq_div]
      exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hlow)
  exact not_lt_of_ge hbound (hM.trans hbad)

/-- The first estimate of the paper's count-control lemma, with weak uniformity
on any compact parameter set and the supremum over the whole time interval
inside probability. The event is survival through the specified integer horizon. -/
theorem uniform_surviving_count_ratio_tight {K : Set ℝ≥0} (hK : IsCompact K)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ K, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M N : ℕ, ∀ n ≥ N, ∀ l ∈ K,
      (pathMeasure (l / n) n ⌊T * n⌋₊).real
        (survivingCountRatioTail M ⌊T * n⌋₊) < ε := by
  let p : ℕ → ℝ≥0 → ℕ → ℝ := fun n l M ↦
    (pathMeasure (l / n) n ⌊T * n⌋₊).real (survivingCountRatioTail M ⌊T * n⌋₊)
  apply compact_uniform_tight_of_sequence hK p ?_ ?_ ε hε
  · intro n l i j hij
    exact measureReal_mono (survivingCountRatioTail_antitone _ (by exact_mod_cast hij))
  · intro l hl ls hls η hη
    have hreal : Tendsto (fun n ↦ (ls n : ℝ)) atTop (𝓝 (l : ℝ)) :=
      NNReal.continuous_coe.continuousAt.tendsto.comp hls
    have hrates : Tendsto (fun n ↦ ((ls n / n : ℝ≥0) : ℝ) * n) atTop (𝓝 (l : ℝ)) := by
      apply hreal.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp only [NNReal.coe_div, NNReal.coe_natCast, div_mul_cancel₀ _ hnR]
    exact path_surviving_count_ratio_tight (fun n ↦ ls n / n) (fun n ↦ ⌊T * n⌋₊)
      (hparams l hl).1 ⟨hT, (hparams l hl).2⟩ hrates
      (tendsto_floor_fraction hT.le) hη

/-- Late visits to any fixed positive count threshold have uniformly small
probability on surviving full histories. This is the stochastic safe-cutoff
input; the threshold may be a common bound for the compact set of tilts. -/
theorem uniform_surviving_safe_count_tight {K : Set ℝ≥0} (hK : IsCompact K)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ K, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J N : ℕ, ∀ n ≥ N, ∀ l ∈ K,
      (pathMeasure (l / n) n ⌊T * n⌋₊).real {p | p.last.active.Nonempty ∧
        ∃ k, J ≤ k ∧ k ≤ ⌊T * n⌋₊ ∧
          0 < infectious (p.eval k) ∧ (infectious (p.eval k) : ℝ) ≤ B} < ε := by
  obtain ⟨M, N, hMN⟩ := uniform_surviving_count_ratio_tight hK hT hparams hε
  obtain ⟨J, hJ⟩ := exists_nat_gt ((M : ℝ) * B)
  refine ⟨J, N, ?_⟩
  intro n hn l hl
  apply lt_of_le_of_lt (measureReal_mono ?_) (hMN n hn l hl)
  intro p hp
  obtain ⟨ha, k, hkJ, hk, hi, hB⟩ := hp
  refine ⟨ha, k, hk, ?_⟩
  have hiR : (0 : ℝ) < infectious (p.eval k) := by exact_mod_cast hi
  apply (lt_div_iff₀ hiR).mpr
  exact (mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg M)).trans_lt
    (hJ.trans_le (by exact_mod_cast hkJ))

/-- A bound on every count ratio gives the summable quadratic reciprocal tail.
The ordinary inverse convention makes extinct counts contribute zero. -/
theorem reciprocalSquare_tail_le_of_ratio (count : ℕ → ℕ) {M : ℝ}
    (K H : ℕ) (hcount : ∀ k ≤ H, (k : ℝ) / count k ≤ M) :
    (∑ k ∈ Finset.Ioo K (H + 1), ((count k : ℝ) ^ 2)⁻¹) ≤
      M ^ 2 * (2 / (K + 1)) := by
  have hpoint (k : ℕ) (hk : k ∈ Finset.Ioo K (H + 1)) :
      ((count k : ℝ) ^ 2)⁻¹ ≤ M ^ 2 * ((k : ℝ) ^ 2)⁻¹ := by
    have hk0 : 0 < k := by have := (Finset.mem_Ioo.mp hk).1; omega
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
    have hratio := hcount k (by have := (Finset.mem_Ioo.mp hk).2; omega)
    have hs := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg _)) hratio 2)
      (inv_nonneg.mpr (sq_nonneg (k : ℝ)))
    have heq : ((k : ℝ) / count k) ^ 2 * ((k : ℝ) ^ 2)⁻¹ = ((count k : ℝ) ^ 2)⁻¹ := by
      rw [div_pow, div_eq_mul_inv]
      calc
        _ = ((k : ℝ) ^ 2 * ((k : ℝ) ^ 2)⁻¹) * ((count k : ℝ) ^ 2)⁻¹ := by ring
        _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero 2 hkR), one_mul]
    rwa [heq] at hs
  calc
    _ ≤ ∑ k ∈ Finset.Ioo K (H + 1), M ^ 2 * ((k : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum hpoint
    _ = M ^ 2 * ∑ k ∈ Finset.Ioo K (H + 1), ((k : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le (α := ℝ) K (H + 1)) (sq_nonneg M)

/-- The quadratic reciprocal tail vanishes uniformly over the whole surviving
history and the compact parameter set. This controls the logarithm remainder
in products, without a logarithmic normalization. -/
theorem uniform_surviving_reciprocal_square_tail {A : Set ℝ≥0} (hA : IsCompact A)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ A, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ K N : ℕ, ∀ n ≥ N, ∀ l ∈ A,
      (pathMeasure (l / n) n ⌊T * n⌋₊).real {p | p.last.active.Nonempty ∧ ε <
        ∑ k ∈ Finset.Ioo K (⌊T * n⌋₊ + 1), ((infectious (p.eval k) : ℝ) ^ 2)⁻¹} < η := by
  obtain ⟨M, N, hMN⟩ := uniform_surviving_count_ratio_tight hA hT hparams hη
  have htail : Tendsto (fun K : ℕ ↦ (M : ℝ) ^ 2 * (2 / ((K : ℝ) + 1))) atTop (𝓝 0) := by
    have h := ((tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun k : ℕ ↦ (1 : ℝ) / k) atTop (𝓝 0)).comp
        (tendsto_add_atTop_nat 1)).const_mul ((M : ℝ) ^ 2 * 2)
    convert h using 1
    · funext K
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring
    · simp
  obtain ⟨K, hK⟩ := (htail.eventually (Iio_mem_nhds hε)).exists
  refine ⟨K, N, ?_⟩
  intro n hn l hl
  apply lt_of_le_of_lt (measureReal_mono ?_) (hMN n hn l hl)
  intro p hp
  refine ⟨hp.1, ?_⟩
  by_contra hbad
  have hratio : ∀ k ≤ ⌊T * n⌋₊, (k : ℝ) / infectious (p.eval k) ≤ M := by
    intro k hk
    exact le_of_not_gt (fun h ↦ hbad ⟨k, hk, h⟩)
  have h := reciprocalSquare_tail_le_of_ratio (fun k ↦ infectious (p.eval k))
    K ⌊T * n⌋₊ hratio
  exact not_lt_of_ge h (hK.trans hp.2)

end HeightPaper.Model
