module

public import HeightPaper.Probability.ReciprocalRemainder
public import HeightPaper.Probability.EarlyCountUpper
public import HeightPaper.Probability.EarlyCountSlope

/-!
# Sharp early reciprocal-sum pinching

Two geometric count barriers bound the early reciprocal sum between harmonic
sums with reciprocal slopes. The estimates live on the full epidemic history
space and retain activity at its endpoint, so they combine with macroscopic
reciprocal estimates without changing probability spaces.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators

namespace HeightPaper.Model

/-- An early large-count event inside a longer epidemic history. -/
def earlyLargeActiveOnFull (c : ℝ) (K early horizon : ℕ) : Set (FinitePath horizon) :=
  ⋃ k ∈ Finset.Ico K (early + 1), {p | p.eval k ∈ largeActiveCount c k}

theorem pathMeasure_earlyLargeActiveOnFull_le (rate : ℝ≥0) (n early horizon K : ℕ)
    (hearly : early ≤ horizon) (c : ℝ) {R q : ℝ} (hR : 1 ≤ R) (hq : 1 ≤ q)
    (hc : geometricContraction R q < q ^ c) (hpressure : (rate : ℝ) * n ≤ R) :
    (pathMeasure rate n horizon).real (earlyLargeActiveOnFull c K early horizon) ≤
      q * (geometricContraction R q / q ^ c) ^ K /
        (1 - geometricContraction R q / q ^ c) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hδ : 0 ≤ geometricContraction R q / q ^ c :=
    div_nonneg (geometricContraction_pos (zero_le_one.trans hR) hq0).le (Real.rpow_pos_of_pos hq0 c).le
  have hδ1 : geometricContraction R q / q ^ c < 1 :=
    (div_lt_one (Real.rpow_pos_of_pos hq0 c)).mpr hc
  calc
    _ ≤ ∑ k ∈ Finset.Ico K (early + 1),
        (pathMeasure rate n horizon).real {p | p.eval k ∈ largeActiveCount c k} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.Ico K (early + 1), q * (geometricContraction R q / q ^ c) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkE : k ≤ early := by have := (Finset.mem_Ico.mp hk).2; omega
      rw [pathMeasure_event_at rate n horizon k (hkE.trans hearly)]
      exact evolve_largeActiveCount_le rate n k c hR hq hpressure
    _ = q * ∑ k ∈ Finset.Ico K (early + 1), (geometricContraction R q / q ^ c) ^ k := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (geom_sum_Ico_le_of_lt_one (m := K) (n := early + 1) hδ hδ1) hq0.le
      simpa only [mul_div_assoc] using hh

/-- Deterministic harmonic pinching outside the two early count deviations. -/
theorem early_reciprocal_pinch (lo hi : ℝ) (hlo : 0 < lo) (_hhi : 0 < hi)
    (K early horizon : ℕ) (p : FinitePath horizon)
    (hactive : ∀ k ∈ Finset.Ico (K + 1) early, 0 < infectious (p.eval k))
    (hsmall : p ∉ earlySmallActiveOnFull lo (K + 1) early horizon)
    (hlarge : p ∉ earlyLargeActiveOnFull hi (K + 1) early horizon) :
    (∑ k ∈ Finset.Ico (K + 1) early, 1 / (k : ℝ)) / hi ≤
        ∑ k ∈ Finset.Ico (K + 1) early, 1 / (infectious (p.eval k) : ℝ) ∧
      (∑ k ∈ Finset.Ico (K + 1) early, 1 / (infectious (p.eval k) : ℝ)) ≤
        (∑ k ∈ Finset.Ico (K + 1) early, 1 / (k : ℝ)) / lo := by
  have hpoint (k : ℕ) (hk : k ∈ Finset.Ico (K + 1) early) :
      (1 / (k : ℝ)) / hi ≤ 1 / (infectious (p.eval k) : ℝ) ∧
        1 / (infectious (p.eval k) : ℝ) ≤ (1 / (k : ℝ)) / lo := by
    have hk0 : 0 < k := by have := (Finset.mem_Ico.mp hk).1; omega
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
    have hI : 0 < (infectious (p.eval k) : ℝ) := by exact_mod_cast hactive k hk
    have hinterval : k ∈ Finset.Ico (K + 1) (early + 1) :=
      Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hk).1, by have := (Finset.mem_Ico.mp hk).2; omega⟩
    have hlow : lo * k < (infectious (p.eval k) : ℝ) := by
      apply lt_of_not_ge
      intro he
      apply hsmall
      exact mem_iUnion₂.mpr ⟨k, hinterval, ⟨hactive k hk, he⟩⟩
    have hupp : (infectious (p.eval k) : ℝ) < hi * k := by
      apply lt_of_not_ge
      intro he
      apply hlarge
      exact mem_iUnion₂.mpr ⟨k, hinterval, he⟩
    constructor
    · have heq : (1 / (k : ℝ)) / hi = 1 / (hi * k) := by ring
      rw [heq]
      exact one_div_le_one_div_of_le hI hupp.le
    · have heq : (1 / (k : ℝ)) / lo = 1 / (lo * k) := by ring
      rw [heq]
      exact one_div_le_one_div_of_le (mul_pos hlo hkR) hlow.le
  constructor
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun k hk ↦ (hpoint k hk).1)
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun k hk ↦ (hpoint k hk).2)

/-- The finite early reciprocal sum lies between the two harmonic barriers
except on explicitly controlled geometric events, on surviving full histories. -/
theorem path_early_reciprocal_pinch_le (rate : ℝ≥0) (n early horizon K : ℕ)
    (hearly : early ≤ horizon) (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    {Rlo Rhi qlo qhi : ℝ} (hRlo : 0 ≤ Rlo) (hRhi : 1 ≤ Rhi)
    (hqlo : 0 < qlo) (hqlo1 : qlo ≤ 1) (hqhi : 1 ≤ qhi)
    (hcLo : geometricContraction Rlo qlo < qlo ^ lo)
    (hcHi : geometricContraction Rhi qhi < qhi ^ hi)
    (hpressureLo : Rlo ≤ (rate : ℝ) * (n - early : ℕ))
    (hpressureHi : (rate : ℝ) * n ≤ Rhi) :
    (pathMeasure rate n horizon).real
      {p | (p.eval horizon).active.Nonempty ∧
        ((∑ k ∈ Finset.Ico (K + 1) early, 1 / (infectious (p.eval k) : ℝ)) <
            (∑ k ∈ Finset.Ico (K + 1) early, 1 / (k : ℝ)) / hi ∨
          (∑ k ∈ Finset.Ico (K + 1) early, 1 / (k : ℝ)) / lo <
            ∑ k ∈ Finset.Ico (K + 1) early, 1 / (infectious (p.eval k) : ℝ))} ≤
      qlo * (geometricContraction Rlo qlo / qlo ^ lo) ^ (K + 1) /
          (1 - geometricContraction Rlo qlo / qlo ^ lo) +
        qhi * (geometricContraction Rhi qhi / qhi ^ hi) ^ (K + 1) /
          (1 - geometricContraction Rhi qhi / qhi ^ hi) := by
  let A : Set (FinitePath horizon) := {p | (p.eval horizon).active.Nonempty ∧
    ((∑ k ∈ Finset.Ico (K + 1) early, 1 / (infectious (p.eval k) : ℝ)) <
        (∑ k ∈ Finset.Ico (K + 1) early, 1 / (k : ℝ)) / hi ∨
      (∑ k ∈ Finset.Ico (K + 1) early, 1 / (k : ℝ)) / lo <
        ∑ k ∈ Finset.Ico (K + 1) early, 1 / (infectious (p.eval k) : ℝ))}
  have hrestrict : (pathMeasure rate n horizon).real A =
      (pathMeasure rate n horizon).real {p | p ∈ A ∧ SupportedPath rate n horizon p.eval} := by
    apply measureReal_congr
    filter_upwards [ae_supportedPath rate n horizon] with p hp
    exact propext (by simp only [hp, and_true])
  change (pathMeasure rate n horizon).real A ≤ _
  rw [hrestrict]
  have hsubset : {p | p ∈ A ∧ SupportedPath rate n horizon p.eval} ⊆
      earlySmallActiveOnFull lo (K + 1) early horizon ∪
        earlyLargeActiveOnFull hi (K + 1) early horizon := by
    intro p hp
    by_contra hn
    have hsmall : p ∉ earlySmallActiveOnFull lo (K + 1) early horizon := fun h ↦ hn (Or.inl h)
    have hlarge : p ∉ earlyLargeActiveOnFull hi (K + 1) early horizon := fun h ↦ hn (Or.inr h)
    have hactive (k : ℕ) (hk : k ∈ Finset.Ico (K + 1) early) : 0 < infectious (p.eval k) := by
      apply Nat.pos_of_ne_zero
      intro hz
      have hkH : k ≤ horizon := (Finset.mem_Ico.mp hk).2.le.trans hearly
      have he := hp.2.infectious_eq_zero_later hkH le_rfl hz
      exact (Nat.ne_of_gt hp.1.1.card_pos) he
    have hh := early_reciprocal_pinch lo hi hlo hhi K early horizon p hactive hsmall hlarge
    exact hp.1.2.elim (not_lt_of_ge hh.1) (not_lt_of_ge hh.2)
  apply (measureReal_mono hsubset).trans
  apply (measureReal_union_le _ _).trans
  exact add_le_add
    (pathMeasure_earlySmallActiveOnFull_le rate n early horizon (K + 1) hearly lo
      hRlo hqlo hqlo1 hcLo hpressureLo)
    (pathMeasure_earlyLargeActiveOnFull_le rate n early horizon (K + 1) hearly hi
      hRhi hqhi hcHi hpressureHi)

end HeightPaper.Model
