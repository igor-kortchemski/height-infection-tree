module

public import HeightPaper.Probability.EarlyReciprocal
public import HeightPaper.Model.ObservedEvents

/-!
# Good observed words for profile normalization

Sharp early count bounds and a macroscopic lower count bound hold together
outside a geometric initial-tail error and an error tending to zero. A fixed
initial cutoff is chosen before the population limit; constants depending on
that cutoff therefore remain fixed throughout the limit.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HeightPaper.Model

/-- Count conditions needed for uniform polynomial normalizer estimates.
The late reciprocal bound controls the extension beyond the early interval. -/
def GoodCountWord (lo hi c L : ℝ) (K E N : ℕ) (events : ℕ → Bool) : Prop :=
  (∀ k, K ≤ k → k ≤ E → lo * k ≤ (prescribedWalk events 1 k : ℝ) ∧
    (prescribedWalk events 1 k : ℝ) ≤ hi * k) ∧
  (∀ k, K ≤ k → k ≤ N → c * k ≤ (prescribedWalk events 1 k : ℝ)) ∧
  (∑ k ∈ Finset.Ico E N, 1 / (prescribedWalk events 1 k : ℝ)) ≤ L

private theorem exists_sharp_count_pressures {l lo hi : ℝ} (hl : 1 < l)
    (hlo : lo < (l - 1) / (l + 1)) (hhi : (l - 1) / (l + 1) < hi) :
    ∃ Rlo Rhi qlo qhi : ℝ, 0 ≤ Rlo ∧ Rlo < l ∧ 1 ≤ Rhi ∧ l < Rhi ∧
      0 < qlo ∧ qlo ≤ 1 ∧ 1 ≤ qhi ∧
      geometricContraction Rlo qlo < qlo ^ lo ∧ geometricContraction Rhi qhi < qhi ^ hi := by
  have hcont : ContinuousAt (fun R : ℝ ↦ (R - 1) / (R + 1)) l :=
    (continuousAt_id.sub continuousAt_const).div (continuousAt_id.add continuousAt_const) (by linarith)
  have helo : ∀ᶠ R : ℝ in 𝓝[<] l, 1 < R ∧ R < l ∧ lo < (R - 1) / (R + 1) := by
    filter_upwards [self_mem_nhdsWithin,
      (hcont.tendsto.eventually (Ioi_mem_nhds hlo)).filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds hl).filter_mono nhdsWithin_le_nhds] with R hRl hs hR
    exact ⟨hR, hRl, hs⟩
  obtain ⟨Rlo, hRlo1, hRloL, hSlopeLo⟩ := helo.exists
  have hehi : ∀ᶠ R : ℝ in 𝓝[>] l, l < R ∧ (R - 1) / (R + 1) < hi := by
    filter_upwards [self_mem_nhdsWithin,
      (hcont.tendsto.eventually (Iio_mem_nhds hhi)).filter_mono nhdsWithin_le_nhds] with R hRl hs
    exact ⟨hRl, hs⟩
  obtain ⟨Rhi, hRhiL, hSlopeHi⟩ := hehi.exists
  have hRlo0 : 0 ≤ Rlo := (zero_lt_one.trans hRlo1).le
  have hRhi1 : 1 ≤ Rhi := (hl.trans hRhiL).le
  obtain ⟨qlo, hqlo, hqlo1, hcLo⟩ := exists_lower_count_parameter hRlo0 hSlopeLo
  obtain ⟨qhi, hqhi, hcHi⟩ := exists_upper_count_parameter (zero_le_one.trans hRhi1) hSlopeHi
  exact ⟨Rlo, Rhi, qlo, qhi, hRlo0, hRloL, hRhi1, hRhiL, hqlo, hqlo1.le, hqhi.le, hcLo, hcHi⟩

/-- With any two early slopes straddling the limiting drift, one can fix an
early interval, a global linear lower count, and a late reciprocal bound.
Making the fixed initial cutoff large makes the actual good-word failure
probability arbitrarily small for all sufficiently large populations. -/
theorem exists_goodCountWord_probability_control
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T lo hi : ℝ}
    (hl : 1 < l) (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hlo : 0 < lo) (hloD : lo < (l - 1) / (l + 1)) (hhiD : (l - 1) / (l + 1) < hi)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    ∃ early : ℕ → ℕ, ∃ a c L : ℝ, 0 < a ∧ 0 < c ∧ 0 < L ∧
      ∀ ζ > (0 : ℝ), ∃ K : ℕ, 1 ≤ K ∧ ∀ᶠ n in atTop,
        K ≤ early n ∧ early n ≤ horizon n ∧ a * (horizon n : ℝ) ≤ early n ∧
        (pathMeasure (rates n) n (horizon n)).real
          {p | p.last.active.Nonempty ∧
            ¬GoodCountWord lo hi c L K (early n) (horizon n) (observedBirth p.eval)} < ζ := by
  obtain ⟨Rlo, Rhi, qlo, qhi, hRlo, hRloL, hRhi, hRhiL, hqlo, hqlo1, hqhi, hcLo, hcHi⟩ :=
    exists_sharp_count_pressures hl hloD hhiD
  have hl0 : 0 < l := zero_lt_one.trans hl
  have hfrac : 0 < 1 - Rlo / l := sub_pos.mpr ((div_lt_one hl0).mpr hRloL)
  let A := min T (1 - Rlo / l) / 2
  have hA : 0 < A := half_pos (lt_min hT.1 hfrac)
  have hAT : A < T := by
    have hmin := min_le_left T (1 - Rlo / l)
    dsimp [A]
    linarith only [hmin, hT.1]
  have hAf : A < 1 - Rlo / l := by
    have hmin := min_le_right T (1 - Rlo / l)
    dsimp [A]
    linarith only [hmin, hfrac]
  have hA1 : A < 1 := by have := div_nonneg hRlo hl0.le; linarith only [this, hAf]
  have hPressure : Rlo < l * (1 - A) := by
    have heq : (Rlo / l) * l = Rlo := div_mul_cancel₀ _ hl0.ne'
    nlinarith [mul_lt_mul_of_pos_left hAf hl0]
  have hPLo := (tendsto_early_pressure rates hA.le hA1 hrates).eventually (Ioi_mem_nhds hPressure)
  have hPHi := hrates.eventually (Iio_mem_nhds hRhiL)
  obtain ⟨b, hb, hmacro⟩ := path_uniform_active_count_lower rates horizon hl hA hAT hT.2 hrates hhorizon
  let a := A / (2 * (T + 1))
  let c := min lo (b / (T + 1))
  let L := (T + 1) / b
  have hTp : 0 < T + 1 := by linarith [hT.1]
  have ha : 0 < a := div_pos hA (by positivity)
  have hc : 0 < c := lt_min hlo (div_pos hb hTp)
  have hL : 0 < L := div_pos hTp hb
  let ρlo := geometricContraction Rlo qlo / qlo ^ lo
  let ρhi := geometricContraction Rhi qhi / qhi ^ hi
  have hqhi0 : 0 < qhi := zero_lt_one.trans_le hqhi
  have hρlo : 0 ≤ ρlo := div_nonneg (geometricContraction_pos hRlo hqlo).le (Real.rpow_pos_of_pos hqlo lo).le
  have hρhi : 0 ≤ ρhi := div_nonneg (geometricContraction_pos (zero_le_one.trans hRhi) hqhi0).le
    (Real.rpow_pos_of_pos hqhi0 hi).le
  have hρlo1 : ρlo < 1 := (div_lt_one (Real.rpow_pos_of_pos hqlo lo)).mpr hcLo
  have hρhi1 : ρhi < 1 := (div_lt_one (Real.rpow_pos_of_pos hqhi0 hi)).mpr hcHi
  have hgeoLo := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρlo hρlo1).const_mul qlo).div_const (1 - ρlo)
  have hgeoHi := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρhi hρhi1).const_mul qhi).div_const (1 - ρhi)
  have hgeo := hgeoLo.add hgeoHi
  simp only [mul_zero, zero_div, add_zero] at hgeo
  refine ⟨fun n ↦ ⌊A * n⌋₊, a, c, L, ha, hc, hL, ?_⟩
  intro ζ hζ
  obtain ⟨K, hK1, hKgeo⟩ := ((eventually_ge_atTop 1).and
    (hgeo.eventually (Iio_mem_nhds (half_pos hζ)))).exists
  refine ⟨K, hK1, ?_⟩
  filter_upwards [hPLo, hPHi,
    (tendsto_floor_fraction hA.le).eventually_lt hhorizon hAT,
    (tendsto_floor_fraction hA.le).eventually (Ioi_mem_nhds (half_lt_self hA)),
    hhorizon.eventually (Iio_mem_nhds (show T < T + 1 by linarith)),
    (tendsto_nat_floor_mul_atTop A hA).eventually (eventually_ge_atTop K),
    hmacro.eventually (Iio_mem_nhds (half_pos hζ)), eventually_gt_atTop 0]
    with n hnLo hnHi htime hEfrac hNfrac hKE hnMacro hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hEN : ⌊A * n⌋₊ ≤ horizon n := by
    exact_mod_cast ((div_lt_div_iff_of_pos_right hnR).mp htime).le
  have hElo : A / 2 * n < (⌊A * n⌋₊ : ℝ) := (lt_div_iff₀ hnR).mp hEfrac
  have hNup : (horizon n : ℝ) < (T + 1) * n := (div_lt_iff₀ hnR).mp hNfrac
  have haN : a * (horizon n : ℝ) ≤ ⌊A * n⌋₊ := by
    have haeq : a * (T + 1) = A / 2 := by dsimp [a]; field_simp
    nlinarith [mul_lt_mul_of_pos_left hNup ha]
  refine ⟨hKE, hEN, haN, ?_⟩
  let badMacro : Set (FinitePath (horizon n)) := {p | (p.eval (horizon n)).active.Nonempty ∧
    ∃ k, ⌊A * n⌋₊ ≤ k ∧ k ≤ horizon n ∧ (infectious (p.eval k) : ℝ) < b * n}
  have hfail : (pathMeasure (rates n) n (horizon n)).real
        {p | p.last.active.Nonempty ∧
          ¬GoodCountWord lo hi c L K ⌊A * n⌋₊ (horizon n) (observedBirth p.eval)} ≤
      (pathMeasure (rates n) n (horizon n)).real (earlySmallActiveOnFull lo K ⌊A * n⌋₊ (horizon n)) +
      (pathMeasure (rates n) n (horizon n)).real (earlyLargeActiveOnFull hi K ⌊A * n⌋₊ (horizon n)) +
      (pathMeasure (rates n) n (horizon n)).real badMacro := by
    have hUnion := measureReal_union_le (μ := pathMeasure (rates n) n (horizon n))
      (earlySmallActiveOnFull lo K ⌊A * n⌋₊ (horizon n) ∪
        earlyLargeActiveOnFull hi K ⌊A * n⌋₊ (horizon n)) badMacro
    have hEarly := measureReal_union_le (μ := pathMeasure (rates n) n (horizon n))
      (earlySmallActiveOnFull lo K ⌊A * n⌋₊ (horizon n))
      (earlyLargeActiveOnFull hi K ⌊A * n⌋₊ (horizon n))
    apply le_trans (b := (pathMeasure (rates n) n (horizon n)).real
      ((earlySmallActiveOnFull lo K ⌊A * n⌋₊ (horizon n) ∪
        earlyLargeActiveOnFull hi K ⌊A * n⌋₊ (horizon n)) ∪ badMacro)) _
      (by linarith only [hUnion, hEarly])
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply PMF.toMeasure_mono _ (show MeasurableSet {p : FinitePath (horizon n) |
      p.last.active.Nonempty ∧ ¬GoodCountWord lo hi c L K ⌊A * n⌋₊ (horizon n) (observedBirth p.eval)} from trivial)
    intro p hp
    by_contra hnone
    have hsmall : p ∉ earlySmallActiveOnFull lo K ⌊A * n⌋₊ (horizon n) := fun h ↦ hnone (Or.inl (Or.inl h))
    have hlarge : p ∉ earlyLargeActiveOnFull hi K ⌊A * n⌋₊ (horizon n) := fun h ↦ hnone (Or.inl (Or.inr h))
    have hlate : p ∉ badMacro := fun h ↦ hnone (Or.inr h)
    have hpath := (mem_support_pathLaw_iff p).mp hp.2
    have hactive : (p.eval (horizon n)).active.Nonempty := by rw [FinitePath.eval_last]; exact hp.1.1
    have hearly (k : ℕ) (hkK : K ≤ k) (hkE : k ≤ ⌊A * n⌋₊) :
        lo * k ≤ (infectious (p.eval k) : ℝ) ∧ (infectious (p.eval k) : ℝ) ≤ hi * k := by
      have hkN := hkE.trans hEN
      have hk : k ∈ Finset.Ico K (⌊A * n⌋₊ + 1) := Finset.mem_Ico.mpr ⟨hkK, by omega⟩
      constructor
      · by_contra hlow
        apply hsmall
        exact mem_iUnion₂.mpr ⟨k, hk,
          ⟨(hpath.active_of_active_later hkN le_rfl hactive).card_pos, (lt_of_not_ge hlow).le⟩⟩
      · by_contra hhigh
        apply hlarge
        exact mem_iUnion₂.mpr ⟨k, hk, (lt_of_not_ge hhigh).le⟩
    have hmacroCount (k : ℕ) (hkE : ⌊A * n⌋₊ ≤ k) (hkN : k ≤ horizon n) :
        b * n ≤ (infectious (p.eval k) : ℝ) := by
      by_contra hlt
      exact hlate ⟨hactive, k, hkE, hkN, lt_of_not_ge hlt⟩
    apply hp.1.2
    refine ⟨?_, ?_, ?_⟩
    · intro k hkK hkE
      rw [hpath.observedWalk_eq hactive (hkE.trans hEN)]
      exact hearly k hkK hkE
    · intro k hkK hkN
      rw [hpath.observedWalk_eq hactive hkN]
      by_cases hkE : k ≤ ⌊A * n⌋₊
      · exact (mul_le_mul_of_nonneg_right (min_le_left lo (b / (T + 1))) (Nat.cast_nonneg k)).trans
          (hearly k hkK hkE).1
      · have hmc := hmacroCount k (by omega) hkN
        have hkR : (k : ℝ) ≤ horizon n := by exact_mod_cast hkN
        have hcu : c * (T + 1) ≤ b := by
          have hh := (mul_le_mul_of_nonneg_right (min_le_right lo (b / (T + 1))) hTp.le)
          rw [div_mul_cancel₀ _ hTp.ne'] at hh
          exact hh
        have hm1 := mul_le_mul_of_nonneg_left (hkR.trans hNup.le) hc.le
        have hm2 := mul_le_mul_of_nonneg_right hcu hnR.le
        nlinarith only [hm1, hm2, hmc]
    · have hsum := reciprocal_sum_le_of_count_lower p.eval hb hn0
        (fun k hk ↦ hmacroCount k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2.le)
      have hsumEq : (∑ k ∈ Finset.Ico ⌊A * n⌋₊ (horizon n),
          1 / (prescribedWalk (observedBirth p.eval) 1 k : ℝ)) =
        ∑ k ∈ Finset.Ico ⌊A * n⌋₊ (horizon n), 1 / (infectious (p.eval k) : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hpath.observedWalk_eq hactive (Finset.mem_Ico.mp hk).2.le]
      rw [hsumEq]
      have heq : (horizon n : ℝ) / (b * n) = ((horizon n : ℝ) / n) / b := by ring
      rw [heq] at hsum
      exact hsum.trans ((div_lt_div_iff_of_pos_right hb).mpr hNfrac).le
  have hlow := pathMeasure_earlySmallActiveOnFull_le (rates n) n ⌊A * n⌋₊ (horizon n) K hEN lo
    hRlo hqlo hqlo1 hcLo hnLo.le
  have hhigh := pathMeasure_earlyLargeActiveOnFull_le (rates n) n ⌊A * n⌋₊ (horizon n) K hEN hi
    hRhi hqhi hcHi hnHi.le
  change _ < ζ
  change (pathMeasure (rates n) n (horizon n)).real badMacro < ζ / 2 at hnMacro
  dsimp only [ρlo, ρhi] at hKgeo
  linarith only [hfail, hlow, hhigh, hKgeo, hnMacro]

end HeightPaper.Model
