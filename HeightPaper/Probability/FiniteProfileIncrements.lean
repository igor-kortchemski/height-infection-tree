module

public import HeightPaper.Probability.FiniteComplexNormalizer
public import HeightPaper.Probability.FiniteProfileMoment
public import HeightPaper.Model.ComplexProfileMoments
public import HeightPaper.Analysis.ComplexMomentExponent

/-! # Uniform finite-epidemic profile increments and moment tails -/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal BigOperators Topology Classical

namespace HeightPaper.CountCoupling

open Model

noncomputable def finiteProfileIncrementBound (l : ℝ) (n H : ℕ) (u : ℕ → ℝ)
    (k : ℕ) (z : ℂ) (p : ℝ) : ℝ :=
  prescribedShiftedMomentBound (Complex.exp z) (finiteBirth l n u) (initial n)
    (finiteSafeCutoff l n H u) p k

/-- Both profiles are evaluated on one actual prescribed-word history. The
normalizer cutoff is always the source cutoff at the full epidemic horizon. -/
noncomputable def finiteProfileDifferenceMoment (l : ℝ) (n H : ℕ) (u : ℕ → ℝ)
    (j k : ℕ) (z : ℂ) (p : ℝ) : ℝ :=
  ∫ q, ‖normalizedActiveWeight (Complex.exp z) q.last /
      finiteComplexNormalizer l n H u k z -
    normalizedActiveWeight (Complex.exp z) (q.eval j) /
      finiteComplexNormalizer l n H u j z‖ ^ p
    ∂kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k

theorem finiteProfileDifferenceMoment_le_sum {l : ℝ} {n H : ℕ} {u : ℕ → ℝ}
    (hs : ∀ i ≤ H, 0 < finiteWalk l n u i) {j k : ℕ}
    (hJj : finiteSafeCutoff l n H u ≤ j) (hjk : j ≤ k) (hk : k ≤ H)
    {z : ℂ} (hz : z.re ≤ 2 * profileRoot l) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    finiteProfileDifferenceMoment l n H u j k z p ≤
      (4 * (2 : ℝ) ^ p) * ∑ i ∈ Finset.Ico j k, finiteProfileIncrementBound l n H u i z p := by
  exact prescribedPath_complex_moment_sub_le _ _ _ _ _ _ hJj hjk hp hp2
    (fun i hi ↦ prescribedWalk_finite_pos hs (hi.trans hk))
    (finiteComplexNormalizer_ne_zero hs hk hz)

/-- The explicit increment envelope has the summable exponent at time `k+1`.
The source's real numerator is increased by one step, avoiding an unnecessary
comparison between consecutive complex normalizers. -/
theorem finiteProfileIncrementBound_le_exp {l M A : ℝ} (hl : 1 < l) (hM : 0 ≤ M)
    (n H K : ℕ) (u : ℕ → ℝ)
    (hs : ∀ i ≤ H, 0 < finiteWalk l n u i)
    (hJ : finiteSafeCutoff l n H u ≤ K)
    (hratio : ∀ i ≤ H, (i : ℝ) / (finiteWalk l n u i : ℝ) ≤ M)
    {k : ℕ} (hJk : finiteSafeCutoff l n H u ≤ k) (hk : k < H)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz : z.re ≤ 2 * profileRoot l)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (herr : |finiteNormalizerMomentLogError l n H u (k + 1) z p| ≤ A) :
    finiteProfileIncrementBound l n H u k z p ≤ Real.exp
      (complexProfileMomentExponent l z p * Real.log (k + 1 : ℕ) +
        (A + 4 * K + 4 + 2 * Real.log 2 + 2 * Real.log (M + 1))) := by
  let events := finiteBirth l n u
  let J := finiteSafeCutoff l n H u
  let v := Real.exp (p * z.re)
  let c := ‖finiteComplexNormalizer l n H u (k + 1) z‖
  let s : ℝ := finiteWalk l n u (k + 1)
  let t : ℝ := (k + 1 : ℕ)
  let a := realNormalizerFrom v events 1 J (k + 1)
  let b := realNormalizer v events 1 (k + 1)
  let b₀ := realNormalizer v events 1 J
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hz2 : z.re ≤ 2 := hz.trans (by linarith [profileRoot_lt_one hl])
  have hpr : 0 ≤ p * z.re := mul_nonneg hp0 hz0
  have hpr4 : p * z.re ≤ 4 := by nlinarith
  have hv : 1 ≤ v := Real.one_le_exp_iff.mpr hpr
  have hw : 1 ≤ ‖Complex.exp z‖ := by
    rw [Complex.norm_exp]
    exact Real.one_le_exp_iff.mpr hz0
  have hvEq : ‖Complex.exp z‖ ^ p = v := by
    rw [Complex.norm_exp, ← Real.exp_mul]
    exact congrArg Real.exp (mul_comm _ _)
  have ht : 0 < t := by dsimp [t]; positivity
  have hs0 : 0 < s := by
    change (0 : ℝ) < (finiteWalk l n u (k + 1) : ℝ)
    exact_mod_cast hs (k + 1) (by omega)
  have hc : 0 < c := norm_pos_iff.mpr (finiteComplexNormalizer_ne_zero hs (by omega) hz)
  have ha : 0 < a := realNormalizerFrom_pos hv events 1 J (k + 1)
  have hb : 0 < b := zero_lt_one.trans_le (one_le_realNormalizer hv events 1 (k + 1))
  have hb₀ : 0 < b₀ := zero_lt_one.trans_le (one_le_realNormalizer hv events 1 J)
  have hraw := prescribedShiftedMomentBound_complex_le (Complex.exp z) hw hp0 events n J k hJk
    (prescribedWalk_finite_pos hs (by omega))
  rw [hvEq, prescribedWalk_finite_real hs (by omega)] at hraw
  have hupper : finiteProfileIncrementBound l n H u k z p ≤
      ((Real.exp z.re / (c * s)) ^ p * (2 : ℝ) ^ p) * b := by
    apply hraw.trans
    rw [Complex.norm_exp]
    exact mul_le_mul_of_nonneg_left (realNormalizer_mono hv events 1 (Nat.le_succ k)) (by positivity)
  have hprefix : Real.log b₀ ≤ 4 * K := by
    have hh := Real.log_le_log hb₀ (realNormalizer_le_pow hv events 1 J)
    rw [Real.log_pow, show Real.log v = p * z.re from Real.log_exp _] at hh
    have hJK : (J : ℝ) ≤ K := by exact_mod_cast hJ
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    nlinarith
  have hsplit : Real.log b = Real.log b₀ + Real.log a := by
    dsimp only [b, b₀, a]
    rw [realNormalizer_split v events 1 (show J ≤ k + 1 by omega), Real.log_mul hb₀.ne' ha.ne']
  have hlogratio : Real.log a - p * Real.log c ≤
      l / (l - 1) * (v - 1 - p * ((Complex.exp z).re - 1)) * Real.log t + A := by
    change |Real.log (a / c ^ p) -
      l / (l - 1) * (v - 1 - p * ((Complex.exp z).re - 1)) * Real.log t| ≤ A at herr
    rw [Real.log_div ha.ne' (Real.rpow_pos_of_pos hc p).ne', Real.log_rpow hc p] at herr
    linarith [(abs_le.mp herr).2]
  have hM1 : 0 < M + 1 := by linarith
  have hts : t ≤ (M + 1) * s := by
    have hh := (div_le_iff₀ hs0).mp (hratio (k + 1) (by omega))
    change t ≤ M * s at hh
    nlinarith
  have hlogt := Real.log_le_log ht hts
  rw [Real.log_mul hM1.ne' hs0.ne'] at hlogt
  have hlogM : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcountlog := mul_le_mul_of_nonneg_left hlogt hp0
  have hpM := mul_le_mul_of_nonneg_right hp2 hlogM
  have hpTwo := mul_le_mul_of_nonneg_right hp2 hlog2
  have hf : 0 < Real.exp z.re / (c * s) := div_pos (Real.exp_pos _) (mul_pos hc hs0)
  have hfP := Real.rpow_pos_of_pos hf p
  have htwoP := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) p
  apply hupper.trans
  rw [← Real.exp_log (mul_pos (mul_pos hfP htwoP) hb)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (mul_pos hfP htwoP).ne' hb.ne', Real.log_mul hfP.ne' htwoP.ne',
    Real.log_rpow hf p, Real.log_rpow (by norm_num : (0 : ℝ) < 2) p,
    Real.log_div (Real.exp_pos _).ne' (mul_pos hc hs0).ne',
    Real.log_mul hc.ne' hs0.ne', Real.log_exp, hsplit]
  change _ ≤ complexProfileMomentExponent l z p * Real.log t + _
  dsimp only [complexProfileMomentExponent, growthFactor]
  change Real.log a - p * Real.log c ≤
    l / (l - 1) * (Real.exp (p * z.re) - 1 - p * ((Complex.exp z).re - 1)) * Real.log t + A at hlogratio
  nlinarith only [hprefix, hlogratio, hcountlog, hpM, hpTwo, hpr4]

/-- Unconditional uniform exponential envelope for every increment bound.
The next count is used, so the terminal index is strictly below the horizon. -/
theorem finiteProfileIncrementBound_uniform_exp {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I, uniformLaw.real
      {u | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u i) ∧
        ∃ k < ⌊T * n⌋₊, finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ k ∧
          ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧ ∃ p ∈ Icc (1 : ℝ) 2,
            Real.exp (complexProfileMomentExponent l z p * Real.log (k + 1 : ℕ) + R) <
              finiteProfileIncrementBound l n ⌊T * n⌋₊ u k z p} < ε := by
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨A, hA, NA, hnormal⟩ := finiteNormalizer_errors_uniform_tight hI hT hparams hδ
  obtain ⟨M, NM, hratio⟩ := coupled_count_ratio_uniform_tight hI hT hparams hδ
  obtain ⟨K, NK, hcutoff⟩ := finiteSafeCutoff_survival_uniform_tight hI hT hparams hδ
  let R := A + 4 * K + 4 + 2 * Real.log 2 + 2 * Real.log ((M : ℝ) + 1)
  have hR : 0 ≤ R := by
    have h₂ := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have hM := Real.log_nonneg (show (1 : ℝ) ≤ (M : ℝ) + 1 by
      have hh : (0 : ℝ) ≤ M := Nat.cast_nonneg _
      linarith)
    dsimp only [R]
    positivity
  refine ⟨R, hR, max NA (max NM NK), ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let E₁ := finiteNormalizerErrorTail A l n H
  let E₂ := coupledCountRatioTail M l n H
  let E₃ : Set (ℕ → ℝ) := {u | K <
    (if ∀ j ≤ H, 0 < finiteWalk l n u j then finiteSafeCutoff l n H u else 0)}
  have hsub : {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
      ∃ k < H, finiteSafeCutoff l n H u ≤ k ∧
        ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧ ∃ p ∈ Icc (1 : ℝ) 2,
          Real.exp (complexProfileMomentExponent l z p * Real.log (k + 1 : ℕ) + R) <
            finiteProfileIncrementBound l n H u k z p} ⊆ (E₁ ∪ E₂) ∪ E₃ := by
    rintro u ⟨hs, k, hk, hJk, z, hz0, hz, p, hp, hbad⟩
    by_contra hnot
    have h₁ : u ∉ E₁ := fun h ↦ hnot (Or.inl (Or.inl h))
    have h₂ : u ∉ E₂ := fun h ↦ hnot (Or.inl (Or.inr h))
    have h₃ : u ∉ E₃ := fun h ↦ hnot (Or.inr h)
    have herror : |finiteNormalizerMomentLogError l n H u (k + 1) z p| ≤ A := by
      apply le_of_not_gt
      intro h
      exact h₁ ⟨hs, k + 1, by omega, by omega, Or.inr
        ⟨z, hz0, hz, p, ⟨zero_le_one.trans hp.1, hp.2⟩, h⟩⟩
    have hr : ∀ j ≤ H, (j : ℝ) / (finiteWalk l n u j : ℝ) ≤ M :=
      fun j hj ↦ le_of_not_gt (fun h ↦ h₂ ⟨hs, j, hj, h⟩)
    have hJ : finiteSafeCutoff l n H u ≤ K := by
      apply le_of_not_gt
      intro h
      apply h₃
      simpa only [E₃, mem_ofPred_eq, ite_eq_left hs] using h
    exact not_lt_of_ge (finiteProfileIncrementBound_le_exp (hparams l hl).1 (Nat.cast_nonneg M)
      n H K u hs hJ hr hJk hk hz0 hz hp.1 hp.2 herror) hbad
  have h₁ : uniformLaw.real E₁ < ε / 4 := hnormal n (by omega) l hl
  have h₂ : uniformLaw.real E₂ < ε / 4 := hratio n (by omega) l hl
  have h₃ : uniformLaw.real E₃ < ε / 4 := hcutoff n (by omega) l hl
  have hprob := measureReal_mono (μ := uniformLaw) hsub
  have h12 := measureReal_union_le (μ := uniformLaw) E₁ E₂
  have h123 := measureReal_union_le (μ := uniformLaw) (E₁ ∪ E₂) E₃
  change uniformLaw.real {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
    ∃ k < H, finiteSafeCutoff l n H u ≤ k ∧
      ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧ ∃ p ∈ Icc (1 : ℝ) 2,
        Real.exp (complexProfileMomentExponent l z p * Real.log (k + 1 : ℕ) + R) <
          finiteProfileIncrementBound l n H u k z p} < ε
  linarith

/-- Summing the controlled increments gives an explicit power tail on the
same tree history, uniformly in its terminal event time. -/
theorem finiteProfileDifferenceMoment_le_tail {l R η : ℝ} (hη : 0 < η)
    {n H : ℕ} {u : ℕ → ℝ} (hs : ∀ i ≤ H, 0 < finiteWalk l n u i)
    {j k : ℕ} (hJj : finiteSafeCutoff l n H u ≤ j) (hj : 1 ≤ j)
    (hjk : j ≤ k) (hk : k ≤ H) {z : ℂ} (hz : z.re ≤ 2 * profileRoot l)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hmargin : complexProfileMomentExponent l z p ≤ -1 - η)
    (hbound : ∀ i ∈ Finset.Ico j k, finiteProfileIncrementBound l n H u i z p ≤
      Real.exp (complexProfileMomentExponent l z p * Real.log (i + 1 : ℕ) + R)) :
    finiteProfileDifferenceMoment l n H u j k z p ≤
      16 * Real.exp R * ((j : ℝ) ^ (-η) / η) := by
  have hsum : (∑ i ∈ Finset.Ico j k, finiteProfileIncrementBound l n H u i z p) ≤
      Real.exp R * ((j : ℝ) ^ (-η) / η) := by
    calc
      _ ≤ ∑ i ∈ Finset.Ico j k,
          Real.exp (complexProfileMomentExponent l z p * Real.log (i + 1 : ℕ) + R) :=
        Finset.sum_le_sum hbound
      _ = Real.exp R * ∑ i ∈ Finset.Ico j k,
          ((i + 1 : ℕ) : ℝ) ^ complexProfileMomentExponent l z p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Real.exp_add, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (i + 1 : ℕ))]
        rw [mul_comm (complexProfileMomentExponent l z p) (Real.log (i + 1 : ℕ))]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_complex_profile_moment_le hη hmargin hj hjk)
        (Real.exp_pos R).le
  have hpref : 4 * (2 : ℝ) ^ p ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp2
    rw [Real.rpow_two] at hh
    linarith
  have hb := (finiteProfileDifferenceMoment_le_sum hs hJj hjk hk hz hp hp2).trans
    (mul_le_mul_of_nonneg_left hsum (by positivity))
  have htail0 : 0 ≤ Real.exp R * ((j : ℝ) ^ (-η) / η) := by positivity
  calc
    _ ≤ (4 * (2 : ℝ) ^ p) * (Real.exp R * ((j : ℝ) ^ (-η) / η)) := hb
    _ ≤ 16 * (Real.exp R * ((j : ℝ) ^ (-η) / η)) :=
      mul_le_mul_of_nonneg_right hpref htail0
    _ = _ := by ring

/-- The random tail constant is uniformly tight. All starting/terminal times,
tilts, and admissible moment orders occur inside the probability. -/
theorem finiteProfileDifferenceMoment_uniform_tail {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {η : ℝ} (hη : 0 < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I, uniformLaw.real
      {u | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u i) ∧
        ∃ j k : ℕ, 1 ≤ j ∧ j ≤ k ∧ k ≤ ⌊T * n⌋₊ ∧
          finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ j ∧
          ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧ ∃ p ∈ Ioc (1 : ℝ) 2,
            complexProfileMomentExponent l z p ≤ -1 - η ∧
            16 * Real.exp R * ((j : ℝ) ^ (-η) / η) <
              finiteProfileDifferenceMoment l n ⌊T * n⌋₊ u j k z p} < ε := by
  obtain ⟨R, hR, N, hN⟩ := finiteProfileIncrementBound_uniform_exp hI hT hparams hε
  refine ⟨R, hR, N, fun n hn l hl ↦ ?_⟩
  apply lt_of_le_of_lt (measureReal_mono (μ := uniformLaw) ?_) (hN n hn l hl)
  rintro u ⟨hs, j, k, hj, hjk, hk, hJ, z, hz0, hz, p, hp, hmargin, hlarge⟩
  by_contra hnot
  have hbound : ∀ i ∈ Finset.Ico j k, finiteProfileIncrementBound l n ⌊T * n⌋₊ u i z p ≤
      Real.exp (complexProfileMomentExponent l z p * Real.log (i + 1 : ℕ) + R) := by
    intro i hi
    apply le_of_not_gt
    intro h
    have hi' := Finset.mem_Ico.mp hi
    exact hnot ⟨hs, i, hi'.2.trans_le hk, hJ.trans hi'.1, z, hz0, hz, p, ⟨hp.1.le, hp.2⟩, h⟩
  exact not_lt_of_ge (finiteProfileDifferenceMoment_le_tail hη hs hJ hj hjk hk hz hp.1 hp.2
    hmargin hbound) hlarge

/-- The source shrinking-tilt corollary, with a single moment order chosen
before the probability tolerances, population, tilt, and epidemic parameter. -/
theorem finiteProfileDifferenceMoment_shrinking_tilts {I : Set ℝ≥0} (hI : IsCompact I)
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hxroot : ∀ l ∈ I, x < profileRoot l)
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n ≥ 1, A n ≤ ⌊T * n⌋₊)
    (K : ℕ → Set ℂ) (hK : ∀ n ≥ 1, IsCompact (K n))
    (hxK : ∀ n ≥ 1, (x : ℂ) ∈ K n)
    (hKE : ∀ n ≥ 1, ∀ l ∈ I, ∀ z ∈ K n, z.re < profileRoot l)
    (hdiam : Tendsto (fun n ↦ Metric.diam (K n)) atTop (𝓝 0)) :
    ∃ p ∈ Ioo (1 : ℝ) 2, ∀ a > 0, ∀ ε > 0, ∃ N : ℕ,
      ∀ n ≥ N, ∀ l ∈ I, uniformLaw.real
        {u | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u i) ∧
          finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ A n ∧
          ∃ z ∈ K n, a < finiteProfileDifferenceMoment l n ⌊T * n⌋₊ u (A n) ⌊T * n⌋₊ z p} < ε := by
  by_cases hne : I.Nonempty
  swap
  · refine ⟨3 / 2, ⟨by norm_num, by norm_num⟩, fun a ha ε hε ↦ ⟨0, ?_⟩⟩
    intro n hn l hl
    exact False.elim (hne ⟨l, hl⟩)
  obtain ⟨l₀, hl₀, hmin⟩ := hI.exists_isLeast hne
  obtain ⟨p, hp, η, hη, r, hr, hmargin⟩ := exists_uniform_complex_profile_moment_decay
    (hparams l₀ hl₀).1 hx.le (hxroot l₀ hl₀)
  refine ⟨p, hp, ?_⟩
  intro a ha ε hε
  obtain ⟨R, _hR, N₀, hN₀⟩ := finiteProfileDifferenceMoment_uniform_tail hI hT hparams hη hε
  have hrad : 0 < min r (x / 2) := lt_min hr (by positivity)
  obtain ⟨ND, hND⟩ := eventually_atTop.mp (hdiam.eventually (Iio_mem_nhds hrad))
  obtain ⟨NJ, hNJ⟩ := eventually_atTop.mp (hA.eventually (eventually_ge_atTop 1))
  have htail : Tendsto (fun n ↦ 16 * Real.exp R * (((A n : ℕ) : ℝ) ^ (-η) / η)) atTop (𝓝 0) := by
    have hh := ((tendsto_rpow_neg_atTop hη).comp
      (tendsto_natCast_atTop_atTop.comp hA)).div_const η |>.const_mul (16 * Real.exp R)
    simpa only [zero_div, mul_zero, Function.comp_def] using hh
  obtain ⟨NT, hNT⟩ := eventually_atTop.mp (htail.eventually (Iio_mem_nhds ha))
  refine ⟨max 1 (max N₀ (max ND (max NJ NT))), ?_⟩
  intro n hn l hl
  have hn1 : 1 ≤ n := by omega
  apply lt_of_le_of_lt (measureReal_mono (μ := uniformLaw) ?_) (hN₀ n (by omega) l hl)
  rintro u ⟨hs, hJ, z, hz, hlarge⟩
  have hdist : dist z (x : ℂ) < min r (x / 2) :=
    (Metric.dist_le_diam_of_mem (hK n hn1).isBounded hz (hxK n hn1)).trans_lt (hND n (by omega))
  have habs : |z.re - x| < x / 2 := by
    have hh := Complex.abs_re_le_norm (z - (x : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at hh
    exact hh.trans_lt (by simpa only [dist_eq_norm] using hdist.trans_le (min_le_right _ _))
  have hz0 : 0 ≤ z.re := by have hh := (abs_lt.mp habs).1; linarith
  have hzupper : z.re ≤ 2 * profileRoot l := by
    have hh := hKE n hn1 l hl z hz
    have hhpos := profileRoot_pos (hparams l hl).1
    linarith
  have hlmin : (l₀ : ℝ) ≤ l := by exact_mod_cast hmin hl
  have hm := hmargin l hlmin z (hdist.trans_le (min_le_left _ _))
  refine ⟨hs, A n, ⌊T * n⌋₊, hNJ n (by omega), hAH n hn1, le_rfl, hJ,
    z, hz0, hzupper, p, ⟨hp.1, hp.2.le⟩, hm, ?_⟩
  exact (hNT n (by omega)).trans hlarge

theorem one_le_finiteSafeCutoff_of_survival {l : ℝ} {n H : ℕ} {u : ℕ → ℝ}
    (hH : 1 ≤ H) (hs : ∀ i ≤ H, 0 < finiteWalk l n u i) :
    1 ≤ finiteSafeCutoff l n H u := by
  have hwalk : finiteWalk l n u 1 = 2 := by
    have hh := finiteWalk_succ l n u 0
    have hp := hs 1 hH
    simp only [finiteWalk_zero] at hh
    cases he : finiteBirth l n u 0 with
    | false =>
        have hz : finiteWalk l n u 1 = 0 := by simpa [he] using hh
        rw [hz] at hp
        contradiction
    | true => simpa [he] using hh
  apply le_csSup ⟨H, fun _ hi ↦ hi.1⟩
  refine ⟨hH, ?_⟩
  apply (sourceUnsafe_iff l _).mpr
  rw [hwalk]
  constructor
  · norm_num
  · unfold sourceSafeThreshold
    have hh := Real.exp_pos (2 * profileRoot l)
    norm_num
    linarith

private theorem complexProfileMomentExponent_uniform_upper {l₀ l : ℝ}
    (hl₀ : 1 < l₀) (hll : l₀ ≤ l) {z : ℂ} (hz0 : 0 ≤ z.re) (hz2 : z.re ≤ 2)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    complexProfileMomentExponent l z p ≤
      growthFactor l₀ * (Real.exp 4 + 1 + 2 * (Real.exp 2 + 1)) := by
  have hp0 := zero_le_one.trans hp
  have hexp := Real.exp_le_exp.mpr (show p * z.re ≤ 4 by nlinarith)
  have hre : |(Complex.exp z).re - 1| ≤ Real.exp 2 + 1 := by
    simpa only [Complex.sub_re, Complex.one_re] using
      (Complex.abs_re_le_norm (Complex.exp z - 1)).trans (norm_exp_sub_one_le_of_re_le hz2)
  have hneg := mul_le_mul_of_nonneg_left (neg_le_abs ((Complex.exp z).re - 1)) hp0
  have hprod := mul_le_mul hp2 hre (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have hcoef : Real.exp (p * z.re) - 1 - p * ((Complex.exp z).re - 1) ≤
      Real.exp 4 + 1 + 2 * (Real.exp 2 + 1) := by nlinarith
  apply (complexProfileMomentExponent_antitone_parameter hl₀ hll hp z).trans
  have hh := mul_le_mul_of_nonneg_left hcoef (growthFactor_pos hl₀).le
  unfold complexProfileMomentExponent
  linarith

private theorem increment_exp_succ_le {α B R : ℝ} (hB : 0 ≤ B) (hα : α ≤ B)
    {k : ℕ} (hk : 1 ≤ k) :
    16 * Real.exp (α * Real.log (k + 1 : ℕ) + R) ≤
      Real.exp (α * Real.log k + (R + Real.log 16 + B * Real.log 2)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsucc : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hlo : Real.log k ≤ Real.log (k + 1 : ℕ) :=
    Real.log_le_log hkR (by exact_mod_cast Nat.le_succ k)
  have hhi : Real.log (k + 1 : ℕ) ≤ Real.log 2 + Real.log k := by
    have hh : ((k + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      push_cast
      linarith
    have hh' := Real.log_le_log hsucc hh
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hkR.ne'] at hh'
  have hprod : α * (Real.log (k + 1 : ℕ) - Real.log k) ≤ B * Real.log 2 :=
    (mul_le_mul_of_nonneg_right hα (sub_nonneg.mpr hlo)).trans
      (mul_le_mul_of_nonneg_left (by linarith :
        Real.log (k + 1 : ℕ) - Real.log k ≤ Real.log 2) hB)
  calc
    _ = Real.exp (Real.log 16 + (α * Real.log (k + 1 : ℕ) + R)) := by
      simp only [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- Source Proposition 2063, with its necessary endpoint correction `k < H`.
The logarithm is exactly `log k`; surviving nonempty horizons have `Jⁿ ≥ 1`.
Time, tilt, and the source moment orders are jointly inside probability. -/
theorem finiteProfileIncrementMoment_uniform_exp {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I, uniformLaw.real
      {u | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u i) ∧
        ∃ k < ⌊T * n⌋₊, finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ k ∧
          ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧ ∃ p ∈ Ioc (1 : ℝ) 2,
            Real.exp (complexProfileMomentExponent l z p * Real.log k + R) <
              finiteProfileDifferenceMoment l n ⌊T * n⌋₊ u k (k + 1) z p} < ε := by
  by_cases hne : I.Nonempty
  swap
  · exact ⟨0, le_rfl, 0, fun n hn l hl ↦ False.elim (hne ⟨l, hl⟩)⟩
  obtain ⟨l₀, hl₀, hmin⟩ := hI.exists_isLeast hne
  obtain ⟨R, hR, N, hN⟩ := finiteProfileIncrementBound_uniform_exp hI hT hparams hε
  let B := growthFactor l₀ * (Real.exp 4 + 1 + 2 * (Real.exp 2 + 1))
  have hB : 0 ≤ B := mul_nonneg (growthFactor_pos (hparams l₀ hl₀).1).le (by positivity)
  have hlog16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨R + Real.log 16 + B * Real.log 2, by positivity, N, fun n hn l hl ↦ ?_⟩
  apply lt_of_le_of_lt (measureReal_mono (μ := uniformLaw) ?_) (hN n hn l hl)
  rintro u ⟨hs, k, hk, hJ, z, hz0, hz, p, hp, hlarge⟩
  by_contra hnot
  have henv : finiteProfileIncrementBound l n ⌊T * n⌋₊ u k z p ≤
      Real.exp (complexProfileMomentExponent l z p * Real.log (k + 1 : ℕ) + R) := by
    apply le_of_not_gt
    intro h
    exact hnot ⟨hs, k, hk, hJ, z, hz0, hz, p, ⟨hp.1.le, hp.2⟩, h⟩
  have hmoment : finiteProfileDifferenceMoment l n ⌊T * n⌋₊ u k (k + 1) z p ≤
      (4 * (2 : ℝ) ^ p) * finiteProfileIncrementBound l n ⌊T * n⌋₊ u k z p := by
    simpa only [Nat.Ico_succ_singleton, Finset.sum_singleton] using
      finiteProfileDifferenceMoment_le_sum hs hJ (Nat.le_succ k) (by omega) hz hp.1 hp.2
  have hpref : 4 * (2 : ℝ) ^ p ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp.2
    rw [Real.rpow_two] at hh
    linarith
  have hmoment' := hmoment.trans ((mul_le_mul_of_nonneg_left henv (by positivity)).trans
    (mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le))
  have hk1 : 1 ≤ k := (one_le_finiteSafeCutoff_of_survival (by omega) hs).trans hJ
  have hlmin : (l₀ : ℝ) ≤ l := by exact_mod_cast hmin hl
  have hz2 : z.re ≤ 2 := hz.trans (by linarith [profileRoot_lt_one (hparams l hl).1])
  have hα := complexProfileMomentExponent_uniform_upper (hparams l₀ hl₀).1 hlmin hz0 hz2 hp.1.le hp.2
  exact not_lt_of_ge (hmoment'.trans (increment_exp_succ_le hB hα hk1)) hlarge

/-- The full tree expectation, including both observations of one history,
depends only on the finite epidemic event prefix. -/
theorem finiteProfileDifferenceMoment_congr_birth_prefix {l : ℝ} {n H : ℕ}
    {u v : ℕ → ℝ} (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n v i)
    {j k : ℕ} (hj : j ≤ H) (hk : k ≤ H) (z : ℂ) (p : ℝ) :
    finiteProfileDifferenceMoment l n H u j k z p = finiteProfileDifferenceMoment l n H v j k z p := by
  have hlaw := kernelPathLaw_prescribed_congr_prefix (initial n)
    (H := k) (fun i hi ↦ he i (hi.trans_le hk))
  have hCj := (finiteNormalizer_congr_birth_prefix he hj z p).1
  have hCk := (finiteNormalizer_congr_birth_prefix he hk z p).1
  simp only [finiteProfileDifferenceMoment, kernelPathMeasure, hlaw, hCj, hCk]

theorem measurable_finiteProfileDifferenceMoment (l : ℝ) (n H j k : ℕ)
    (hj : j ≤ H) (hk : k ≤ H) (z : ℂ) (p : ℝ) :
    Measurable (fun u ↦ finiteProfileDifferenceMoment l n H u j k z p) :=
  measurable_of_finiteBirth_prefix l n H
    (fun _ _ he ↦ finiteProfileDifferenceMoment_congr_birth_prefix he hj hk z p)

/-- Arbitrary time/tilt/moment-order restrictions and thresholds give
measurable simultaneous exceedance events; no countability of the tilts is
required because the epidemic event prefix is finite. -/
theorem measurableSet_finiteProfileDifference_exceedance (l : ℝ) (n H : ℕ)
    (P : ℕ → ℕ → ℂ → ℝ → Prop) (a : ℕ → ℕ → ℂ → ℝ → ℝ) :
    MeasurableSet {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
      ∃ j ≤ H, ∃ k ≤ H, finiteSafeCutoff l n H u ≤ j ∧
        ∃ z : ℂ, ∃ p : ℝ, P j k z p ∧ a j k z p < finiteProfileDifferenceMoment l n H u j k z p} := by
  apply measurableSet_of_finiteBirth_prefix l n H
  intro u v he
  have hsurv : (∀ i ≤ H, 0 < finiteWalk l n u i) ↔ ∀ i ≤ H, 0 < finiteWalk l n v i := by
    constructor <;> intro hs i hi
    · rw [← finiteWalk_congr_birth_prefix he hi]
      exact hs i hi
    · rw [finiteWalk_congr_birth_prefix he hi]
      exact hs i hi
  simp only [mem_ofPred_eq, hsurv, finiteSafeCutoff_congr_birth_prefix he]
  apply and_congr_right
  intro _hs
  apply exists_congr
  intro j
  apply and_congr_right
  intro hj
  apply exists_congr
  intro k
  apply and_congr_right
  intro hk
  apply and_congr_right
  intro _hJ
  apply exists_congr
  intro z
  apply exists_congr
  intro p
  rw [finiteProfileDifferenceMoment_congr_birth_prefix he hj hk z p]

end HeightPaper.CountCoupling
