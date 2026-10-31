module

public import HeightPaper.Probability.FiniteProfileIncrements
public import HeightPaper.Analysis.LogPowerSum
public import Mathlib.Analysis.MeanInequalities

/-! # General complex moment growth, including the critical logarithm -/

@[expose] public section

open MeasureTheory Set
open scoped NNReal BigOperators Classical

namespace HeightPaper.CountCoupling

open Model

theorem norm_rpow_le_sub_add (x y : ℂ) {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ‖x‖ ^ p ≤ 2 * (‖x - y‖ ^ p + ‖y‖ ^ p) := by
  have ht : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by simpa using norm_add_le (x - y) y
  have hc : (‖x - y‖ + ‖y‖) ^ p ≤ (2 : ℝ) ^ (p - 1) * (‖x - y‖ ^ p + ‖y‖ ^ p) := by
    simpa [Fin.sum_univ_succ] using
      Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ)
        (f := ![‖x - y‖, ‖y‖]) hp (fun i _ ↦ by fin_cases i <;> simp)
  have htwo : (2 : ℝ) ^ (p - 1) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ 2 by norm_num) (show p - 1 ≤ 1 by linarith)
  exact ((Real.rpow_le_rpow (norm_nonneg _) ht (by linarith)).trans hc).trans
    (mul_le_mul_of_nonneg_right htwo (by positivity))

/-- Split at the actual cutoff on one history before taking expectations. -/
theorem finiteProfileMoment_le_difference_add_prefix {l : ℝ} {n H : ℕ} {u : ℕ → ℝ}
    {k : ℕ} (hJk : finiteSafeCutoff l n H u ≤ k) (z : ℂ) {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    finiteProfileMoment (Complex.exp z) p l n H u k ≤
      2 * (finiteProfileDifferenceMoment l n H u (finiteSafeCutoff l n H u) k z p +
        finiteProfileMoment (Complex.exp z) p l n H u (finiteSafeCutoff l n H u)) := by
  let J := finiteSafeCutoff l n H u
  let K := fun i ↦ prescribedStep (finiteBirth l n u i)
  let A : FinitePath k → ℂ := fun q ↦ normalizedActiveWeight (Complex.exp z) q.last /
    finiteComplexNormalizer l n H u k z
  let B : FinitePath k → ℂ := fun q ↦ normalizedActiveWeight (Complex.exp z) (q.eval J) /
    finiteComplexNormalizer l n H u J z
  have hbase : (∫ q, ‖B q‖ ^ p ∂kernelPathMeasure K (initial n) k) =
      finiteProfileMoment (Complex.exp z) p l n H u J := by
    exact kernelPathMeasure_integral_prefixAt K (initial n) k J hJk
      (fun q ↦ ‖normalizedActiveWeight (Complex.exp z) q.last /
        finiteComplexNormalizer l n H u J z‖ ^ p)
  change (∫ q, ‖A q‖ ^ p ∂kernelPathMeasure K (initial n) k) ≤ _
  have hInt (f : FinitePath k → ℝ) : Integrable f (kernelPathMeasure K (initial n) k) :=
    integrable_kernelPathMeasure K (fun i s ↦ finite_support_prescribedStep _ s) (initial n) k f
  calc
    _ ≤ ∫ q, 2 * (‖A q - B q‖ ^ p + ‖B q‖ ^ p) ∂kernelPathMeasure K (initial n) k :=
      integral_mono (hInt _) (hInt _) (fun q ↦ norm_rpow_le_sub_add _ _ hp hp2)
    _ = _ := by
      rw [integral_const_mul, integral_add (hInt _) (hInt _), hbase]
      rfl

theorem finiteProfileMoment_at_cutoff_le {l : ℝ} (hl : 1 < l) {n H K : ℕ} {u : ℕ → ℝ}
    (hs : ∀ i ≤ H, 0 < finiteWalk l n u i) (hJ : finiteSafeCutoff l n H u ≤ K)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz : z.re ≤ 2 * profileRoot l)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    finiteProfileMoment (Complex.exp z) p l n H u (finiteSafeCutoff l n H u) ≤ Real.exp (4 * K) := by
  let J := finiteSafeCutoff l n H u
  have hw : 1 ≤ ‖Complex.exp z‖ := by
    rw [Complex.norm_exp]
    exact Real.one_le_exp_iff.mpr hz0
  have hb := finiteProfileMoment_le_prefix hw hp n H u hs
    (finiteSafeCutoff_le_horizon l n H u) le_rfl
  have hratio : finiteProfileMomentRatio (Complex.exp z) p l n H u J = 1 := by
    simp [finiteProfileMomentRatio, J, realNormalizerFrom, prescribedNormalizerFrom]
  change finiteProfileMoment (Complex.exp z) p l n H u J ≤ _
  change finiteProfileMoment (Complex.exp z) p l n H u J ≤
    finiteProfileMomentRatio (Complex.exp z) p l n H u J * (‖Complex.exp z‖ ^ p) ^ J at hb
  rw [hratio, one_mul, Complex.norm_exp, ← Real.exp_mul, ← Real.exp_nat_mul] at hb
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have hz2 : z.re ≤ 2 := hz.trans (by linarith [profileRoot_lt_one hl])
  have hpz : p * z.re ≤ 4 := by nlinarith
  have hJK : (J : ℝ) ≤ K := by exact_mod_cast hJ
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  nlinarith

noncomputable def profileGrowthScale (a : ℝ) (k : ℕ) : ℝ :=
  (1 + Real.log k) * Real.exp (max (a + 1) 0 * Real.log k)

theorem one_le_profileGrowthScale (a : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ profileGrowthScale a k := by
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  have he := Real.one_le_exp_iff.mpr (mul_nonneg (le_max_right (a + 1) 0) hlog)
  unfold profileGrowthScale
  nlinarith

/-- The explicit envelope has no denominator singularity at exponent `-1`. -/
theorem finiteProfileMoment_le_growth {l R : ℝ} (hl : 1 < l) {n H K : ℕ} {u : ℕ → ℝ}
    (hs : ∀ i ≤ H, 0 < finiteWalk l n u i) (hJ : finiteSafeCutoff l n H u ≤ K)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ H) (hJk : finiteSafeCutoff l n H u ≤ k)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz : z.re ≤ 2 * profileRoot l)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hbound : ∀ i ∈ Finset.Ico (finiteSafeCutoff l n H u) k,
      finiteProfileIncrementBound l n H u i z p ≤
        Real.exp (complexProfileMomentExponent l z p * Real.log (i + 1 : ℕ) + R)) :
    finiteProfileMoment (Complex.exp z) p l n H u k ≤
      (32 * Real.exp R + 2 * Real.exp (4 * K)) *
        profileGrowthScale (complexProfileMomentExponent l z p) k := by
  let G := profileGrowthScale (complexProfileMomentExponent l z p) k
  have hG : 1 ≤ G := one_le_profileGrowthScale _ hk1
  have hsum : (∑ i ∈ Finset.Ico (finiteSafeCutoff l n H u) k,
      finiteProfileIncrementBound l n H u i z p) ≤ Real.exp R * G := by
    apply (Finset.sum_le_sum hbound).trans
    simpa only [G, profileGrowthScale, mul_assoc] using
      sum_exp_log_Ico_le (complexProfileMomentExponent l z p) R (finiteSafeCutoff l n H u) k
  have hdiff := finiteProfileDifferenceMoment_le_sum hs le_rfl hJk hk hz hp hp2
  have htwo : 4 * (2 : ℝ) ^ p ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hp2
    rw [Real.rpow_two] at hh
    linarith
  have hd : finiteProfileDifferenceMoment l n H u (finiteSafeCutoff l n H u) k z p ≤
      16 * Real.exp R * G := by
    apply hdiff.trans
    calc
      _ ≤ (4 * (2 : ℝ) ^ p) * (Real.exp R * G) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 16 * (Real.exp R * G) := mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = _ := by ring
  have hprefix := finiteProfileMoment_at_cutoff_le hl hs hJ hz0 hz hp.le hp2
  have hdecomp := finiteProfileMoment_le_difference_add_prefix hJk z hp.le hp2
  have hprefG : Real.exp (4 * K) ≤ Real.exp (4 * K) * G := by nlinarith [Real.exp_pos (4 * K)]
  change _ ≤ (32 * Real.exp R + 2 * Real.exp (4 * K)) * G
  nlinarith

/-- In a strictly summable increment window, the conditional profile moment
has a bound independent of the observation time. -/
theorem finiteProfileMoment_le_of_strict_decay {l R η : ℝ}
    (hl : 1 < l) (hη : 0 < η)
    {n H K : ℕ} {u : ℕ → ℝ}
    (hs : ∀ i ≤ H, 0 < finiteWalk l n u i)
    (hJ : finiteSafeCutoff l n H u ≤ K)
    {k : ℕ} (hk : k ≤ H) (hJk : finiteSafeCutoff l n H u ≤ k)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz : z.re ≤ 2 * profileRoot l)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hdecay : complexProfileMomentExponent l z p ≤ -1 - η)
    (hbound : ∀ i ∈ Finset.Ico (finiteSafeCutoff l n H u) k,
      finiteProfileIncrementBound l n H u i z p ≤
        Real.exp (complexProfileMomentExponent l z p * Real.log (i + 1 : ℕ) + R)) :
    finiteProfileMoment (Complex.exp z) p l n H u k ≤
      32 * Real.exp R * (∑' i : ℕ, ((i + 1 : ℕ) : ℝ) ^ (-1 - η)) +
        2 * Real.exp (4 * K) := by
  let B : ℝ := Real.exp R * (∑' i : ℕ, ((i + 1 : ℕ) : ℝ) ^ (-1 - η))
  have hsum : (∑ i ∈ Finset.Ico (finiteSafeCutoff l n H u) k,
      finiteProfileIncrementBound l n H u i z p) ≤ B := by
    apply (Finset.sum_le_sum hbound).trans
    exact sum_exp_log_Ico_le_of_strict_decay hη hdecay R _ _
  have hB : 0 ≤ B :=
    (Finset.sum_nonneg (s := Finset.Ico (finiteSafeCutoff l n H u) k)
      (fun i _ => (Real.exp_pos _).le)).trans
      (sum_exp_log_Ico_le_of_strict_decay hη hdecay R
        (finiteSafeCutoff l n H u) k)
  have hdiff := finiteProfileDifferenceMoment_le_sum hs le_rfl hJk hk hz hp hp2
  have htwo : 4 * (2 : ℝ) ^ p ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hp2
    rw [Real.rpow_two] at hh
    linarith
  have hd : finiteProfileDifferenceMoment l n H u (finiteSafeCutoff l n H u) k z p ≤
      16 * B := by
    apply hdiff.trans
    calc
      _ ≤ (4 * (2 : ℝ) ^ p) * B := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 16 * B := mul_le_mul_of_nonneg_right htwo hB
  have hprefix := finiteProfileMoment_at_cutoff_le hl hs hJ hz0 hz hp.le hp2
  have hdecomp := finiteProfileMoment_le_difference_add_prefix hJk z hp.le hp2
  calc
    _ ≤ 32 * B + 2 * Real.exp (4 * K) := by nlinarith
    _ = _ := by dsimp [B]; ring

def finiteProfileGrowthBad (C l : ℝ) (n H : ℕ) : Set (ℕ → ℝ) :=
  {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
    ∃ k, 1 ≤ k ∧ k ≤ H ∧ finiteSafeCutoff l n H u ≤ k ∧
      ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧ ∃ p ∈ Ioc (1 : ℝ) 2,
        C * profileGrowthScale (complexProfileMomentExponent l z p) k <
          finiteProfileMoment (Complex.exp z) p l n H u k}

theorem measurableSet_finiteProfileGrowthBad (C l : ℝ) (n H : ℕ) :
    MeasurableSet (finiteProfileGrowthBad C l n H) := by
  have htransfer : ∀ u v, (∀ i < H, finiteBirth l n u i = finiteBirth l n v i) →
      u ∈ finiteProfileGrowthBad C l n H → v ∈ finiteProfileGrowthBad C l n H := by
    intro u v he
    rintro ⟨hs, k, hk1, hk, hJ, z, hz0, hz, p, hp, hbad⟩
    refine ⟨?_, k, hk1, hk, ?_, z, hz0, hz, p, hp, ?_⟩
    · intro i hi
      rw [← finiteWalk_congr_birth_prefix he hi]
      exact hs i hi
    · rwa [← finiteSafeCutoff_congr_birth_prefix he]
    · rwa [← finiteProfileMoment_congr_prefix (Complex.exp z) p he hk]
  apply measurableSet_of_finiteBirth_prefix l n H
  intro u v he
  exact ⟨htransfer u v he, htransfer v u (fun i hi ↦ (he i hi).symm)⟩

/-- A single tight multiplier controls every event time, complex tilt in the
source strip and moment order simultaneously.  Parameter uniformity is weak:
the parameter is chosen outside the probability, after the common constants. -/
theorem finiteProfileMoment_growth_uniform {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real (finiteProfileGrowthBad C l n ⌊T * n⌋₊) < ε := by
  have hδ : 0 < ε / 3 := by positivity
  obtain ⟨R, hR, NR, hinc⟩ := finiteProfileIncrementBound_uniform_exp hI hT hparams hδ
  obtain ⟨K, NK, hcut⟩ := finiteSafeCutoff_survival_uniform_tight hI hT hparams hδ
  let C := 32 * Real.exp R + 2 * Real.exp (4 * K)
  refine ⟨C, by dsimp [C]; positivity, max NR NK, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let E₁ : Set (ℕ → ℝ) := {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
    ∃ k < H, finiteSafeCutoff l n H u ≤ k ∧
      ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧ ∃ p ∈ Icc (1 : ℝ) 2,
        Real.exp (complexProfileMomentExponent l z p * Real.log (k + 1 : ℕ) + R) <
          finiteProfileIncrementBound l n H u k z p}
  let E₂ : Set (ℕ → ℝ) := {u | K <
    (if ∀ i ≤ H, 0 < finiteWalk l n u i then finiteSafeCutoff l n H u else 0)}
  have hsub : finiteProfileGrowthBad C l n H ⊆ E₁ ∪ E₂ := by
    rintro u ⟨hs, k, hk1, hk, hJk, z, hz0, hz, p, hp, hbad⟩
    by_contra hnot
    have h₁ : u ∉ E₁ := fun h ↦ hnot (Or.inl h)
    have h₂ : u ∉ E₂ := fun h ↦ hnot (Or.inr h)
    have hJ : finiteSafeCutoff l n H u ≤ K := by
      apply le_of_not_gt
      intro h
      apply h₂
      simpa only [E₂, mem_ofPred_eq, ite_eq_left hs] using h
    have hbound : ∀ i ∈ Finset.Ico (finiteSafeCutoff l n H u) k,
        finiteProfileIncrementBound l n H u i z p ≤
          Real.exp (complexProfileMomentExponent l z p * Real.log (i + 1 : ℕ) + R) := by
      intro i hi
      obtain ⟨hJi, hik⟩ := Finset.mem_Ico.mp hi
      apply le_of_not_gt
      intro h
      exact h₁ ⟨hs, i, hik.trans_le hk, hJi, z, hz0, hz, p, ⟨hp.1.le, hp.2⟩, h⟩
    exact (not_lt_of_ge (finiteProfileMoment_le_growth (hparams l hl).1 hs hJ
      hk1 hk hJk hz0 hz hp.1 hp.2 hbound)) hbad
  have h₁ : uniformLaw.real E₁ < ε / 3 := hinc n (by omega) l hl
  have h₂ : uniformLaw.real E₂ < ε / 3 := hcut n (by omega) l hl
  have hm := measureReal_mono (μ := uniformLaw) hsub
  have hu := measureReal_union_le (μ := uniformLaw) E₁ E₂
  change uniformLaw.real (finiteProfileGrowthBad C l n H) < ε
  linarith

end HeightPaper.CountCoupling
