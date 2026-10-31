module

public import HeightPaper.Model.FiniteNormalizerBounds
public import HeightPaper.Model.CoupledPrescribedWalk
public import HeightPaper.Model.PrescribedPrefix
public import HeightPaper.Probability.FiniteReciprocalControl
public import HeightPaper.Probability.FiniteSafeCutoff
public import HeightPaper.Probability.FiniteEventMeasurable

/-!
# Uniform complex normalizer estimates for the finite epidemic

The products are the prescribed-tree normalizers evaluated at the actual
common-uniform epidemic event word and the exact source cutoff. Their error
bounds use the proved centered reciprocal sums, count ratios, and cutoff tails.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators NNReal Classical

namespace HeightPaper.CountCoupling

open Model

/-- The source product from event `Jⁿ + 1` through event `k`. -/
noncomputable def finiteComplexNormalizer (l : ℝ) (n H : ℕ) (u : ℕ → ℝ)
    (k : ℕ) (z : ℂ) : ℂ :=
  prescribedNormalizerFrom (Complex.exp z) (finiteBirth l n u) 1
    (finiteSafeCutoff l n H u) k

/-- The centered logarithm is built from the individual small-factor logs. -/
noncomputable def finiteNormalizerLogError (l : ℝ) (n H : ℕ) (u : ℕ → ℝ)
    (k : ℕ) (z : ℂ) : ℂ :=
  normalizerCenteredLogFrom (finiteBirth l n u) 1 (finiteSafeCutoff l n H u) k
    (l / (l - 1)) (Complex.exp z)

noncomputable def finiteNormalizerMomentRatio (l : ℝ) (n H : ℕ) (u : ℕ → ℝ)
    (k : ℕ) (z : ℂ) (p : ℝ) : ℝ :=
  realNormalizerFrom (Real.exp (p * z.re)) (finiteBirth l n u) 1
    (finiteSafeCutoff l n H u) k / ‖finiteComplexNormalizer l n H u k z‖ ^ p

noncomputable def finiteNormalizerMomentLogError (l : ℝ) (n H : ℕ) (u : ℕ → ℝ)
    (k : ℕ) (z : ℂ) (p : ℝ) : ℝ :=
  Real.log (finiteNormalizerMomentRatio l n H u k z p) -
    l / (l - 1) * (Real.exp (p * z.re) - 1 - p * ((Complex.exp z).re - 1)) * Real.log k

theorem finiteComplexNormalizer_ofReal (l : ℝ) (n H : ℕ) (u : ℕ → ℝ)
    (k : ℕ) (x : ℝ) :
    finiteComplexNormalizer l n H u k (x : ℂ) =
      (realNormalizerFrom (Real.exp x) (finiteBirth l n u) 1 (finiteSafeCutoff l n H u) k : ℂ) := by
  simp only [finiteComplexNormalizer, ← Complex.ofReal_exp, prescribedNormalizerFrom_ofReal]

/-- The real ratio is exactly the source complex numerator at its real tilt. -/
theorem finiteNormalizerMomentRatio_coe (l : ℝ) (n H : ℕ) (u : ℕ → ℝ)
    (k : ℕ) (z : ℂ) (p : ℝ) :
    (finiteNormalizerMomentRatio l n H u k z p : ℂ) =
      finiteComplexNormalizer l n H u k ((p * z.re : ℝ) : ℂ) /
        ((‖finiteComplexNormalizer l n H u k z‖ ^ p : ℝ) : ℂ) := by
  simp only [finiteNormalizerMomentRatio, Complex.ofReal_div, finiteComplexNormalizer_ofReal]

theorem norm_exp_sub_one_le_of_re_le {z : ℂ} {a : ℝ} (hza : z.re ≤ a) :
    ‖Complex.exp z - 1‖ ≤ Real.exp a + 1 := by
  apply (norm_sub_le _ _).trans
  rw [Complex.norm_exp, norm_one]
  exact add_le_add (Real.exp_le_exp.mpr hza) le_rfl

/-- The exact source cutoff is safe on the whole closed strip up to `2 zλ`.
Only product indices strictly after `Jⁿ` occur. -/
theorem finiteNormalizer_factor_small {l : ℝ} {n H : ℕ} {u : ℕ → ℝ}
    (hs : ∀ j ≤ H, 0 < finiteWalk l n u j) {k : ℕ} (hk : k ≤ H)
    {z : ℂ} (hz : z.re ≤ 2 * profileRoot l) :
    ∀ i ∈ Finset.Ico (finiteSafeCutoff l n H u) k,
      ‖Complex.exp z - 1‖ * birthReciprocal (finiteBirth l n u) 1 i < 1 / 2 := by
  intro i hi
  have hi' := Finset.mem_Ico.mp hi
  have hiH : i < H := hi'.2.trans_le hk
  have hpos : 0 < (finiteWalk l n u (i + 1) : ℝ) := by
    exact_mod_cast hs (i + 1) (by omega)
  have hsafety := finiteSafeCutoff_safe_after l n H u (by omega :
    finiteSafeCutoff l n H u < i + 1) (by omega : i + 1 ≤ H)
  rw [birthReciprocal_finite_eq hs hiH]
  split_ifs
  · apply lt_of_le_of_lt _ hsafety
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (norm_exp_sub_one_le_of_re_le hz) (by positivity : 0 ≤ 1 / (finiteWalk l n u (i + 1) : ℝ))
  · norm_num

/-- Exact exponential representation with the chosen complex error. -/
theorem finiteComplexNormalizer_eq_exp {l : ℝ} {n H : ℕ} {u : ℕ → ℝ}
    (hs : ∀ j ≤ H, 0 < finiteWalk l n u j) {k : ℕ} (hk : k ≤ H)
    {z : ℂ} (hz : z.re ≤ 2 * profileRoot l) :
    finiteComplexNormalizer l n H u k z = Complex.exp
      (((l / (l - 1) : ℝ) : ℂ) * (Complex.exp z - 1) * (Real.log k : ℂ) +
        finiteNormalizerLogError l n H u k z) :=
  prescribedNormalizerFrom_eq_exp_centered _ _ _ _ _ _
    (fun i hi ↦ (finiteNormalizer_factor_small hs hk hz i hi).trans (by norm_num))

theorem finiteComplexNormalizer_ne_zero {l : ℝ} {n H : ℕ} {u : ℕ → ℝ}
    (hs : ∀ j ≤ H, 0 < finiteWalk l n u j) {k : ℕ} (hk : k ≤ H)
    {z : ℂ} (hz : z.re ≤ 2 * profileRoot l) :
    finiteComplexNormalizer l n H u k z ≠ 0 := by
  rw [finiteComplexNormalizer_eq_exp hs hk hz]
  exact Complex.exp_ne_zero _

/-- The real moment ratio also has an exact exponential representation. -/
theorem finiteNormalizerMomentRatio_eq_exp {l : ℝ} {n H : ℕ} {u : ℕ → ℝ}
    (hs : ∀ j ≤ H, 0 < finiteWalk l n u j) {k : ℕ} (hk : k ≤ H)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz : z.re ≤ 2 * profileRoot l)
    {p : ℝ} (hp : 0 ≤ p) :
    finiteNormalizerMomentRatio l n H u k z p = Real.exp
      (l / (l - 1) * (Real.exp (p * z.re) - 1 - p * ((Complex.exp z).re - 1)) *
        Real.log k + finiteNormalizerMomentLogError l n H u k z p) := by
  have hpos : 0 < finiteNormalizerMomentRatio l n H u k z p := by
    apply div_pos
    · exact realNormalizerFrom_pos (Real.one_le_exp_iff.mpr (mul_nonneg hp hz0)) _ _ _ _
    · exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (finiteComplexNormalizer_ne_zero hs hk hz)) p
  unfold finiteNormalizerMomentLogError
  rw [add_sub_cancel]
  exact (Real.exp_log hpos).symm

theorem birthReciprocal_finite_le_of_ratio {l M : ℝ} {n H : ℕ} {u : ℕ → ℝ}
    (hM : 0 ≤ M) (hs : ∀ j ≤ H, 0 < finiteWalk l n u j)
    (hratio : ∀ j ≤ H, (j : ℝ) / (finiteWalk l n u j : ℝ) ≤ M)
    {i : ℕ} (hi : i < H) :
    birthReciprocal (finiteBirth l n u) 1 i ≤ M / ((i + 1 : ℕ) : ℝ) := by
  have hpos : 0 < (finiteWalk l n u (i + 1) : ℝ) := by
    exact_mod_cast hs (i + 1) (by omega)
  have hiR : (0 : ℝ) < (i + 1 : ℕ) := by positivity
  rw [birthReciprocal_finite_eq hs hi]
  split_ifs
  · apply (div_le_div_iff₀ hpos hiR).mpr
    simpa only [one_mul] using (div_le_iff₀ hpos).mp (hratio (i + 1) (by omega))
  · simp only [zero_div]
    exact div_nonneg hM hiR.le

/-- All time and tilt errors are controlled on the same three good events. -/
theorem finiteNormalizer_errors_le {l M B : ℝ} (hl : 1 < l) (hM : 0 ≤ M)
    (n H K : ℕ) (u : ℕ → ℝ)
    (hs : ∀ j ≤ H, 0 < finiteWalk l n u j)
    (hJ : finiteSafeCutoff l n H u ≤ K)
    (hratio : ∀ j ≤ H, (j : ℝ) / (finiteWalk l n u j : ℝ) ≤ M)
    (hcenter : ∀ j ≤ H,
      |birthReciprocalSum (fun i ↦ (finiteWalk l n u i : ℝ)) (finiteBirth l n u) j -
        l / (l - 1) * Real.log j| ≤ B)
    {k : ℕ} (hJk : finiteSafeCutoff l n H u ≤ k) (hk : k ≤ H)
    {z : ℂ} (hz : z.re ≤ 2 * profileRoot l) :
    ‖finiteNormalizerLogError l n H u k z‖ ≤
        (Real.exp 2 + 1) * (B + K) + (Real.exp 2 + 1) ^ 2 * (2 * M ^ 2) ∧
      ∀ p ∈ Icc (0 : ℝ) 2, 0 ≤ z.re →
        |finiteNormalizerMomentLogError l n H u k z p| ≤
          ((Real.exp 4 + 1) + 2 * (Real.exp 2 + 1)) * (B + K) +
            ((Real.exp 4 + 1) ^ 2 + 2 * (Real.exp 2 + 1) ^ 2) * (2 * M ^ 2) := by
  have hshift : |(∑ i ∈ Finset.Ico (finiteSafeCutoff l n H u) k,
      birthReciprocal (finiteBirth l n u) 1 i) - l / (l - 1) * Real.log k| ≤ B + K :=
    birthReciprocal_Ico_centered_bound _ _ _ _ _ hJk hJ
      (by rw [sum_birthReciprocal_finite_eq hs hk]; exact hcenter k hk)
  have hsquare : (∑ i ∈ Finset.Ico (finiteSafeCutoff l n H u) k,
      (birthReciprocal (finiteBirth l n u) 1 i) ^ 2) ≤ 2 * M ^ 2 :=
    birthReciprocal_Ico_square_bound _ _ _ _
      (fun i hi ↦ birthReciprocal_finite_le_of_ratio hM hs hratio (hi.trans_le hk))
  have hz2 : z.re ≤ 2 := hz.trans (by linarith [profileRoot_lt_one hl])
  have hw := norm_exp_sub_one_le_of_re_le hz2
  have hsmall := fun i hi ↦ (finiteNormalizer_factor_small hs hk hz i hi).le
  constructor
  · exact norm_normalizerCenteredLogFrom_le _ _ _ _ (by positivity) hshift hsquare _ hw hsmall
  · intro p hp hz0
    have hpabs : |p| ≤ 2 := by rw [abs_of_nonneg hp.1]; exact hp.2
    have hv : 1 ≤ Real.exp (p * z.re) := Real.one_le_exp_iff.mpr (mul_nonneg hp.1 hz0)
    have hvV : Real.exp (p * z.re) - 1 ≤ Real.exp 4 + 1 := by
      have hexp := Real.exp_le_exp.mpr (show p * z.re ≤ 4 by nlinarith [hp.1, hp.2])
      linarith
    exact normalizerFrom_momentRatio_centered_bound _ _ _ _
      (by positivity) (by positivity) (by norm_num) hv hvV hpabs hshift hsquare _ hw hsmall

/-- Joint error event: event time, complex tilt, and moment order are inside
the probability. The epidemic parameter stays outside it. -/
def finiteNormalizerErrorTail (R l : ℝ) (n H : ℕ) : Set (ℕ → ℝ) :=
  {u | (∀ j ≤ H, 0 < finiteWalk l n u j) ∧
    ∃ k ≤ H, finiteSafeCutoff l n H u ≤ k ∧
      ((∃ z : ℂ, z.re ≤ 2 * profileRoot l ∧ R < ‖finiteNormalizerLogError l n H u k z‖) ∨
        ∃ z : ℂ, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
          ∃ p ∈ Icc (0 : ℝ) 2, R < |finiteNormalizerMomentLogError l n H u k z p|)}

/-- Both source normalizer errors are tight, simultaneously over every event
time and the full safe tilt strip, weakly uniformly on compact parameter sets.
No stochastic count or reciprocal hypotheses remain in this statement. -/
theorem finiteNormalizer_errors_uniform_tight {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real (finiteNormalizerErrorTail R l n ⌊T * n⌋₊) < ε := by
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨B, hB, NB, hcenter⟩ := finiteCenteredReciprocal_uniform_tight hI hT hparams hδ
  obtain ⟨M, NM, hratio⟩ := coupled_count_ratio_uniform_tight hI hT hparams hδ
  obtain ⟨K, NK, hcutoff⟩ := finiteSafeCutoff_survival_uniform_tight hI hT hparams hδ
  let A := (Real.exp 2 + 1) * (B + K) + (Real.exp 2 + 1) ^ 2 * (2 * (M : ℝ) ^ 2)
  let D := ((Real.exp 4 + 1) + 2 * (Real.exp 2 + 1)) * (B + K) +
    ((Real.exp 4 + 1) ^ 2 + 2 * (Real.exp 2 + 1) ^ 2) * (2 * (M : ℝ) ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨A + D, add_nonneg hA hD, max NB (max NM NK), ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let E₁ : Set (ℕ → ℝ) := {u | (∀ j ≤ H, 0 < finiteWalk l n u j) ∧
    ∃ k ≤ H, B < |birthReciprocalSum (fun j ↦ (finiteWalk l n u j : ℝ))
      (finiteBirth l n u) k - (l : ℝ) / ((l : ℝ) - 1) * Real.log k|}
  let E₂ := coupledCountRatioTail M l n H
  let E₃ : Set (ℕ → ℝ) := {u | K <
    (if ∀ j ≤ H, 0 < finiteWalk l n u j then finiteSafeCutoff l n H u else 0)}
  have hsub : finiteNormalizerErrorTail (A + D) l n H ⊆ (E₁ ∪ E₂) ∪ E₃ := by
    rintro u ⟨hs, k, hk, hJk, hbad⟩
    by_contra hnot
    have h₁ : u ∉ E₁ := fun h ↦ hnot (Or.inl (Or.inl h))
    have h₂ : u ∉ E₂ := fun h ↦ hnot (Or.inl (Or.inr h))
    have h₃ : u ∉ E₃ := fun h ↦ hnot (Or.inr h)
    have hc : ∀ j ≤ H, |birthReciprocalSum (fun i ↦ (finiteWalk l n u i : ℝ))
        (finiteBirth l n u) j - (l : ℝ) / ((l : ℝ) - 1) * Real.log j| ≤ B :=
      fun j hj ↦ le_of_not_gt (fun h ↦ h₁ ⟨hs, j, hj, h⟩)
    have hr : ∀ j ≤ H, (j : ℝ) / (finiteWalk l n u j : ℝ) ≤ M :=
      fun j hj ↦ le_of_not_gt (fun h ↦ h₂ ⟨hs, j, hj, h⟩)
    have hJ : finiteSafeCutoff l n H u ≤ K := by
      apply le_of_not_gt
      intro h
      apply h₃
      simpa only [E₃, mem_ofPred_eq, ite_eq_left hs] using h
    rcases hbad with ⟨z, hz, hlarge⟩ | ⟨z, hz0, hz, p, hp, hlarge⟩
    · have hb := (finiteNormalizer_errors_le (hparams l hl).1 (Nat.cast_nonneg M)
        n H K u hs hJ hr hc hJk hk hz).1
      change ‖finiteNormalizerLogError l n H u k z‖ ≤ A at hb
      linarith
    · have hb := (finiteNormalizer_errors_le (hparams l hl).1 (Nat.cast_nonneg M)
        n H K u hs hJ hr hc hJk hk hz).2 p hp hz0
      change |finiteNormalizerMomentLogError l n H u k z p| ≤ D at hb
      linarith
  have h₁ : uniformLaw.real E₁ < ε / 4 := hcenter n (by omega) l hl
  have h₂ : uniformLaw.real E₂ < ε / 4 := hratio n (by omega) l hl
  have h₃ : uniformLaw.real E₃ < ε / 4 := hcutoff n (by omega) l hl
  have hprob := measureReal_mono (μ := uniformLaw) hsub
  have h12 := measureReal_union_le (μ := uniformLaw) E₁ E₂
  have h123 := measureReal_union_le (μ := uniformLaw) (E₁ ∪ E₂) E₃
  change uniformLaw.real (finiteNormalizerErrorTail (A + D) l n H) < ε
  linarith

/-- The first assertion of the source lemma, in a stronger domain that
contains every compact subset of `E(λ)` (and also of `E′(λ)`). -/
theorem finiteNormalizerLogError_uniform_tight {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {K : Set ℂ} (hK : ∀ l ∈ I, ∀ z ∈ K, z.re ≤ 2 * profileRoot l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I, uniformLaw.real
      {u | (∀ j ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u j) ∧
        ∃ k ≤ ⌊T * n⌋₊, finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ k ∧
          ∃ z ∈ K, R < ‖finiteNormalizerLogError l n ⌊T * n⌋₊ u k z‖} < ε := by
  obtain ⟨R, hR, N, hN⟩ := finiteNormalizer_errors_uniform_tight hI hT hparams hε
  refine ⟨R, hR, N, fun n hn l hl ↦ ?_⟩
  apply lt_of_le_of_lt (measureReal_mono (μ := uniformLaw) ?_) (hN n hn l hl)
  rintro u ⟨hs, k, hk, hJ, z, hz, hb⟩
  exact ⟨hs, k, hk, hJ, Or.inl ⟨z, hK l hl z hz, hb⟩⟩

/-- The second assertion, jointly uniform also over `p ∈ [0,2]`. The real
numerator needs no small-factor restriction, so the full source `E′` works. -/
theorem finiteNormalizerMomentLogError_uniform_tight {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {K : Set ℂ} (hK : ∀ l ∈ I, ∀ z ∈ K, 0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I, uniformLaw.real
      {u | (∀ j ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u j) ∧
        ∃ k ≤ ⌊T * n⌋₊, finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ k ∧
          ∃ z ∈ K, ∃ p ∈ Icc (0 : ℝ) 2,
            R < |finiteNormalizerMomentLogError l n ⌊T * n⌋₊ u k z p|} < ε := by
  obtain ⟨R, hR, N, hN⟩ := finiteNormalizer_errors_uniform_tight hI hT hparams hε
  refine ⟨R, hR, N, fun n hn l hl ↦ ?_⟩
  apply lt_of_le_of_lt (measureReal_mono (μ := uniformLaw) ?_) (hN n hn l hl)
  rintro u ⟨hs, k, hk, hJ, z, hz, p, hp, hb⟩
  exact ⟨hs, k, hk, hJ, Or.inr ⟨z, (hK l hl z hz).1, (hK l hl z hz).2, p, hp, hb⟩⟩

/-- The normalizers and both chosen errors only use the finite event word. -/
theorem finiteNormalizer_congr_birth_prefix {l : ℝ} {n H : ℕ} {u v : ℕ → ℝ}
    (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n v i)
    {k : ℕ} (hk : k ≤ H) (z : ℂ) (p : ℝ) :
    finiteComplexNormalizer l n H u k z = finiteComplexNormalizer l n H v k z ∧
      finiteNormalizerLogError l n H u k z = finiteNormalizerLogError l n H v k z ∧
      finiteNormalizerMomentRatio l n H u k z p = finiteNormalizerMomentRatio l n H v k z p ∧
      finiteNormalizerMomentLogError l n H u k z p = finiteNormalizerMomentLogError l n H v k z p := by
  have hJ := finiteSafeCutoff_congr_birth_prefix he
  have ha : ∀ i ∈ Finset.Ico (finiteSafeCutoff l n H v) k,
      birthReciprocal (finiteBirth l n u) 1 i = birthReciprocal (finiteBirth l n v) 1 i :=
    fun i hi ↦ birthReciprocal_congr_prefix 1 he ((Finset.mem_Ico.mp hi).2.trans_le hk)
  have hC : finiteComplexNormalizer l n H u k z = finiteComplexNormalizer l n H v k z := by
    simp only [finiteComplexNormalizer, hJ]
    exact prescribedNormalizerFrom_congr_prefix _ 1 _ he hk
  have hE : finiteNormalizerLogError l n H u k z = finiteNormalizerLogError l n H v k z := by
    simp only [finiteNormalizerLogError, normalizerCenteredLogFrom, normalizerRemainderFrom,
      complexProductRemainder, hJ]
    have hsum := Finset.sum_congr rfl ha
    rw [hsum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [ha i hi]
  have hR : finiteNormalizerMomentRatio l n H u k z p = finiteNormalizerMomentRatio l n H v k z p := by
    simp only [finiteNormalizerMomentRatio, hJ, hC, realNormalizerFrom_congr_prefix _ 1 _ he hk]
  exact ⟨hC, hE, hR, by simp only [finiteNormalizerMomentLogError, hR]⟩

theorem measurable_finiteComplexNormalizer (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (z : ℂ) :
    Measurable (fun u ↦ finiteComplexNormalizer l n H u k z) :=
  measurable_of_finiteBirth_prefix l n H
    (fun _ _ he ↦ (finiteNormalizer_congr_birth_prefix he hk z 0).1)

theorem measurable_finiteNormalizerLogError (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (z : ℂ) :
    Measurable (fun u ↦ finiteNormalizerLogError l n H u k z) :=
  measurable_of_finiteBirth_prefix l n H
    (fun _ _ he ↦ (finiteNormalizer_congr_birth_prefix he hk z 0).2.1)

theorem measurable_finiteNormalizerMomentRatio (l : ℝ) (n H k : ℕ) (hk : k ≤ H)
    (z : ℂ) (p : ℝ) : Measurable (fun u ↦ finiteNormalizerMomentRatio l n H u k z p) :=
  measurable_of_finiteBirth_prefix l n H
    (fun _ _ he ↦ (finiteNormalizer_congr_birth_prefix he hk z p).2.2.1)

theorem measurable_finiteNormalizerMomentLogError (l : ℝ) (n H k : ℕ) (hk : k ≤ H)
    (z : ℂ) (p : ℝ) : Measurable (fun u ↦ finiteNormalizerMomentLogError l n H u k z p) :=
  measurable_of_finiteBirth_prefix l n H
    (fun _ _ he ↦ (finiteNormalizer_congr_birth_prefix he hk z p).2.2.2)

/-- The joint supremum-tail event is measurable despite its uncountable tilt
and moment-order quantifiers: it depends on a finite Boolean event word. -/
theorem measurableSet_finiteNormalizerErrorTail (R l : ℝ) (n H : ℕ) :
    MeasurableSet (finiteNormalizerErrorTail R l n H) := by
  apply measurableSet_of_finiteBirth_prefix l n H
  intro u v he
  have hsurv : (∀ j ≤ H, 0 < finiteWalk l n u j) ↔ ∀ j ≤ H, 0 < finiteWalk l n v j := by
    constructor <;> intro hs j hj
    · rw [← finiteWalk_congr_birth_prefix he hj]
      exact hs j hj
    · rw [finiteWalk_congr_birth_prefix he hj]
      exact hs j hj
  simp only [finiteNormalizerErrorTail, mem_ofPred_eq, hsurv, finiteSafeCutoff_congr_birth_prefix he]
  apply and_congr_right
  intro _hs
  apply exists_congr
  intro k
  apply and_congr_right
  intro hk
  apply and_congr_right
  intro _hJ
  apply or_congr
  · apply exists_congr
    intro z
    rw [(finiteNormalizer_congr_birth_prefix he hk z 0).2.1]
  · apply exists_congr
    intro z
    apply and_congr_right
    intro _hz0
    apply and_congr_right
    intro _hz
    apply exists_congr
    intro p
    rw [(finiteNormalizer_congr_birth_prefix he hk z p).2.2.2]

end HeightPaper.CountCoupling
