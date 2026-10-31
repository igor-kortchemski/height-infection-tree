module

public import HeightPaper.Probability.FiniteProfileGrowth
public import HeightPaper.Analysis.ProfileFourierMoment

/-! # Finite profile moments after normalization at the real saddle -/

@[expose] public section

open MeasureTheory Set
open scoped NNReal BigOperators Classical

namespace HeightPaper.CountCoupling

open Model

/-- The actual prescribed-word profile, normalized by the deterministic
growth at the real saddle `x`. The tree history and the full-horizon safe
cutoff are the same ones used in `finiteProfileMoment`. -/
noncomputable def finiteSaddleMoment (l : ℝ) (n _H : ℕ) (u : ℕ → ℝ) (k : ℕ)
    (x : ℝ) (z : ℂ) (p : ℝ) : ℝ :=
  ∫ q, ‖normalizedActiveWeight (Complex.exp z) q.last /
      (Real.exp (growthFactor l * (Real.exp x - 1) * Real.log k) : ℂ)‖ ^ p
    ∂kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k

theorem finiteComplexNormalizer_saddle_rpow {l : ℝ} {n H : ℕ} {u : ℕ → ℝ}
    (hs : ∀ i ≤ H, 0 < finiteWalk l n u i) {k : ℕ} (hk : k ≤ H)
    (x : ℝ) {z : ℂ} (hz : z.re ≤ 2 * profileRoot l) (p : ℝ) :
    ‖finiteComplexNormalizer l n H u k z /
      (Real.exp (growthFactor l * (Real.exp x - 1) * Real.log k) : ℂ)‖ ^ p =
      Real.exp (p * (growthFactor l * ((Complex.exp z).re - Real.exp x) * Real.log k +
        (finiteNormalizerLogError l n H u k z).re)) := by
  rw [norm_div, finiteComplexNormalizer_eq_exp hs hk hz, Complex.norm_exp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have he : ((((l / (l - 1) : ℝ) : ℂ) * (Complex.exp z - 1) * (Real.log k : ℂ) +
      finiteNormalizerLogError l n H u k z)).re =
      growthFactor l * ((Complex.exp z).re - 1) * Real.log k +
        (finiteNormalizerLogError l n H u k z).re := by
    simp only [growthFactor, Complex.add_re, Complex.mul_re, Complex.sub_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
      mul_zero, zero_mul, sub_zero]
  rw [he, ← Real.exp_sub, ← Real.exp_mul]
  congr 1
  ring

/-- Exact moment factorization; the complex normalizer error remains inside
its exponential until the subsequent quantitative estimate. -/
theorem finiteSaddleMoment_eq {l : ℝ} {n H : ℕ} {u : ℕ → ℝ}
    (hs : ∀ i ≤ H, 0 < finiteWalk l n u i) {k : ℕ} (hk : k ≤ H)
    (x : ℝ) {z : ℂ} (hz : z.re ≤ 2 * profileRoot l) (p : ℝ) :
    finiteSaddleMoment l n H u k x z p =
      finiteProfileMoment (Complex.exp z) p l n H u k *
        Real.exp (p * (growthFactor l * ((Complex.exp z).re - Real.exp x) * Real.log k +
          (finiteNormalizerLogError l n H u k z).re)) := by
  let C := finiteComplexNormalizer l n H u k z
  let D : ℂ := Real.exp (growthFactor l * (Real.exp x - 1) * Real.log k)
  have hC : C ≠ 0 := finiteComplexNormalizer_ne_zero hs hk hz
  have hpoint (q : FinitePath k) :
      ‖normalizedActiveWeight (Complex.exp z) q.last / D‖ ^ p =
        ‖normalizedActiveWeight (Complex.exp z) q.last / C‖ ^ p * ‖C / D‖ ^ p := by
    have he : normalizedActiveWeight (Complex.exp z) q.last / D =
        (normalizedActiveWeight (Complex.exp z) q.last / C) * (C / D) := by
      rw [div_mul_div_cancel₀ hC]
    rw [he, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  unfold finiteSaddleMoment
  change (∫ q, ‖normalizedActiveWeight (Complex.exp z) q.last / D‖ ^ p
    ∂kernelPathMeasure _ (initial n) k) = _
  simp_rw [hpoint]
  rw [integral_mul_const]
  change finiteProfileMoment (Complex.exp z) p l n H u k * ‖C / D‖ ^ p = _
  rw [finiteComplexNormalizer_saddle_rpow hs hk x hz p]

noncomputable def finiteSaddleScale (l η : ℝ) (k : ℕ) (x v p : ℝ) : ℝ :=
  (1 + Real.log k) *
    (Real.exp (-(2 / Real.pi ^ 2) * p * growthFactor l * Real.exp x * Real.log k * v ^ 2) +
      Real.exp (-η * Real.log k))

/-- The real normalization cancels the potentially growing complex moment
exponent. The logarithmic factor remains in both branches. -/
theorem finiteSaddleMoment_le {l C R η : ℝ} (hl : 1 < l) (hC : 0 ≤ C) (hR : 0 ≤ R)
    {n H : ℕ} {u : ℕ → ℝ} (hs : ∀ i ≤ H, 0 < finiteWalk l n u i)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ H) {x v p : ℝ}
    (hx : x ≤ 2 * profileRoot l) (hv : |v| ≤ Real.pi) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hmargin : complexProfileMomentExponent l (x : ℂ) p ≤ -1 - η)
    (hgrowth : finiteProfileMoment (Complex.exp ((x : ℂ) + (v : ℂ) * Complex.I)) p l n H u k ≤
      C * profileGrowthScale (complexProfileMomentExponent l ((x : ℂ) + (v : ℂ) * Complex.I) p) k)
    (herror : ‖finiteNormalizerLogError l n H u k ((x : ℂ) + (v : ℂ) * Complex.I)‖ ≤ R) :
    finiteSaddleMoment l n H u k x ((x : ℂ) + (v : ℂ) * Complex.I) p ≤
      (C * Real.exp (2 * R)) * finiteSaddleScale l η k x v p := by
  let z : ℂ := (x : ℂ) + (v : ℂ) * Complex.I
  let b := p * growthFactor l * ((Complex.exp z).re - Real.exp x) * Real.log k
  have hz : z.re ≤ 2 * profileRoot l := by simpa [z] using hx
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
  have herr : p * (finiteNormalizerLogError l n H u k z).re ≤ 2 * R := by
    have he : (finiteNormalizerLogError l n H u k z).re ≤ R :=
      (Complex.re_le_norm _).trans herror
    exact (mul_le_mul_of_nonneg_left he hp).trans (mul_le_mul_of_nonneg_right hp2 hR)
  have hexp : Real.exp (p * (growthFactor l * ((Complex.exp z).re - Real.exp x) * Real.log k +
      (finiteNormalizerLogError l n H u k z).re)) ≤ Real.exp (2 * R) * Real.exp b := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [b]
    nlinarith
  have hphase := profile_growth_phase_bound hl hlog hp hv hmargin
  have hG : 0 ≤ profileGrowthScale (complexProfileMomentExponent l z p) k :=
    zero_le_one.trans (one_le_profileGrowthScale _ hk1)
  rw [finiteSaddleMoment_eq hs hk x hz p]
  calc
    _ ≤ (C * profileGrowthScale (complexProfileMomentExponent l z p) k) *
        (Real.exp (2 * R) * Real.exp b) :=
      mul_le_mul hgrowth hexp (Real.exp_pos _).le (mul_nonneg hC hG)
    _ = (C * Real.exp (2 * R) * (1 + Real.log k)) *
        (Real.exp (max (complexProfileMomentExponent l z p + 1) 0 * Real.log k) * Real.exp b) := by
      unfold profileGrowthScale
      ring
    _ ≤ (C * Real.exp (2 * R) * (1 + Real.log k)) *
        (Real.exp (-(2 / Real.pi ^ 2) * p * growthFactor l * Real.exp x * Real.log k * v ^ 2) +
          Real.exp (-η * Real.log k)) :=
      mul_le_mul_of_nonneg_left hphase (by positivity)
    _ = _ := by unfold finiteSaddleScale; ring

theorem finiteSaddleMoment_congr_prefix {l : ℝ} {n H : ℕ} {u v : ℕ → ℝ}
    (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n v i) {k : ℕ} (hk : k ≤ H)
    (x : ℝ) (z : ℂ) (p : ℝ) :
    finiteSaddleMoment l n H u k x z p = finiteSaddleMoment l n H v k x z p := by
  unfold finiteSaddleMoment kernelPathMeasure
  rw [kernelPathLaw_prescribed_congr_prefix (initial n) (fun i hi ↦ he i (hi.trans_le hk))]

theorem measurable_finiteSaddleMoment (l : ℝ) (n H k : ℕ) (hk : k ≤ H)
    (x : ℝ) (z : ℂ) (p : ℝ) : Measurable (fun u ↦ finiteSaddleMoment l n H u k x z p) :=
  measurable_of_finiteBirth_prefix l n H
    (fun _ _ he ↦ finiteSaddleMoment_congr_prefix he hk x z p)

def finiteSaddleMomentBad (η C l : ℝ) (n H : ℕ) : Set (ℕ → ℝ) :=
  {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
    ∃ k, 1 ≤ k ∧ k ≤ H ∧ finiteSafeCutoff l n H u ≤ k ∧
      ∃ x : ℝ, 0 ≤ x ∧ x ≤ 2 * profileRoot l ∧ ∃ v : ℝ, |v| ≤ Real.pi ∧
        ∃ p ∈ Ioc (1 : ℝ) 2, complexProfileMomentExponent l (x : ℂ) p ≤ -1 - η ∧
          C * finiteSaddleScale l η k x v p <
            finiteSaddleMoment l n H u k x ((x : ℂ) + (v : ℂ) * Complex.I) p}

theorem measurableSet_finiteSaddleMomentBad (η C l : ℝ) (n H : ℕ) :
    MeasurableSet (finiteSaddleMomentBad η C l n H) := by
  have htransfer : ∀ u v, (∀ i < H, finiteBirth l n u i = finiteBirth l n v i) →
      u ∈ finiteSaddleMomentBad η C l n H → v ∈ finiteSaddleMomentBad η C l n H := by
    intro u v he
    rintro ⟨hs, k, hk1, hk, hJ, x, hx0, hx, w, hw, p, hp, hm, hbad⟩
    refine ⟨?_, k, hk1, hk, ?_, x, hx0, hx, w, hw, p, hp, hm, ?_⟩
    · intro i hi
      rw [← finiteWalk_congr_birth_prefix he hi]
      exact hs i hi
    · rwa [← finiteSafeCutoff_congr_birth_prefix he]
    · rwa [← finiteSaddleMoment_congr_prefix he hk]
  apply measurableSet_of_finiteBirth_prefix l n H
  intro u v he
  exact ⟨htransfer u v he, htransfer v u (fun i hi ↦ (he i hi).symm)⟩

/-- The full Fourier interval has a tight common multiplier in the actual
finite-word conditional moment, uniformly over time, saddle, frequency and
moment order, and weakly uniformly over compact parameter sets. -/
theorem finiteSaddleMoment_uniform_bound {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (η : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real (finiteSaddleMomentBad η D l n ⌊T * n⌋₊) < ε := by
  have hδ : 0 < ε / 3 := by positivity
  obtain ⟨C, hC, NC, hgrowth⟩ := finiteProfileMoment_growth_uniform hI hT hparams hδ
  obtain ⟨R, hR, NR, hnormal⟩ := finiteNormalizer_errors_uniform_tight hI hT hparams hδ
  refine ⟨C * Real.exp (2 * R), by positivity, max NC NR, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  have hsub : finiteSaddleMomentBad η (C * Real.exp (2 * R)) l n H ⊆
      finiteProfileGrowthBad C l n H ∪ finiteNormalizerErrorTail R l n H := by
    rintro u ⟨hs, k, hk1, hk, hJ, x, hx0, hx, v, hv, p, hp, hm, hbad⟩
    by_contra hnot
    have h₁ : u ∉ finiteProfileGrowthBad C l n H := fun h ↦ hnot (Or.inl h)
    have h₂ : u ∉ finiteNormalizerErrorTail R l n H := fun h ↦ hnot (Or.inr h)
    let z : ℂ := (x : ℂ) + (v : ℂ) * Complex.I
    have hz0 : 0 ≤ z.re := by simpa [z] using hx0
    have hz : z.re ≤ 2 * profileRoot l := by simpa [z] using hx
    have hmoment : finiteProfileMoment (Complex.exp z) p l n H u k ≤
        C * profileGrowthScale (complexProfileMomentExponent l z p) k :=
      le_of_not_gt (fun h ↦ h₁ ⟨hs, k, hk1, hk, hJ, z, hz0, hz, p, hp, h⟩)
    have herr : ‖finiteNormalizerLogError l n H u k z‖ ≤ R :=
      le_of_not_gt (fun h ↦ h₂ ⟨hs, k, hk, hJ, Or.inl ⟨z, hz, h⟩⟩)
    exact (not_lt_of_ge (finiteSaddleMoment_le (hparams l hl).1 hC hR hs hk1 hk hx hv
      (by linarith [hp.1]) hp.2 hm hmoment herr)) hbad
  have h₁ := hgrowth n (show NC ≤ n by omega) l hl
  have h₂ := hnormal n (show NR ≤ n by omega) l hl
  have hm := measureReal_mono (μ := uniformLaw) hsub
  have hu := measureReal_union_le (μ := uniformLaw) (finiteProfileGrowthBad C l n H)
    (finiteNormalizerErrorTail R l n H)
  change uniformLaw.real (finiteSaddleMomentBad η (C * Real.exp (2 * R)) l n H) < ε
  linarith

end HeightPaper.CountCoupling
