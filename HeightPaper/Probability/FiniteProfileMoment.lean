module

public import HeightPaper.Model.CoupledPrescribedWalk
public import HeightPaper.Model.ProfileCutoffMoment
public import HeightPaper.Model.PrescribedPrefix
public import HeightPaper.Probability.FiniteEventMeasurable

/-!
# Uniform Jensen control for the finite coupled profile

The tree expectation is taken under the actual prescribed-word law. Its
identification with epidemic conditioning is `pathLaw_filter_eventCylinder`.
The random prefix constant is bounded using the proved tightness of the
finite safe cutoff, uniformly over all times, bounded weights and moment orders.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

noncomputable def finiteProfileMoment (w : ℂ) (p l : ℝ) (n H : ℕ)
    (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∫ q, ‖normalizedActiveWeight w q.last /
    prescribedNormalizerFrom w (finiteBirth l n u) 1 (finiteSafeCutoff l n H u) k‖ ^ p
    ∂kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) k

noncomputable def finiteProfileMomentRatio (w : ℂ) (p l : ℝ) (n H : ℕ)
    (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  realNormalizerFrom (‖w‖ ^ p) (finiteBirth l n u) 1 (finiteSafeCutoff l n H u) k /
    ‖prescribedNormalizerFrom w (finiteBirth l n u) 1 (finiteSafeCutoff l n H u) k‖ ^ p

theorem finiteProfileMoment_congr_prefix (w : ℂ) (p : ℝ) {l : ℝ} {n H : ℕ}
    {u v : ℕ → ℝ} (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n v i)
    {k : ℕ} (hk : k ≤ H) :
    finiteProfileMoment w p l n H u k = finiteProfileMoment w p l n H v k := by
  unfold finiteProfileMoment
  rw [finiteSafeCutoff_congr_birth_prefix he,
    prescribedNormalizerFrom_congr_prefix w 1 _ he hk]
  unfold kernelPathMeasure
  rw [kernelPathLaw_prescribed_congr_prefix (initial n) (fun i hi ↦ he i (hi.trans_le hk))]

theorem finiteProfileMomentRatio_congr_prefix (w : ℂ) (p : ℝ) {l : ℝ} {n H : ℕ}
    {u v : ℕ → ℝ} (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n v i)
    {k : ℕ} (hk : k ≤ H) :
    finiteProfileMomentRatio w p l n H u k = finiteProfileMomentRatio w p l n H v k := by
  unfold finiteProfileMomentRatio
  rw [finiteSafeCutoff_congr_birth_prefix he,
    prescribedNormalizerFrom_congr_prefix w 1 _ he hk,
    realNormalizerFrom_congr_prefix (‖w‖ ^ p) 1 _ he hk]

theorem measurable_finiteProfileMoment (w : ℂ) (p l : ℝ) (n H k : ℕ) (hk : k ≤ H) :
    Measurable (fun u ↦ finiteProfileMoment w p l n H u k) :=
  measurable_of_finiteBirth_prefix l n H
    (fun _ _ he ↦ finiteProfileMoment_congr_prefix w p he hk)

theorem measurable_finiteProfileMomentRatio (w : ℂ) (p l : ℝ) (n H k : ℕ) (hk : k ≤ H) :
    Measurable (fun u ↦ finiteProfileMomentRatio w p l n H u k) :=
  measurable_of_finiteBirth_prefix l n H
    (fun _ _ he ↦ finiteProfileMomentRatio_congr_prefix w p he hk)

def finiteProfileMomentBad (W R l : ℝ) (n H : ℕ) : Set (ℕ → ℝ) :=
  {u | (∀ j ≤ H, 0 < finiteWalk l n u j) ∧
    ∃ k ≤ H, finiteSafeCutoff l n H u ≤ k ∧
      ∃ w : ℂ, ‖w‖ ≤ W ∧ ∃ p : ℝ, 1 ≤ p ∧ p ≤ 2 ∧
        finiteProfileMomentRatio w p l n H u k * R < finiteProfileMoment w p l n H u k}

theorem measurableSet_finiteProfileMomentBad (W R l : ℝ) (n H : ℕ) :
    MeasurableSet (finiteProfileMomentBad W R l n H) := by
  have htransfer : ∀ u v, (∀ i < H, finiteBirth l n u i = finiteBirth l n v i) →
      u ∈ finiteProfileMomentBad W R l n H → v ∈ finiteProfileMomentBad W R l n H := by
    intro u v he hu
    obtain ⟨hs, k, hk, hJ, w, hwW, p, hp, hp2, hbad⟩ := hu
    refine ⟨?_, k, hk, ?_, w, hwW, p, hp, hp2, ?_⟩
    · intro j hj
      rw [← finiteWalk_congr_birth_prefix he hj]
      exact hs j hj
    · rwa [← finiteSafeCutoff_congr_birth_prefix he]
    · rwa [← finiteProfileMoment_congr_prefix w p he hk,
        ← finiteProfileMomentRatio_congr_prefix w p he hk]
  apply measurableSet_of_finiteBirth_prefix l n H
  intro u v he
  exact ⟨htransfer u v he, htransfer v u (fun i hi ↦ (he i hi).symm)⟩

theorem finiteProfileMomentRatio_nonneg (w : ℂ) (hw : 1 ≤ ‖w‖) {p : ℝ}
    (hp : 0 ≤ p) (l : ℝ) (n H : ℕ) (u : ℕ → ℝ) (k : ℕ) :
    0 ≤ finiteProfileMomentRatio w p l n H u k := by
  exact div_nonneg (realNormalizerFrom_pos (Real.one_le_rpow hw hp) _ _ _ _).le
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem finiteProfileMoment_le_prefix {w : ℂ} (hw : 1 ≤ ‖w‖) {p l : ℝ}
    (hp : 1 ≤ p) (n H : ℕ) (u : ℕ → ℝ)
    (hs : ∀ j ≤ H, 0 < finiteWalk l n u j) {k : ℕ} (hk : k ≤ H)
    (hJ : finiteSafeCutoff l n H u ≤ k) :
    finiteProfileMoment w p l n H u k ≤
      finiteProfileMomentRatio w p l n H u k * (‖w‖ ^ p) ^ finiteSafeCutoff l n H u := by
  exact prescribedPath_shifted_moment_le_prefix w hw (finiteBirth l n u) n k _ hJ hp
    (fun i hi ↦ prescribedWalk_finite_pos hs (hi.trans hk))

theorem finiteProfileMoment_le_max_prefix (w : ℂ) {p l : ℝ}
    (hp : 1 ≤ p) (n H : ℕ) (u : ℕ → ℝ)
    (hs : ∀ j ≤ H, 0 < finiteWalk l n u j) {k : ℕ} (hk : k ≤ H)
    (hJ : finiteSafeCutoff l n H u ≤ k) :
    finiteProfileMoment w p l n H u k ≤
      finiteProfileMomentRatio w p l n H u k * (max 1 (‖w‖ ^ p)) ^ finiteSafeCutoff l n H u := by
  exact prescribedPath_shifted_moment_le_max_prefix w (finiteBirth l n u) n k _ hJ hp
    (fun i hi ↦ prescribedWalk_finite_pos hs (hi.trans hk))

/-- The random multiplier in the paper's Jensen moment bound is tight,
uniformly in the event time, every weight `‖w‖ ≤ W`, and every moment
order `1 ≤ p ≤ 2`; population and parameter follow the common tail constants. -/
theorem finiteProfileMoment_uniform_bound {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {W : ℝ} (hW : 1 ≤ W) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real (finiteProfileMomentBad W R l n ⌊T * n⌋₊) < ε := by
  obtain ⟨J, N, htail⟩ := finiteSafeCutoff_survival_uniform_tight hI hT hparams hε
  refine ⟨(W ^ 2) ^ J, by positivity, N, ?_⟩
  intro n hn l hl
  apply lt_of_le_of_lt (measureReal_mono ?_) (htail n hn l hl)
  rintro u ⟨hs, k, hk, hJk, w, hwW, p, hp, hp2, hbad⟩
  change J < (if ∀ j ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u j then
    finiteSafeCutoff l n ⌊T * n⌋₊ u else 0)
  rw [ite_eq_left hs]
  by_contra hlarge
  have hJ : finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ J := le_of_not_gt hlarge
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hv : ‖w‖ ^ p ≤ W ^ 2 := by
    calc
      _ ≤ W ^ p := Real.rpow_le_rpow (norm_nonneg _) hwW hp0
      _ ≤ W ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW hp2
      _ = _ := Real.rpow_two W
  have hvmax : max 1 (‖w‖ ^ p) ≤ W ^ 2 := max_le (by nlinarith) hv
  have hprefix : (max 1 (‖w‖ ^ p)) ^ finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ (W ^ 2) ^ J := by
    calc
      _ ≤ (W ^ 2) ^ finiteSafeCutoff l n ⌊T * n⌋₊ u := by gcongr
      _ ≤ _ := pow_le_pow_right₀ (by nlinarith : (1 : ℝ) ≤ W ^ 2) hJ
  have hmoment := finiteProfileMoment_le_max_prefix w hp n ⌊T * n⌋₊ u hs hk hJk
  have hratio : 0 ≤ finiteProfileMomentRatio w p l n ⌊T * n⌋₊ u k :=
    div_nonneg (realNormalizerFrom_nonneg (Real.rpow_nonneg (norm_nonneg _) _) _ _ _ _)
      (Real.rpow_nonneg (norm_nonneg _) _)
  have hbound := mul_le_mul_of_nonneg_left hprefix hratio
  exact (not_lt_of_ge (hmoment.trans hbound)) hbad

end HeightPaper.CountCoupling
