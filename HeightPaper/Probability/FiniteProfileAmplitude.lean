module

public import HeightPaper.Probability.FiniteUnshiftedProfileTail
public import HeightPaper.Probability.FiniteAnalyticResidual
public import HeightPaper.Probability.FiniteTreeCouplingLaw
public import HeightPaper.Model.ProfileSaddleResidual
public import HeightPaper.Model.RankProfileBound

/-! # The actual finite saddle amplitude and its factors -/

@[expose] public section

open Complex
open scoped BigOperators

namespace HeightPaper.Model

theorem profileResidual_ofReal (s : State) (γ a x : ℝ) :
    profileResidual s γ a (x : ℂ) =
      ((activeWeight (Real.exp x) s / (infectious s : ℝ) *
        Real.exp (-a * γ * (Real.exp x - 1)) : ℝ) : ℂ) := by
  simp only [profileResidual, poissonExponent, ← Complex.ofReal_exp,
    normalizedActiveWeight_ofReal, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_natCast]
  congr 2
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

theorem profileResidual_ofReal_pos (s : State) (hs : s.active.Nonempty) (γ a x : ℝ) :
    (profileResidual s γ a (x : ℂ)).im = 0 ∧ 0 < (profileResidual s γ a (x : ℂ)).re := by
  rw [profileResidual_ofReal, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, mul_pos (div_pos ?_ ?_) (Real.exp_pos _)⟩
  · exact Finset.sum_pos (fun _ _ => pow_pos (Real.exp_pos _) _) hs
  · exact_mod_cast hs.card_pos

end HeightPaper.Model

namespace HeightPaper.CountCoupling

open Model

/-- The factorization used for probability bounds retains the actual entire
amplitude in Fourier inversion. Its inverse denominator is justified on the
positive-real neighborhood. -/
theorem profileResidual_eq_unshifted_mul_residual (l a : ℝ) (n H : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) {z : ℂ} (hz : 1 ≤ (Complex.exp z).re) :
    profileResidual (coupledTreeState l n q H) (growthFactor l) a z =
      finiteUnshiftedRankProfile l n q H z *
        finiteUnshiftedNormalizerResidual l n H q.1 a z := by
  have hn := one_le_norm_prescribedNormalizer hz (finiteBirth l n q.1) 1 H
  have hc : prescribedNormalizer (Complex.exp z) (finiteBirth l n q.1) 1 H ≠ 0 := by
    intro he
    rw [he, norm_zero] at hn
    norm_num at hn
  have hexp : -(a : ℂ) * poissonExponent (growthFactor l) z =
      -((growthFactor l : ℂ) * (Complex.exp z - 1) * (a : ℂ)) := by
    unfold poissonExponent
    ring
  rw [profileResidual, hexp, finiteUnshiftedRankProfile, prescribedNormalizedProfile,
    infectious_initial, prescribedNormalizerFrom_zero, finiteUnshiftedNormalizerResidual]
  change _ = (_ / prescribedNormalizer (Complex.exp z) (finiteBirth l n q.1) 1 H) * _
  field_simp
  rfl

theorem norm_profileResidual_le_of_unshifted_bounds (l a : ℝ) (n H : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) {z : ℂ} (hz : 1 ≤ (Complex.exp z).re)
    {B M : ℝ} (hB : 0 ≤ B)
    (hprofile : ‖finiteUnshiftedRankProfile l n q H z‖ ≤ B)
    (hresidual : ‖finiteUnshiftedNormalizerResidual l n H q.1 a z‖ ≤ M) :
    ‖profileResidual (coupledTreeState l n q H) (growthFactor l) a z‖ ≤ B * M := by
  rw [profileResidual_eq_unshifted_mul_residual l a n H q hz, norm_mul]
  exact mul_le_mul hprofile hresidual (norm_nonneg _) hB

end HeightPaper.CountCoupling
