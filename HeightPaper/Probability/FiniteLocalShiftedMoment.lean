module

public import HeightPaper.Probability.LocalProfileLimitParentMoment
public import HeightPaper.Probability.FiniteProfileMomentConditionalExpectation
public import HeightPaper.Model.ProfileMomentTriangle

/-!
# A higher conditional moment for the finite-to-local profile difference

The finite prescribed-word moment and the canonical local parent moment
combine by the elementary moment triangle inequality.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace HeightPaper.CountCoupling

theorem finiteShifted_localLimit_parent_difference_moment_le
    (l : ℝ) (n H k : ℕ) (hk : k ≤ H) (u : ℕ → ℝ)
    (z : ℂ) {q Cfinite Clocal : ℝ} (hq : 1 ≤ q)
    (hfinite : finiteProfileMoment (Complex.exp z) q l n H u k ≤ Cfinite)
    (hlocal : Integrable
      (fun v ↦ ‖localRankProfileLimit l 0 (u, v) z‖ ^ q) uniformLaw ∧
      (∫ v, ‖localRankProfileLimit l 0 (u, v) z‖ ^ q ∂uniformLaw) ≤ Clocal) :
    Integrable (fun v ↦ ‖finiteShiftedRankProfile l n H (u, v) k z -
      localRankProfileLimit l 0 (u, v) z‖ ^ q) uniformLaw ∧
    (∫ v, ‖finiteShiftedRankProfile l n H (u, v) k z -
      localRankProfileLimit l 0 (u, v) z‖ ^ q ∂uniformLaw) ≤
      (2 : ℝ) ^ (q - 1) * (Cfinite + Clocal) := by
  have hfinmeas : Measurable
      (fun v ↦ finiteShiftedRankProfile l n H (u, v) k z) :=
    (measurable_finiteShiftedRankProfile l n H k hk z).comp
      (measurable_const.prodMk measurable_id)
  have hlocmeas : Measurable (fun v ↦ localRankProfileLimit l 0 (u, v) z) :=
    (measurable_localRankProfileLimit l 0 z).comp
      (measurable_const.prodMk measurable_id)
  have hfinint : Integrable
      (fun v ↦ ‖finiteShiftedRankProfile l n H (u, v) k z‖ ^ q) uniformLaw :=
    finiteShiftedRankProfile_parent_moment_integrable l n H k u z q
  have htriangle := Model.integral_norm_sub_rpow_le uniformLaw hq
    hfinmeas hlocmeas hfinint hlocal.1
  have hfinbound :
      (∫ v, ‖finiteShiftedRankProfile l n H (u, v) k z‖ ^ q ∂uniformLaw) ≤
        Cfinite := by
    rw [finiteShiftedRankProfile_parent_moment_eq]
    exact hfinite
  refine ⟨htriangle.1, htriangle.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (add_le_add hfinbound hlocal.2) (Real.rpow_nonneg (by norm_num) _)

end HeightPaper.CountCoupling
