module

public import HeightPaper.Probability.FiniteLocalShiftedMomentUniform
public import HeightPaper.Probability.FiniteShiftedLocalJointProbability
public import HeightPaper.Probability.ConditionalMomentTransfer
public import HeightPaper.Probability.EarlyBranchJointLaw

/-!
# Conditional finite-to-local moment comparison at a fixed real tilt

Joint convergence in probability and uniform higher conditional moments
give a lower conditional moment convergence on the common count word.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

theorem uniform_finiteShifted_localLimit_conditional_moment_fixed_real
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ p ∈ Ioo (1 : ℝ) 2, ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real {u | u ∈ finiteSurvival l n ⌊T * n⌋₊ ∧
        u ∈ localSurvival l ∧
        finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ A n ∧
        ε < ∫ v, ‖finiteShiftedRankProfile l n ⌊T * n⌋₊
          (u, v) (A n) (x : ℂ) -
          localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw} < δ := by
  obtain ⟨q, hq, C, hC, Nhigh, hhigh⟩ :=
    finiteShifted_localLimit_parent_difference_moment_uniform
      hI hl₀ hT hparams hIlower hx A hA hAH (show 0 < δ / 2 by positivity)
  let p : ℝ := (1 + q) / 2
  have hp : 1 < p := by dsimp [p]; linarith [hq.1]
  have hpq : p < q := by dsimp [p]; linarith [hq.1]
  have hp2 : p < 2 := hpq.trans hq.2
  obtain ⟨a, R, d, ha, haR, hd, hnum⟩ :=
    exists_conditional_moment_truncation (zero_lt_one.trans hp) hpq hε
  have htarget : 0 < δ * d / 2 := by positivity
  obtain ⟨Nprob, hprob⟩ :=
    uniform_finiteShiftedProfile_localLimit_moving_time_probability_of_real_tilt
      hI hl₀ hT hparams hIlower hx A hA hAH ha htarget
  refine ⟨p, ⟨hp, hp2⟩, max Nhigh Nprob, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let S : Set (ℕ → ℝ) :=
    {u | u ∈ finiteSurvival l n H ∧ u ∈ localSurvival l ∧
      finiteSafeCutoff l n H u ≤ A n}
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun w ↦
    ‖finiteShiftedRankProfile l n H w (A n) (x : ℂ) -
      localRankProfileLimit l 0 w (x : ℂ)‖
  obtain ⟨B, hB, hBsmall, hgood⟩ :=
    hhigh n ((le_max_left _ _).trans hn) l hl
  have hS : MeasurableSet S :=
    (measurableSet_finiteSurvival (l : ℝ) n H).inter
      ((measurableSet_localSurvival (l : ℝ)).inter
        (measurableSet_le (measurable_finiteSafeCutoff (l : ℝ) n H) measurable_const))
  have hF : Measurable F :=
    ((measurable_finiteShiftedRankProfile (l : ℝ) n H (A n) (hAH n) (x : ℂ)).sub
      (measurable_localRankProfileLimit (l : ℝ) 0 (x : ℂ))).norm
  have hFn (w : (ℕ → ℝ) × (ℕ → ℝ)) : 0 ≤ F w := norm_nonneg _
  have hgood' : ∀ᵐ u ∂uniformLaw, u ∈ S → u ∉ B →
      Integrable (fun v ↦ F (u, v) ^ p) uniformLaw ∧
      Integrable (fun v ↦ F (u, v) ^ q) uniformLaw ∧
      (∫ v, F (u, v) ^ q ∂uniformLaw) ≤ C := by
    filter_upwards [hgood] with u hu hSu hnot
    obtain ⟨hfin, hloc, hcut⟩ := hSu
    obtain ⟨hqi, hqbound⟩ := hu hfin hloc hcut hnot
    have hmeas : Measurable (fun v ↦
        finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ) -
          localRankProfileLimit l 0 (u, v) (x : ℂ)) :=
      ((measurable_finiteShiftedRankProfile (l : ℝ) n H (A n) (hAH n) (x : ℂ)).sub
        (measurable_localRankProfileLimit (l : ℝ) 0 (x : ℂ))).comp
          (measurable_const.prodMk measurable_id)
    have hpi := integrable_norm_rpow_of_le hmeas.aestronglyMeasurable
      (zero_lt_one.trans hp).le (zero_lt_one.trans hq.1).le hpq.le hqi
    exact ⟨hpi, hqi, hqbound⟩
  have htransfer := conditional_lower_moment_bad_le_joint_tail_ae
    uniformLaw uniformLaw F hF hFn S B hS a R p q C d ε ha haR
    (zero_lt_one.trans hp).le hpq hd hnum hgood'
  have hjoint : (uniformLaw.prod uniformLaw).real
      {w | w.1 ∈ S ∧ a < F w} < δ * d / 2 := by
    convert hprob n ((le_max_right _ _).trans hn) l hl using 1
    congr 1
    ext w
    simp only [S, F, H, mem_ofPred_eq]
    tauto
  have hdiv : (uniformLaw.prod uniformLaw).real
      {w | w.1 ∈ S ∧ a < F w} / d < δ / 2 := by
    have hh := div_lt_div_of_pos_right hjoint hd
    convert hh using 1
    field_simp
  have heq : uniformLaw.real {u | u ∈ finiteSurvival l n H ∧
      u ∈ localSurvival l ∧ finiteSafeCutoff l n H u ≤ A n ∧
      ε < ∫ v, ‖finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ) -
        localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw} =
      uniformLaw.real {u | u ∈ S ∧ ε < ∫ v, F (u, v) ^ p ∂uniformLaw} := by
    congr 1
    ext u
    simp only [S, F, mem_ofPred_eq]
    tauto
  rw [heq]
  calc
    _ ≤ uniformLaw.real B + (uniformLaw.prod uniformLaw).real
      {w | w.1 ∈ S ∧ a < F w} / d := htransfer
    _ < δ / 2 + δ / 2 := add_lt_add hBsmall hdiv
    _ = δ := by ring

end HeightPaper.CountCoupling

namespace HeightPaper.CountCoupling

theorem uniform_finiteShifted_localLimit_conditional_moment_fixed_order
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    : ∃ p ∈ Ioo (1 : ℝ) 2, ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real {u | u ∈ finiteSurvival l n ⌊T * n⌋₊ ∧
        u ∈ localSurvival l ∧
        finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ A n ∧
        ε < ∫ v, ‖finiteShiftedRankProfile l n ⌊T * n⌋₊
          (u, v) (A n) (x : ℂ) -
          localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw} < δ := by
  obtain ⟨q, hq, η, hη, r, hr, hwindow⟩ :=
    exists_localProfile_moment_disk hl₀ hx.1 hx.2
  let p : ℝ := (1 + q) / 2
  have hp : 1 < p := by dsimp [p]; linarith [hq.1]
  have hpq : p < q := by dsimp [p]; linarith [hq.1]
  have hp2 : p < 2 := hpq.trans hq.2
  refine ⟨p, ⟨hp, hp2⟩, ?_⟩
  intro ε hε δ hδ
  obtain ⟨C, hC, Nhigh, hhigh⟩ :=
    finiteShifted_localLimit_parent_difference_moment_uniform_of_window
      hI hl₀ hT hparams hIlower hx hq hη hr hwindow A hA hAH
      (show 0 < δ / 2 by positivity)
  obtain ⟨a, R, d, ha, haR, hd, hnum⟩ :=
    exists_conditional_moment_truncation (zero_lt_one.trans hp) hpq hε
  have htarget : 0 < δ * d / 2 := by positivity
  obtain ⟨Nprob, hprob⟩ :=
    uniform_finiteShiftedProfile_localLimit_moving_time_probability_of_real_tilt
      hI hl₀ hT hparams hIlower hx A hA hAH ha htarget
  refine ⟨max Nhigh Nprob, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let S : Set (ℕ → ℝ) :=
    {u | u ∈ finiteSurvival l n H ∧ u ∈ localSurvival l ∧
      finiteSafeCutoff l n H u ≤ A n}
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun w ↦
    ‖finiteShiftedRankProfile l n H w (A n) (x : ℂ) -
      localRankProfileLimit l 0 w (x : ℂ)‖
  obtain ⟨B, hB, hBsmall, hgood⟩ :=
    hhigh n ((le_max_left _ _).trans hn) l hl
  have hS : MeasurableSet S :=
    (measurableSet_finiteSurvival (l : ℝ) n H).inter
      ((measurableSet_localSurvival (l : ℝ)).inter
        (measurableSet_le (measurable_finiteSafeCutoff (l : ℝ) n H) measurable_const))
  have hF : Measurable F :=
    ((measurable_finiteShiftedRankProfile (l : ℝ) n H (A n) (hAH n) (x : ℂ)).sub
      (measurable_localRankProfileLimit (l : ℝ) 0 (x : ℂ))).norm
  have hFn (w : (ℕ → ℝ) × (ℕ → ℝ)) : 0 ≤ F w := norm_nonneg _
  have hgood' : ∀ᵐ u ∂uniformLaw, u ∈ S → u ∉ B →
      Integrable (fun v ↦ F (u, v) ^ p) uniformLaw ∧
      Integrable (fun v ↦ F (u, v) ^ q) uniformLaw ∧
      (∫ v, F (u, v) ^ q ∂uniformLaw) ≤ C := by
    filter_upwards [hgood] with u hu hSu hnot
    obtain ⟨hfin, hloc, hcut⟩ := hSu
    obtain ⟨hqi, hqbound⟩ := hu hfin hloc hcut hnot
    have hmeas : Measurable (fun v ↦
        finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ) -
          localRankProfileLimit l 0 (u, v) (x : ℂ)) :=
      ((measurable_finiteShiftedRankProfile (l : ℝ) n H (A n) (hAH n) (x : ℂ)).sub
        (measurable_localRankProfileLimit (l : ℝ) 0 (x : ℂ))).comp
          (measurable_const.prodMk measurable_id)
    have hpi := integrable_norm_rpow_of_le hmeas.aestronglyMeasurable
      (zero_lt_one.trans hp).le (zero_lt_one.trans hq.1).le hpq.le hqi
    exact ⟨hpi, hqi, hqbound⟩
  have htransfer := conditional_lower_moment_bad_le_joint_tail_ae
    uniformLaw uniformLaw F hF hFn S B hS a R p q C d ε ha haR
    (zero_lt_one.trans hp).le hpq hd hnum hgood'
  have hjoint : (uniformLaw.prod uniformLaw).real
      {w | w.1 ∈ S ∧ a < F w} < δ * d / 2 := by
    convert hprob n ((le_max_right _ _).trans hn) l hl using 1
    congr 1
    ext w
    simp only [S, F, H, mem_ofPred_eq]
    tauto
  have hdiv : (uniformLaw.prod uniformLaw).real
      {w | w.1 ∈ S ∧ a < F w} / d < δ / 2 := by
    have hh := div_lt_div_of_pos_right hjoint hd
    convert hh using 1
    field_simp
  have heq : uniformLaw.real {u | u ∈ finiteSurvival l n H ∧
      u ∈ localSurvival l ∧ finiteSafeCutoff l n H u ≤ A n ∧
      ε < ∫ v, ‖finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ) -
        localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw} =
      uniformLaw.real {u | u ∈ S ∧ ε < ∫ v, F (u, v) ^ p ∂uniformLaw} := by
    congr 1
    ext u
    simp only [S, F, mem_ofPred_eq]
    tauto
  rw [heq]
  calc
    _ ≤ uniformLaw.real B + (uniformLaw.prod uniformLaw).real
      {w | w.1 ∈ S ∧ a < F w} / d := htransfer
    _ < δ / 2 + δ / 2 := add_lt_add hBsmall hdiv
    _ = δ := by ring


end HeightPaper.CountCoupling

namespace HeightPaper.CountCoupling

theorem uniform_finiteShifted_localLimit_conditional_moment_fixed_order_of_window
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x q η r p : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (hq : q ∈ Ioo (1 : ℝ) 2) (hη : 0 < η) (hr : 0 < r)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < r →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ q * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z q ≤ -1 - η)
    (hpdef : p = (1 + q) / 2)
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    : ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real {u | u ∈ finiteSurvival l n ⌊T * n⌋₊ ∧
        u ∈ localSurvival l ∧
        finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ A n ∧
        ε < ∫ v, ‖finiteShiftedRankProfile l n ⌊T * n⌋₊
          (u, v) (A n) (x : ℂ) -
          localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw} < δ := by
  have hp : 1 < p := by rw [hpdef]; linarith [hq.1]
  have hpq : p < q := by rw [hpdef]; linarith [hq.1]
  intro ε hε δ hδ
  obtain ⟨C, hC, Nhigh, hhigh⟩ :=
    finiteShifted_localLimit_parent_difference_moment_uniform_of_window
      hI hl₀ hT hparams hIlower hx hq hη hr hwindow A hA hAH
      (show 0 < δ / 2 by positivity)
  obtain ⟨a, R, d, ha, haR, hd, hnum⟩ :=
    exists_conditional_moment_truncation (zero_lt_one.trans hp) hpq hε
  have htarget : 0 < δ * d / 2 := by positivity
  obtain ⟨Nprob, hprob⟩ :=
    uniform_finiteShiftedProfile_localLimit_moving_time_probability_of_real_tilt
      hI hl₀ hT hparams hIlower hx A hA hAH ha htarget
  refine ⟨max Nhigh Nprob, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let S : Set (ℕ → ℝ) :=
    {u | u ∈ finiteSurvival l n H ∧ u ∈ localSurvival l ∧
      finiteSafeCutoff l n H u ≤ A n}
  let F : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun w ↦
    ‖finiteShiftedRankProfile l n H w (A n) (x : ℂ) -
      localRankProfileLimit l 0 w (x : ℂ)‖
  obtain ⟨B, hB, hBsmall, hgood⟩ :=
    hhigh n ((le_max_left _ _).trans hn) l hl
  have hS : MeasurableSet S :=
    (measurableSet_finiteSurvival (l : ℝ) n H).inter
      ((measurableSet_localSurvival (l : ℝ)).inter
        (measurableSet_le (measurable_finiteSafeCutoff (l : ℝ) n H) measurable_const))
  have hF : Measurable F :=
    ((measurable_finiteShiftedRankProfile (l : ℝ) n H (A n) (hAH n) (x : ℂ)).sub
      (measurable_localRankProfileLimit (l : ℝ) 0 (x : ℂ))).norm
  have hFn (w : (ℕ → ℝ) × (ℕ → ℝ)) : 0 ≤ F w := norm_nonneg _
  have hgood' : ∀ᵐ u ∂uniformLaw, u ∈ S → u ∉ B →
      Integrable (fun v ↦ F (u, v) ^ p) uniformLaw ∧
      Integrable (fun v ↦ F (u, v) ^ q) uniformLaw ∧
      (∫ v, F (u, v) ^ q ∂uniformLaw) ≤ C := by
    filter_upwards [hgood] with u hu hSu hnot
    obtain ⟨hfin, hloc, hcut⟩ := hSu
    obtain ⟨hqi, hqbound⟩ := hu hfin hloc hcut hnot
    have hmeas : Measurable (fun v ↦
        finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ) -
          localRankProfileLimit l 0 (u, v) (x : ℂ)) :=
      ((measurable_finiteShiftedRankProfile (l : ℝ) n H (A n) (hAH n) (x : ℂ)).sub
        (measurable_localRankProfileLimit (l : ℝ) 0 (x : ℂ))).comp
          (measurable_const.prodMk measurable_id)
    have hpi := integrable_norm_rpow_of_le hmeas.aestronglyMeasurable
      (zero_lt_one.trans hp).le (zero_lt_one.trans hq.1).le hpq.le hqi
    exact ⟨hpi, hqi, hqbound⟩
  have htransfer := conditional_lower_moment_bad_le_joint_tail_ae
    uniformLaw uniformLaw F hF hFn S B hS a R p q C d ε ha haR
    (zero_lt_one.trans hp).le hpq hd hnum hgood'
  have hjoint : (uniformLaw.prod uniformLaw).real
      {w | w.1 ∈ S ∧ a < F w} < δ * d / 2 := by
    convert hprob n ((le_max_right _ _).trans hn) l hl using 1
    congr 1
    ext w
    simp only [S, F, H, mem_ofPred_eq]
    tauto
  have hdiv : (uniformLaw.prod uniformLaw).real
      {w | w.1 ∈ S ∧ a < F w} / d < δ / 2 := by
    have hh := div_lt_div_of_pos_right hjoint hd
    convert hh using 1
    field_simp
  have heq : uniformLaw.real {u | u ∈ finiteSurvival l n H ∧
      u ∈ localSurvival l ∧ finiteSafeCutoff l n H u ≤ A n ∧
      ε < ∫ v, ‖finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ) -
        localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw} =
      uniformLaw.real {u | u ∈ S ∧ ε < ∫ v, F (u, v) ^ p ∂uniformLaw} := by
    congr 1
    ext u
    simp only [S, F, mem_ofPred_eq]
    tauto
  rw [heq]
  calc
    _ ≤ uniformLaw.real B + (uniformLaw.prod uniformLaw).real
      {w | w.1 ∈ S ∧ a < F w} / d := htransfer
    _ < δ / 2 + δ / 2 := add_lt_add hBsmall hdiv
    _ = δ := by ring



end HeightPaper.CountCoupling
