module

public import HeightPaper.Probability.FiniteLocalShiftedConditionalMoment
public import HeightPaper.Probability.FiniteShiftedProfileConditionalMoment

/-!
# Conditional convergence at shrinking complex tilts

The real-center finite-to-local comparison and the finite analytic modulus
share one higher moment window. Their conditional moments can therefore be
combined at an order selected before any error tolerances.
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

theorem uniform_finiteShifted_localLimit_shrinking_tilts_conditional_moment_with_window
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    (Kset : ℕ → Set ℂ) (hK : ∀ n, IsCompact (Kset n))
    (hxK : ∀ n, (x : ℂ) ∈ Kset n)
    (hdiam : Tendsto (fun n ↦ Metric.diam (Kset n)) atTop (𝓝 0)) :
    ∃ q ∈ Ioo (1 : ℝ) 2, ∃ η > (0 : ℝ), ∃ ρ > (0 : ℝ),
      (∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
        0 ≤ z.re ∧ z.re < profileRoot l ∧ q * z.re < 2 * profileRoot l ∧
          complexProfileMomentExponent l z q ≤ -1 - η) ∧
      ∃ p ∈ Ioc (1 : ℝ) 2, p = (1 + q) / 2 ∧
      ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
        uniformLaw.real {u | u ∈ finiteSurvival l n ⌊T * n⌋₊ ∧
          u ∈ localSurvival l ∧
          finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ A n ∧
          ∃ z ∈ Kset n,
            ε < ∫ v, ‖finiteShiftedRankProfile l n ⌊T * n⌋₊
              (u, v) (A n) z -
              localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw} < δ := by
  obtain ⟨q, hq, η, hη, ρ, hρ, hw⟩ :=
    exists_localProfile_unshifted_moment_disk hl₀ hx.1 hx.2
  let p : ℝ := (1 + q) / 2
  have hp : 1 < p := by dsimp [p]; linarith [hq.1]
  have hpq : p < q := by dsimp [p]; linarith [hq.1]
  have hpRange : p ∈ Ioc (1 : ℝ) 2 :=
    ⟨hp, (hpq.trans hq.2).le⟩
  have hr : 0 < ρ / 4 := by positivity
  have hrR : ρ / 4 < ρ / 2 := by linarith
  have hRρ : ρ / 2 < ρ := by linarith
  have hright : ∀ z ∈ closedBall (x : ℂ) (ρ / 2),
      1 ≤ (Complex.exp z).re := by
    intro z hz
    exact (hw l₀ le_rfl z ((mem_closedBall.mp hz).trans_lt hRρ)).1.le
  have hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ q * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z q ≤ -1 - η :=
    fun l hl z hz ↦ (hw l hl z hz).2
  refine ⟨q, hq, η, hη, ρ, hρ, hwindow, p, hpRange, rfl, ?_⟩
  intro ε hε δ hδ
  let c : ℝ := (2 : ℝ) ^ (p - 1)
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  let e : ℝ := ε / (4 * c)
  have he : 0 < e := by dsimp [e]; positivity
  have hδ3 : 0 < δ / 3 := by positivity
  obtain ⟨Ntilt, htilt⟩ :=
    uniform_finiteShiftedProfile_shrinking_tilts_conditional_moment
      hI hl₀ hT hparams hIlower hx ⟨hq.1, hq.2.le⟩ hη
      hr hrR hRρ hright hwindow A hA hAH Kset hK hxK hdiam
      (zero_lt_one.trans hp) hpq he hδ3
  obtain ⟨Ncenter, hcenter⟩ :=
    uniform_finiteShifted_localLimit_conditional_moment_fixed_order_of_window
      hI hl₀ hT hparams hIlower hx hq hη hρ hwindow rfl
      A hA hAH e he (δ / 3) hδ3
  obtain ⟨C, hC, Nhigh, hhigh⟩ :=
    finiteShifted_localLimit_parent_difference_moment_uniform_of_window
      hI hl₀ hT hparams hIlower hx hq hη hρ hwindow A hA hAH hδ3
  refine ⟨max Ntilt (max Ncenter Nhigh), ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let S : Set (ℕ → ℝ) :=
    {u | u ∈ finiteSurvival l n H ∧ u ∈ localSurvival l ∧
      finiteSafeCutoff l n H u ≤ A n}
  let Tbad : Set (ℕ → ℝ) :=
    {u | u ∈ finiteSurvival l n H ∧ finiteSafeCutoff l n H u ≤ A n ∧
      ∃ z ∈ Kset n,
        e < ∫ v, ‖finiteShiftedRankProfile l n H (u, v) (A n) z -
          finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ)‖ ^ p
          ∂uniformLaw}
  let Cbad : Set (ℕ → ℝ) :=
    {u | u ∈ S ∧ e < ∫ v,
      ‖finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ) -
        localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw}
  obtain ⟨B, hB, hBsmall, hgood⟩ :=
    hhigh n ((le_max_right _ _).trans ((le_max_right _ _).trans hn)) l hl
  have hS : MeasurableSet S :=
    (measurableSet_finiteSurvival (l : ℝ) n H).inter
      ((measurableSet_localSurvival (l : ℝ)).inter
        (measurableSet_le (measurable_finiteSafeCutoff (l : ℝ) n H) measurable_const))
  have hTbad : uniformLaw.real Tbad < δ / 3 := by
    simpa only [Tbad, finiteSurvival, H, Set.mem_ofPred_eq] using
      htilt n ((le_max_left _ _).trans hn) l hl
  have hCbad : uniformLaw.real Cbad < δ / 3 := by
    simpa only [Cbad, S, H, mem_ofPred_eq, and_assoc] using
      hcenter n ((le_max_left _ _).trans ((le_max_right _ _).trans hn)) l hl
  have hsub : ∀ᵐ u ∂uniformLaw,
      (u ∈ S ∧ ∃ z ∈ Kset n,
        ε < ∫ v, ‖finiteShiftedRankProfile l n H (u, v) (A n) z -
          localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw) →
      u ∈ B ∪ (Tbad ∪ Cbad) := by
    filter_upwards [hgood] with u hu ⟨hSu, z, hz, htarget⟩
    by_cases hBu : u ∈ B
    · exact Or.inl hBu
    by_cases hCu : u ∈ Cbad
    · exact Or.inr (Or.inr hCu)
    by_cases hTu : u ∈ Tbad
    · exact Or.inr (Or.inl hTu)
    exfalso
    obtain ⟨hfin, hloc, hcut⟩ := hSu
    obtain ⟨hqi, _⟩ := hu hfin hloc hcut hBu
    have hmeasCenter : Measurable (fun v ↦
        finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ) -
          localRankProfileLimit l 0 (u, v) (x : ℂ)) :=
      ((measurable_finiteShiftedRankProfile (l : ℝ) n H (A n) (hAH n) (x : ℂ)).sub
        (measurable_localRankProfileLimit (l : ℝ) 0 (x : ℂ))).comp
          (measurable_const.prodMk measurable_id)
    have hpi : Integrable (fun v ↦
        ‖finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ) -
          localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p) uniformLaw :=
      integrable_norm_rpow_of_le hmeasCenter.aestronglyMeasurable
        (zero_lt_one.trans hp).le (zero_lt_one.trans hq.1).le hpq.le hqi
    have htiltInt : Integrable (fun v ↦
        ‖finiteShiftedRankProfile l n H (u, v) (A n) z -
          finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ)‖ ^ p) uniformLaw :=
      finiteShiftedRankProfile_parent_difference_integrable
        (l : ℝ) n H (A n) u z (x : ℂ) p
    have hf : Measurable (fun v ↦
        finiteShiftedRankProfile l n H (u, v) (A n) z -
          finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ)) :=
      ((measurable_finiteShiftedRankProfile (l : ℝ) n H (A n) (hAH n) z).sub
        (measurable_finiteShiftedRankProfile (l : ℝ) n H (A n) (hAH n) (x : ℂ))).comp
          (measurable_const.prodMk measurable_id)
    have hg : Measurable (fun v ↦
        localRankProfileLimit l 0 (u, v) (x : ℂ) -
          finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ)) := by
      exact ((measurable_localRankProfileLimit (l : ℝ) 0 (x : ℂ)).sub
        (measurable_finiteShiftedRankProfile (l : ℝ) n H (A n) (hAH n) (x : ℂ))).comp
          (measurable_const.prodMk measurable_id)
    have hgi : Integrable (fun v ↦
        ‖localRankProfileLimit l 0 (u, v) (x : ℂ) -
          finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ)‖ ^ p) uniformLaw := by
      simpa only [norm_sub_rev] using hpi
    have htriangle := Model.integral_norm_sub_rpow_le uniformLaw hp.le hf hg htiltInt hgi
    have hbound :
        (∫ v, ‖finiteShiftedRankProfile l n H (u, v) (A n) z -
          localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw) ≤
        c * ((∫ v, ‖finiteShiftedRankProfile l n H (u, v) (A n) z -
            finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ)‖ ^ p ∂uniformLaw) +
          (∫ v, ‖finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ) -
            localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw)) := by
      convert htriangle.2 using 1
      · congr 1; ext v; congr 1; abel
      · simp only [c, norm_sub_rev]
    have hcenterSmall :
        (∫ v, ‖finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ) -
          localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw) ≤ e :=
      le_of_not_gt (fun hh ↦ hCu ⟨⟨hfin, hloc, hcut⟩, hh⟩)
    have htiltSmall :
        (∫ v, ‖finiteShiftedRankProfile l n H (u, v) (A n) z -
          finiteShiftedRankProfile l n H (u, v) (A n) (x : ℂ)‖ ^ p ∂uniformLaw) ≤ e :=
      le_of_not_gt (fun hh ↦ hTu ⟨hfin, hcut, z, hz, hh⟩)
    have hnum : c * (e + e) < ε := by
      have hce : c * e = ε / 4 := by dsimp [e]; field_simp
      nlinarith
    exact not_lt_of_ge (hbound.trans
      ((mul_le_mul_of_nonneg_left (add_le_add htiltSmall hcenterSmall) hc.le).trans
        hnum.le)) htarget
  have hmeasure := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hunion : uniformLaw.real (B ∪ (Tbad ∪ Cbad)) ≤
      uniformLaw.real B + uniformLaw.real Tbad + uniformLaw.real Cbad := by
    calc
      _ ≤ uniformLaw.real B + uniformLaw.real (Tbad ∪ Cbad) :=
        measureReal_union_le _ _
      _ ≤ uniformLaw.real B +
          (uniformLaw.real Tbad + uniformLaw.real Cbad) :=
        add_le_add le_rfl (measureReal_union_le _ _)
      _ = _ := by ring
  have htargetEq :
      {u | u ∈ finiteSurvival l n H ∧ u ∈ localSurvival l ∧
        finiteSafeCutoff l n H u ≤ A n ∧
        ∃ z ∈ Kset n,
          ε < ∫ v, ‖finiteShiftedRankProfile l n H (u, v) (A n) z -
            localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw} =
      {u | u ∈ S ∧ ∃ z ∈ Kset n,
        ε < ∫ v, ‖finiteShiftedRankProfile l n H (u, v) (A n) z -
          localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw} := by
    ext u
    simp only [S, mem_ofPred_eq]
    tauto
  rw [htargetEq]
  exact lt_of_le_of_lt (hmeasure.trans hunion) (by linarith)

theorem uniform_finiteShifted_localLimit_shrinking_tilts_conditional_moment
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    (Kset : ℕ → Set ℂ) (hK : ∀ n, IsCompact (Kset n))
    (hxK : ∀ n, (x : ℂ) ∈ Kset n)
    (hdiam : Tendsto (fun n ↦ Metric.diam (Kset n)) atTop (𝓝 0)) :
    ∃ p ∈ Ioc (1 : ℝ) 2, ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
        uniformLaw.real {u | u ∈ finiteSurvival l n ⌊T * n⌋₊ ∧
          u ∈ localSurvival l ∧
          finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ A n ∧
          ∃ z ∈ Kset n,
            ε < ∫ v, ‖finiteShiftedRankProfile l n ⌊T * n⌋₊
              (u, v) (A n) z -
              localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw} < δ := by
  obtain ⟨q, hq, η, hη, ρ, hρ, hw, p, hp, hpdef, h⟩ :=
    uniform_finiteShifted_localLimit_shrinking_tilts_conditional_moment_with_window
      hI hl₀ hT hparams hIlower hx A hA hAH Kset hK hxK hdiam
  exact ⟨p, hp, h⟩

/-- At the paper's observation horizon, the finite safe cutoff is automatic.
This is the simultaneous small-complex-tilt conditional moment estimate on
the common count and parent coupling. -/
theorem uniform_finiteShifted_localLimit_horizon_shrinking_tilts_conditional_moment
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (Kset : ℕ → Set ℂ) (hK : ∀ n, IsCompact (Kset n))
    (hxK : ∀ n, (x : ℂ) ∈ Kset n)
    (hdiam : Tendsto (fun n ↦ Metric.diam (Kset n)) atTop (𝓝 0)) :
    ∃ p ∈ Ioc (1 : ℝ) 2, ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
        uniformLaw.real {u | u ∈ finiteSurvival l n ⌊T * n⌋₊ ∧
          u ∈ localSurvival l ∧
          ∃ z ∈ Kset n,
            ε < ∫ v, ‖finiteShiftedRankProfile l n ⌊T * n⌋₊
              (u, v) ⌊T * n⌋₊ z -
              localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw} < δ := by
  let A : ℕ → ℕ := fun n ↦ ⌊T * n⌋₊
  have hA : Tendsto A atTop atTop :=
    tendsto_nat_floor_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hT)
  obtain ⟨p, hp, h⟩ :=
    uniform_finiteShifted_localLimit_shrinking_tilts_conditional_moment
      hI hl₀ hT hparams hIlower hx A hA (fun n ↦ le_rfl)
      Kset hK hxK hdiam
  refine ⟨p, hp, ?_⟩
  intro ε hε δ hδ
  obtain ⟨N, hN⟩ := h ε hε δ hδ
  refine ⟨N, ?_⟩
  intro n hn l hl
  convert hN n hn l hl using 1
  congr 1
  ext u
  simp only [A, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hfin, hloc, hz⟩
    exact ⟨hfin, hloc, finiteSafeCutoff_le_horizon _ _ _ _, hz⟩
  · rintro ⟨hfin, hloc, _, hz⟩
    exact ⟨hfin, hloc, hz⟩

end HeightPaper.CountCoupling
