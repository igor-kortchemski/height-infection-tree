module

public import HeightPaper.Probability.FiniteLocalShiftedExtendedConditionalMoment
public import HeightPaper.Probability.FiniteLocalShiftedComplexConditionalMoment

/-!
# Uniform convergence of the full-walk extended conditional moment

The higher real-center moment makes the nonnegative extended conditional
expectation finite on a high-probability survival event.  There it agrees
with the ordinary parent integral, uniformly for shrinking complex tilts.
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

namespace HeightPaper.CountCoupling

theorem uniform_finiteShifted_localLimit_horizon_extendedConditionalMoment
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
            ENNReal.ofReal ε < finiteLocalShiftedExtendedMoment
              l n ⌊T * n⌋₊ ⌊T * n⌋₊ z (x : ℂ) p u} < δ := by
  let A : ℕ → ℕ := fun n ↦ ⌊T * n⌋₊
  have hA : Tendsto A atTop atTop :=
    tendsto_nat_floor_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hT)
  obtain ⟨q, hq, η, hη, ρ, hρ, hw, p, hp, hpdef, hreal⟩ :=
    uniform_finiteShifted_localLimit_shrinking_tilts_conditional_moment_with_window
      hI hl₀ hT hparams hIlower hx A hA (fun _ ↦ le_rfl)
      Kset hK hxK hdiam
  refine ⟨p, hp, ?_⟩
  intro ε hε δ hδ
  have hhalf : 0 < δ / 2 := by positivity
  obtain ⟨Nreal, hNreal⟩ := hreal ε hε (δ / 2) hhalf
  obtain ⟨C, hC, Nhigh, hhigh⟩ :=
    finiteShifted_localLimit_parent_difference_moment_uniform_of_window
      hI hl₀ hT hparams hIlower hx hq hη hρ hw A hA
      (fun _ ↦ le_rfl) hhalf
  refine ⟨max Nreal Nhigh, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let S : Set (ℕ → ℝ) :=
    {u | u ∈ finiteSurvival l n H ∧ u ∈ localSurvival l}
  let R : Set (ℕ → ℝ) :=
    {u | u ∈ S ∧ ∃ z ∈ Kset n,
      ε < ∫ v, ‖finiteShiftedRankProfile l n H (u, v) H z -
        localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw}
  obtain ⟨B, hB, hBsmall, hgood⟩ :=
    hhigh n ((le_max_right _ _).trans hn) l hl
  have hRsmall : uniformLaw.real R < δ / 2 := by
    convert hNreal n ((le_max_left _ _).trans hn) l hl using 1
    congr 1
    ext u
    simp only [R, S, H, A, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hfin, hloc⟩, hz⟩
      exact ⟨hfin, hloc, finiteSafeCutoff_le_horizon _ _ _ _, hz⟩
    · rintro ⟨hfin, hloc, _, hz⟩
      exact ⟨⟨hfin, hloc⟩, hz⟩
  have hpq : p < q := by rw [hpdef]; linarith [hq.1]
  have hsub : ∀ᵐ u ∂uniformLaw,
      (u ∈ S ∧ ∃ z ∈ Kset n,
        ENNReal.ofReal ε < finiteLocalShiftedExtendedMoment
          (l : ℝ) n H H z (x : ℂ) p u) → u ∈ B ∪ R := by
    filter_upwards [hgood] with u hu ⟨hSu, z, hz, hext⟩
    by_cases hBu : u ∈ B
    · exact Or.inl hBu
    right
    obtain ⟨hfin, hloc⟩ := hSu
    obtain ⟨hqi, _⟩ := hu hfin hloc (finiteSafeCutoff_le_horizon _ _ _ _) hBu
    have hmeasCenter : Measurable (fun v ↦
        finiteShiftedRankProfile (l : ℝ) n H (u, v) H (x : ℂ) -
          localRankProfileLimit l 0 (u, v) (x : ℂ)) :=
      ((measurable_finiteShiftedRankProfile (l : ℝ) n H H le_rfl (x : ℂ)).sub
        (measurable_localRankProfileLimit (l : ℝ) 0 (x : ℂ))).comp
          (measurable_const.prodMk measurable_id)
    have hpi : Integrable (fun v ↦
        ‖finiteShiftedRankProfile (l : ℝ) n H (u, v) H (x : ℂ) -
          localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p) uniformLaw :=
      integrable_norm_rpow_of_le hmeasCenter.aestronglyMeasurable
        (zero_lt_one.trans hp.1).le (zero_lt_one.trans hq.1).le hpq.le hqi
    have htiltInt : Integrable (fun v ↦
        ‖finiteShiftedRankProfile (l : ℝ) n H (u, v) H z -
          finiteShiftedRankProfile l n H (u, v) H (x : ℂ)‖ ^ p) uniformLaw :=
      finiteShiftedRankProfile_parent_difference_integrable
        (l : ℝ) n H H u z (x : ℂ) p
    have hf : Measurable (fun v ↦
        finiteShiftedRankProfile (l : ℝ) n H (u, v) H z -
          finiteShiftedRankProfile l n H (u, v) H (x : ℂ)) :=
      ((measurable_finiteShiftedRankProfile (l : ℝ) n H H le_rfl z).sub
        (measurable_finiteShiftedRankProfile (l : ℝ) n H H le_rfl (x : ℂ))).comp
          (measurable_const.prodMk measurable_id)
    have hg : Measurable (fun v ↦
        localRankProfileLimit l 0 (u, v) (x : ℂ) -
          finiteShiftedRankProfile (l : ℝ) n H (u, v) H (x : ℂ)) :=
      ((measurable_localRankProfileLimit (l : ℝ) 0 (x : ℂ)).sub
        (measurable_finiteShiftedRankProfile (l : ℝ) n H H le_rfl (x : ℂ))).comp
          (measurable_const.prodMk measurable_id)
    have hgi : Integrable (fun v ↦
        ‖localRankProfileLimit l 0 (u, v) (x : ℂ) -
          finiteShiftedRankProfile (l : ℝ) n H (u, v) H (x : ℂ)‖ ^ p) uniformLaw := by
      simpa only [norm_sub_rev] using hpi
    have htargetInt : Integrable (fun v ↦
        ‖finiteShiftedRankProfile (l : ℝ) n H (u, v) H z -
          localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p) uniformLaw := by
      convert (Model.integral_norm_sub_rpow_le uniformLaw hp.1.le hf hg
        htiltInt hgi).1 using 1
      ext v
      congr 1
      abel
    have heq : finiteLocalShiftedExtendedMoment
        (l : ℝ) n H H z (x : ℂ) p u =
        ENNReal.ofReal (∫ v, ‖finiteShiftedRankProfile l n H (u, v) H z -
          localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ p ∂uniformLaw) := by
      exact (ofReal_integral_eq_lintegral_ofReal htargetInt
        (ae_of_all _ fun v ↦ Real.rpow_nonneg (norm_nonneg _) _)).symm
    rw [heq] at hext
    have hrealBad := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le).mp hext
    exact ⟨⟨hfin, hloc⟩, z, hz, hrealBad⟩
  have hmeasure := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hunion : uniformLaw.real (B ∪ R) ≤ uniformLaw.real B + uniformLaw.real R :=
    measureReal_union_le _ _
  have htargetEq :
      {u | u ∈ finiteSurvival l n H ∧ u ∈ localSurvival l ∧
        ∃ z ∈ Kset n,
          ENNReal.ofReal ε < finiteLocalShiftedExtendedMoment
            (l : ℝ) n H H z (x : ℂ) p u} =
      {u | u ∈ S ∧ ∃ z ∈ Kset n,
        ENNReal.ofReal ε < finiteLocalShiftedExtendedMoment
          (l : ℝ) n H H z (x : ℂ) p u} := by
    ext u
    simp only [S, mem_ofPred_eq]
    tauto
  rw [htargetEq]
  exact lt_of_le_of_lt (hmeasure.trans hunion) (by linarith)

/-- The local-survival formulation is stronger than the source's statement
with its finite-survival and safe-cutoff indicators. It includes extinction
exactly at the finite observation horizon through the uniform survival
comparison. -/
theorem uniform_finiteShifted_localLimit_horizon_extendedConditionalMoment_localSurvival
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
        uniformLaw.real {u | u ∈ localSurvival l ∧
          ∃ z ∈ Kset n,
            ENNReal.ofReal ε < finiteLocalShiftedExtendedMoment
              l n ⌊T * n⌋₊ ⌊T * n⌋₊ z (x : ℂ) p u} < δ := by
  obtain ⟨p, hp, h⟩ :=
    uniform_finiteShifted_localLimit_horizon_extendedConditionalMoment
      hI hl₀ hT hparams hIlower hx Kset hK hxK hdiam
  refine ⟨p, hp, ?_⟩
  intro ε hε δ hδ
  have hhalf : 0 < δ / 2 := by positivity
  obtain ⟨Nmain, hmain⟩ := h ε hε (δ / 2) hhalf
  obtain ⟨Nsurv, hsurv⟩ :=
    uniform_survival_disagreement hI hT hparams hhalf
  refine ⟨max Nmain Nsurv, ?_⟩
  intro n hn l hl
  let S : Set (ℕ → ℝ) :=
    {u | u ∈ finiteSurvival l n ⌊T * n⌋₊ ∧ u ∈ localSurvival l ∧
      ∃ z ∈ Kset n,
        ENNReal.ofReal ε < finiteLocalShiftedExtendedMoment
          (l : ℝ) n ⌊T * n⌋₊ ⌊T * n⌋₊ z (x : ℂ) p u}
  let D : Set (ℕ → ℝ) :=
    {u | ¬ (u ∈ finiteSurvival l n ⌊T * n⌋₊ ↔ u ∈ localSurvival l)}
  have hS : uniformLaw.real S < δ / 2 :=
    hmain n ((le_max_left _ _).trans hn) l hl
  have hD : uniformLaw.real D < δ / 2 := by
    simpa only [D, finiteSurvival, localSurvival, Set.mem_ofPred_eq] using
      hsurv n ((le_max_right _ _).trans hn) l hl
  have hsub : {u | u ∈ localSurvival l ∧
      ∃ z ∈ Kset n,
        ENNReal.ofReal ε < finiteLocalShiftedExtendedMoment
          (l : ℝ) n ⌊T * n⌋₊ ⌊T * n⌋₊ z (x : ℂ) p u} ⊆ S ∪ D := by
    intro u ⟨hloc, hz⟩
    by_cases hfin : u ∈ finiteSurvival l n ⌊T * n⌋₊
    · exact Or.inl ⟨hfin, hloc, hz⟩
    · exact Or.inr (by simp only [D, mem_ofPred_eq]; tauto)
  exact lt_of_le_of_lt
    ((measureReal_mono hsub).trans (measureReal_union_le S D)) (by linarith)

end HeightPaper.CountCoupling
