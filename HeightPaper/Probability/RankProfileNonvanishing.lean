module

public import HeightPaper.Probability.RankProfileZeroEvents
public import HeightPaper.Probability.ClosedSetZeroOne

/-!
# Simultaneous nonvanishing of the parent-rank profile limit

The measurable finite-profile tail event detects a zero on each compact set.
The closed-set zero–one theorem then upgrades pointwise nonvanishing to one
probability-one event for the entire real domain.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace HeightPaper.Model

theorem rankProfile_limit_compact_zero_event (events : ℕ → Bool) (s₀ : State) (J : ℕ)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : ∀ x ∈ K, 0 ≤ x)
    (times : ℕ → ℕ) (htimes : Tendsto times atTop atTop)
    (hpos : ∀ j, 0 < prescribedWalk events (infectious s₀) j)
    (L : (ℕ → ℝ) → ℝ → ℂ)
    (hlim : ∀ᵐ v ∂CountCoupling.uniformLaw,
      ContinuousOn (L v) K ∧ TendstoUniformlyOn
        (fun m => rankProfileAtReal events s₀ J v (times m)) (L v) atTop K) :
    NullMeasurableSet {v | ∃ x ∈ K, L v x = 0} CountCoupling.uniformLaw ∧
      (CountCoupling.uniformLaw {v | ∃ x ∈ K, L v x = 0} = 0 ∨
        CountCoupling.uniformLaw {v | ∃ x ∈ K, L v x = 0} = 1) := by
  have heq : {v | ∃ x ∈ K, L v x = 0} =ᵐ[CountCoupling.uniformLaw]
      rankProfileZeroEvent events s₀ J K times := by
    filter_upwards [hlim] with v hv
    exact propext (exists_zero_iff_tendsto_normInfOn_zero hK hv.1 hv.2)
  refine ⟨(measurableSet_rankProfileZeroEvent events s₀ J K times hK0 hpos).nullMeasurableSet.congr
    heq.symm, ?_⟩
  rw [measure_congr heq]
  exact rankProfileZeroEvent_zero_one events s₀ J hK hK0 times htimes hpos

/-- This theorem uses the actual independent uniform parent ranks. The only
limit hypotheses are local uniform convergence, continuity and pointwise
nonvanishing; there is no assumed simultaneous positivity. -/
theorem rankProfile_limit_ae_nonzero (events : ℕ → Bool) (s₀ : State) (J : ℕ)
    {D : Set ℝ} (hD : IsOpen D) (hD0 : ∀ x ∈ D, 0 ≤ x)
    (times : ℕ → ℕ) (htimes : Tendsto times atTop atTop)
    (hpos : ∀ j, 0 < prescribedWalk events (infectious s₀) j)
    (L : (ℕ → ℝ) → ℝ → ℂ)
    (hlim : ∀ᵐ v ∂CountCoupling.uniformLaw,
      TendstoLocallyUniformlyOn
        (fun m => rankProfileAtReal events s₀ J v (times m)) (L v) atTop D ∧
      ContinuousOn (L v) D)
    (hpoint : ∀ x ∈ D, ∀ᵐ v ∂CountCoupling.uniformLaw, L v x ≠ 0) :
    ∀ᵐ v ∂CountCoupling.uniformLaw, ∀ x ∈ D, L v x ≠ 0 := by
  let : LocallyCompactSpace D := hD.locallyCompactSpace
  have hcompact (K : Set D) (hK : IsCompact K) :
      NullMeasurableSet {v | ∃ x ∈ K, L v x = 0} CountCoupling.uniformLaw ∧
        (CountCoupling.uniformLaw {v | ∃ x ∈ K, L v x = 0} = 0 ∨
          CountCoupling.uniformLaw {v | ∃ x ∈ K, L v x = 0} = 1) := by
    let K' : Set ℝ := Subtype.val '' K
    have hK' : IsCompact K' := hK.image continuous_subtype_val
    have hKD : K' ⊆ D := by rintro x ⟨y, _, rfl⟩; exact y.property
    have hlim' : ∀ᵐ v ∂CountCoupling.uniformLaw,
        ContinuousOn (L v) K' ∧ TendstoUniformlyOn
          (fun m => rankProfileAtReal events s₀ J v (times m)) (L v) atTop K' := by
      filter_upwards [hlim] with v hv
      exact ⟨hv.2.mono hKD,
        (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK').mp (hv.1.mono hKD)⟩
    have hh := rankProfile_limit_compact_zero_event events s₀ J hK'
      (fun x hx => hD0 x (hKD hx)) times htimes hpos L hlim'
    have heq : {v | ∃ x ∈ K', L v x = 0} = {v | ∃ x ∈ K, L v x = 0} := by
      ext v
      simp only [K', mem_ofPred_eq, exists_mem_image]
    rwa [heq] at hh
  have hh := ae_forall_ne_of_zero_one_compact_zeroSet_hits
    (μ := CountCoupling.uniformLaw) (fun v (x : D) => L v x) (0 : ℂ)
    (hlim.mono (fun v hv => continuousOn_iff_continuous_domRestrict.mp hv.2))
    (fun x => hpoint x x.property)
    (fun K hK => (hcompact K hK).1) (fun K hK => (hcompact K hK).2)
  filter_upwards [hh] with v hv
  exact fun x hx => hv ⟨x, hx⟩

end HeightPaper.Model
