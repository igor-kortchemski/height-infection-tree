module

public import HeightPaper.Probability.LocalAnalyticPositiveMean
public import HeightPaper.Probability.RankProfileZeroEvents

/-!
# Pointwise positivity of the canonical local profile

The zero event at a real tilt is invariant under changing finitely many parent
uniforms. The exact infinite trajectory-law identity transfers its zero-one
alternative to the prescribed tree process. The proved positive mean then
excludes a probability-one zero event.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace HeightPaper.Model

/-- Singleton compact zero events transfer from the independent parent ranks
to any measurable cofinal limit under the actual prescribed trajectory law. -/
theorem prescribedTrajectory_profile_limit_zero_one (events : ℕ → Bool) (n J : ℕ)
    {x : ℝ} (hx : 0 ≤ x) (times : ℕ → ℕ) (htimes : Tendsto times atTop atTop)
    (hpos : ∀ i, 0 < prescribedWalk events 1 i)
    (F : (ℕ → State) → ℂ) (hF : Measurable F)
    (hlim : ∀ᵐ ω ∂prescribedTrajectoryMeasure events (initial n),
      Tendsto (fun m ↦ prescribedNormalizedProfile (Complex.exp (x : ℂ)) events
        (initial n) J (times m) (ω (times m))) atTop (𝓝 (F ω))) :
    prescribedTrajectoryMeasure events (initial n) {ω | F ω = 0} = 0 ∨
      prescribedTrajectoryMeasure events (initial n) {ω | F ω = 0} = 1 := by
  have hpos' : ∀ i, 0 < prescribedWalk events (infectious (initial n)) i := by
    simpa only [infectious_initial] using hpos
  have hlimrank : ∀ᵐ u ∂CountCoupling.uniformLaw,
      Tendsto (fun m ↦ rankProfileAtReal events (initial n) J u (times m) x)
        atTop (𝓝 (F (rankState events (initial n) u))) := by
    have hh := hlim
    rw [← rankTrajectory_law events (initial n)] at hh
    exact ae_of_ae_map (measurable_rankTrajectory events (initial n)).aemeasurable hh
  have heq : prescribedTrajectoryMeasure events (initial n) {ω | F ω = 0} =
      CountCoupling.uniformLaw (rankProfileZeroEvent events (initial n) J {x} times) := by
    rw [← rankTrajectory_law events (initial n),
      Measure.map_apply (measurable_rankTrajectory events (initial n))
        (measurableSet_eq_fun hF measurable_const)]
    apply measure_congr
    filter_upwards [hlimrank] with u hu
    apply propext
    have hh := exists_zero_iff_tendsto_normInfOn_zero (K := {x}) isCompact_singleton
      (F := fun m y ↦ rankProfileAtReal events (initial n) J u (times m) y)
      (f := fun _ ↦ F (rankState events (initial n) u)) continuousOn_const
      (tendstoUniformlyOn_singleton_iff_tendsto.mpr hu)
    simpa [rankProfileZeroEvent] using hh
  rw [heq]
  exact rankProfileZeroEvent_zero_one events (initial n) J isCompact_singleton
    (by intro y hy; simpa only [Set.mem_singleton_iff.mp hy] using hx) times htimes hpos'

/-- For a fixed surviving word, any a.s. and Lp real-profile limit is strictly
positive almost surely. Its mean is derived from the finite product identity. -/
theorem prescribedTrajectory_profile_lp_limit_ae_pos {x p : ℝ} (hx : 0 ≤ x) (hp : 1 ≤ p)
    (events : ℕ → Bool) (n J : ℕ)
    (hpos : ∀ i, 0 < prescribedWalk events 1 i)
    (F : (ℕ → State) → ℂ) (hF : Measurable F)
    (hlim : ∀ᵐ ω ∂prescribedTrajectoryMeasure events (initial n),
      Tendsto (fun k ↦ prescribedNormalizedProfile (Complex.exp (x : ℂ)) events (initial n)
        J (J + k) (ω (J + k))) atTop (𝓝 (F ω)))
    (hLp : Tendsto (fun k ↦ eLpNorm
      ((fun ω ↦ prescribedNormalizedProfile (Complex.exp (x : ℂ)) events (initial n)
        J (J + k) (ω (J + k))) - F) (ENNReal.ofReal p)
        (prescribedTrajectoryMeasure events (initial n))) atTop (𝓝 0)) :
    ∀ᵐ ω ∂prescribedTrajectoryMeasure events (initial n), 0 < (F ω).re := by
  have hm := prescribedTrajectory_profile_limit_nonneg_mean
    (Real.one_le_exp_iff.mpr hx) hp events n J hpos F
    (by simpa only [Complex.ofReal_exp] using hlim)
    (by simpa only [Complex.ofReal_exp] using hLp)
  apply ae_re_pos_of_nonneg_mean_pos_zero_one _ F hF hm.1 hm.2.2
  exact prescribedTrajectory_profile_limit_zero_one events n J hx (fun k ↦ J + k)
    (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat J) hpos F hF hlim

end HeightPaper.Model

namespace HeightPaper.CountCoupling

/-- One almost-sure count-word event works for every real tilt in the positive
profile interval. Each corresponding canonical value is strictly positive
under the actual conditional parent-trajectory law. -/
theorem localAnalyticProfileLimit_ae_pos_all_real {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) →
      ∀ x : ℝ, 0 < x → x < profileRoot l → ∀ n : ℕ,
        ∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
          0 < (localAnalyticProfileLimit l n u ω (x : ℂ)).re := by
  filter_upwards [localProfile_ae_canonical_analytic_limit_all_real hl,
    localAnalyticProfileLimit_ae_nonneg_mean_all_real hl] with u hu hmean
  intro hs x hx hxr n
  obtain ⟨R, hR, hcanonical⟩ := hu hs x hx hxr
  have hlim : ∀ᵐ ω ∂Model.prescribedTrajectoryMeasure (localBirth l u) (Model.initial n),
      Tendsto (fun m ↦ Model.prescribedNormalizedProfile (Complex.exp (x : ℂ))
        (localBirth l u) (Model.initial n) (localSafeCutoff l u) (localSafeCutoff l u + 2 ^ m)
        (ω (localSafeCutoff l u + 2 ^ m))) atTop
        (𝓝 (localAnalyticProfileLimit l n u ω (x : ℂ))) := by
    filter_upwards [(hcanonical n).1] with ω hω
    exact (hω 0 le_rfl hR).1.tendsto_at (by simp)
  have hpos : ∀ i, 0 < Model.prescribedWalk (localBirth l u) 1 i := by
    intro i
    apply prescribedWalk_local_pos (H := i) _ le_rfl
    intro j _
    exact_mod_cast hs j
  have hmeas : Measurable (fun ω ↦ localAnalyticProfileLimit l n u ω (x : ℂ)) :=
    Model.measurable_prescribedAnalyticProfileLimit_eval (localBirth l u) (Model.initial n)
      (localSafeCutoff l u) (x : ℂ)
  have hm := hmean hs x hx hxr n
  apply ae_re_pos_of_nonneg_mean_pos_zero_one _ _ hmeas hm.1 hm.2.2
  apply Model.prescribedTrajectory_profile_limit_zero_one (localBirth l u) n
    (localSafeCutoff l u) hx.le (fun m ↦ localSafeCutoff l u + 2 ^ m) _ hpos _ hmeas hlim
  simpa only [Nat.add_comm, Function.comp_def] using (tendsto_add_atTop_nat (localSafeCutoff l u)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))

end HeightPaper.CountCoupling
