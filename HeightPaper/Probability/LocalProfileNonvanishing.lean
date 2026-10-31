module

public import HeightPaper.Probability.RankProfileNonvanishing
public import HeightPaper.Probability.LocalProfilePositive

/-!
# The canonical local profile has no real zero

The count-word event is chosen before the entire real interval. The parent
draws are the independent uniforms whose full trajectory law was identified
with the prescribed tree process. This proof uses the paper's finite-reset
argument, positive mean, and a closed-zero-set zero–one argument.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace HeightPaper.CountCoupling

/-- The full simultaneous nonvanishing assertion on the concrete parent
sampler, with one conditional probability-one event for every real tilt. -/
theorem localAnalyticProfileLimit_ae_nonzero_all_real {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
      ∀ᵐ v ∂uniformLaw, ∀ x ∈ Ioo (0 : ℝ) (profileRoot l),
        localAnalyticProfileLimit l n u
          (Model.rankState (localBirth l u) (Model.initial n) v) (x : ℂ) ≠ 0 := by
  filter_upwards [localProfile_ae_real_domain_convergence hl,
    localAnalyticProfileLimit_ae_pos_all_real hl] with u hdomain hpositive
  intro hs n
  let events := localBirth l u
  let s₀ := Model.initial n
  let J := localSafeCutoff l u
  let L := fun v (x : ℝ) => localAnalyticProfileLimit l n u
    (Model.rankState events s₀ v) (x : ℂ)
  have hlim : ∀ᵐ v ∂uniformLaw,
      TendstoLocallyUniformlyOn
        (fun m => Model.rankProfileAtReal events s₀ J v (J + 2 ^ m)) (L v)
          atTop (Ioo (0 : ℝ) (profileRoot l)) ∧
      ContinuousOn (L v) (Ioo (0 : ℝ) (profileRoot l)) := by
    have hh := hdomain hs n
    rw [← Model.rankTrajectory_law (localBirth l u) (Model.initial n)] at hh
    exact ae_of_ae_map (Model.measurable_rankTrajectory events s₀).aemeasurable hh
  have hpoint (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) :
      ∀ᵐ v ∂uniformLaw, L v x ≠ 0 := by
    have hh := hpositive hs x hx.1 hx.2 n
    rw [← Model.rankTrajectory_law (localBirth l u) (Model.initial n)] at hh
    have hp := ae_of_ae_map (Model.measurable_rankTrajectory events s₀).aemeasurable hh
    filter_upwards [hp] with v hv
    intro he
    have hz : (L v x).re = 0 := congrArg Complex.re he
    exact (ne_of_gt hv) hz
  have htimes : Tendsto (fun m : ℕ => J + 2 ^ m) atTop atTop := by
    apply tendsto_atTop_mono (fun m => Nat.le_add_left (2 ^ m) J)
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))
  have hpos : ∀ j, 0 < Model.prescribedWalk events (Model.infectious s₀) j := by
    intro j
    simp only [s₀, Model.infectious_initial]
    apply prescribedWalk_local_pos (H := j) (fun i _ => ?_) le_rfl
    exact_mod_cast hs i
  exact Model.rankProfile_limit_ae_nonzero events s₀ J isOpen_Ioo
    (fun x hx => hx.1.le) _ htimes hpos L hlim hpoint

/-- The same simultaneous event gives real, strictly positive values. -/
theorem localAnalyticProfileLimit_ae_positive_all_real {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
      ∀ᵐ v ∂uniformLaw, ∀ x ∈ Ioo (0 : ℝ) (profileRoot l),
        (localAnalyticProfileLimit l n u
          (Model.rankState (localBirth l u) (Model.initial n) v) (x : ℂ)).im = 0 ∧
        0 < (localAnalyticProfileLimit l n u
          (Model.rankState (localBirth l u) (Model.initial n) v) (x : ℂ)).re := by
  filter_upwards [localProfile_ae_real_domain_convergence hl,
    localAnalyticProfileLimit_ae_nonzero_all_real hl] with u hdomain hnonzero
  intro hs n
  have hh := hdomain hs n
  rw [← Model.rankTrajectory_law (localBirth l u) (Model.initial n)] at hh
  have hlim := ae_of_ae_map
    (Model.measurable_rankTrajectory (localBirth l u) (Model.initial n)).aemeasurable hh
  filter_upwards [hlim, hnonzero hs n] with v hv hn
  intro x hx
  have ht := hv.1.tendsto_at hx
  have hnn (m : ℕ) := Model.prescribedNormalizedProfile_ofReal_nonneg
    (Real.one_le_exp_iff.mpr hx.1.le) (localBirth l u) (Model.initial n) (localSafeCutoff l u)
    (localSafeCutoff l u + 2 ^ m)
    (Model.rankState (localBirth l u) (Model.initial n) v (localSafeCutoff l u + 2 ^ m))
  simp only [Complex.ofReal_exp] at hnn
  have him := (isClosed_eq Complex.continuous_im continuous_const).mem_of_tendsto ht
    (Eventually.of_forall (fun m => (hnn m).1))
  have hre := ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp ht)
    (Eventually.of_forall (fun m => (hnn m).2))
  refine ⟨him, ?_⟩
  by_contra hnot
  have hz := le_antisymm (le_of_not_gt hnot) hre
  exact hn x hx (Complex.ext hz him)

/-- The zero set in the source lemma is in fact empty, hence countable. -/
theorem localAnalyticProfileLimit_ae_countable_real_zeros {l : ℝ} (hl : 1 < l) :
    ∀ᵐ u ∂uniformLaw, (∀ i, 0 < (localWalk l u i : ℝ)) → ∀ n : ℕ,
      ∀ᵐ v ∂uniformLaw, Set.Countable {x : ℝ | x ∈ Ioo (0 : ℝ) (profileRoot l) ∧
        localAnalyticProfileLimit l n u
          (Model.rankState (localBirth l u) (Model.initial n) v) (x : ℂ) = 0} := by
  filter_upwards [localAnalyticProfileLimit_ae_nonzero_all_real hl] with u hu
  intro hs n
  filter_upwards [hu hs n] with v hv
  have he : {x : ℝ | x ∈ Ioo (0 : ℝ) (profileRoot l) ∧
        localAnalyticProfileLimit l n u
          (Model.rankState (localBirth l u) (Model.initial n) v) (x : ℂ) = 0} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    exact fun x hx => hv x hx.1 hx.2
  rw [he]
  exact Set.countable_empty

end HeightPaper.CountCoupling
