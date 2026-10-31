module

public import HeightPaper.Probability.LocalProfilePositive
public import HeightPaper.Probability.TreeUniformCoupling
public import HeightPaper.Model.UnshiftedProfile

/-!
# Canonical local profiles on the shared birth-parent space

The unshifted limit divides out the retained cutoff-prefix normalizer. This
preserves the physical profile while avoiding jumps of the auxiliary cutoff
when the epidemic parameter varies.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace HeightPaper.Model

theorem measurable_prescribedNormalizer_exp (z : ℂ) (k : ℕ) :
    Measurable (fun events : ℕ → Bool ↦ prescribedNormalizer (Complex.exp z) events 1 k) := by
  have hh := (measurable_prescribedNormalizedProfile_joint (initial 0) 0 k z).comp
    (measurable_id.prodMk (measurable_const :
      Measurable (fun _ : ℕ → Bool ↦ fun _ : ℕ ↦ initial 0)))
  have hi := hh.inv
  change Measurable (fun events : ℕ → Bool ↦
    (prescribedNormalizedProfile (Complex.exp z) events (initial 0) 0 k (initial 0))⁻¹) at hi
  simpa only [Function.comp_def, prescribedNormalizedProfile, infectious_initial,
    normalizedActiveWeight_initial, prescribedNormalizerFrom_zero, one_div, Pi.inv_apply, inv_inv, id_eq] using hi

end HeightPaper.Model

namespace HeightPaper.CountCoupling

noncomputable def localRankProfileLimit (l : ℝ) (n : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) (z : ℂ) : ℂ :=
  localAnalyticProfileLimit l n q.1
    (Model.rankState (localBirth l q.1) (Model.initial n) q.2) z

noncomputable def localProfilePrefixNormalizer (l : ℝ) (u : ℕ → ℝ) (z : ℂ) : ℂ :=
  Model.prescribedNormalizer (Complex.exp z) (localBirth l u) 1 (localSafeCutoff l u)

noncomputable def localUnshiftedRankProfileLimit (l : ℝ) (n : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) (z : ℂ) : ℂ :=
  localRankProfileLimit l n q z / localProfilePrefixNormalizer l q.1 z

noncomputable def localUnshiftedRankProfile (l : ℝ) (n : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) (k : ℕ) (z : ℂ) : ℂ :=
  Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l q.1) (Model.initial n) 0 k
    (Model.rankState (localBirth l q.1) (Model.initial n) q.2 k)

theorem measurable_localRankProfileLimit (l : ℝ) (n : ℕ) (z : ℂ) :
    Measurable (fun q ↦ localRankProfileLimit l n q z) := by
  have hh := (measurable_localAnalyticProfileLimit_joint l n z).comp
    (measurable_fst.prodMk (measurable_local_rankTrajectory l (Model.initial n)))
  simpa only [localRankProfileLimit, Function.comp_def] using hh

theorem measurable_localProfilePrefixNormalizer (l : ℝ) (z : ℂ) :
    Measurable (fun u ↦ localProfilePrefixNormalizer l u z) := by
  have hm : Measurable (fun p : (ℕ → Bool) × ℕ ↦
      Model.prescribedNormalizer (Complex.exp z) p.1 1 p.2) :=
    measurable_from_prod_countable_left (fun k ↦ Model.measurable_prescribedNormalizer_exp z k)
  exact hm.comp ((Measurable.of_eval (measurable_localBirth l)).prodMk (measurable_localSafeCutoff l))

theorem measurable_localUnshiftedRankProfileLimit (l : ℝ) (n : ℕ) (z : ℂ) :
    Measurable (fun q ↦ localUnshiftedRankProfileLimit l n q z) :=
  (measurable_localRankProfileLimit l n z).div
    ((measurable_localProfilePrefixNormalizer l z).comp measurable_fst)

theorem measurable_localUnshiftedRankProfile (l : ℝ) (n k : ℕ) (z : ℂ) :
    Measurable (fun q ↦ localUnshiftedRankProfile l n q k z) :=
  (Model.measurable_prescribedNormalizedProfile_joint (Model.initial n) 0 k z).comp
    (((Measurable.of_eval (measurable_localBirth l)).comp measurable_fst).prodMk
      (measurable_local_rankTrajectory l (Model.initial n)))

theorem localUnshiftedRankProfile_eq_div_prefix (l : ℝ) (n : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) {k : ℕ} (hk : localSafeCutoff l q.1 ≤ k) (z : ℂ) :
    localUnshiftedRankProfile l n q k z =
      Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l q.1) (Model.initial n)
        (localSafeCutoff l q.1) k (Model.rankState (localBirth l q.1) (Model.initial n) q.2 k) /
      localProfilePrefixNormalizer l q.1 z := by
  exact Model.prescribedNormalizedProfile_zero_eq_div_prefix (Complex.exp z) (localBirth l q.1)
    (Model.initial n) _ hk

theorem norm_localUnshiftedRankProfileLimit_sub_le (l : ℝ) (n : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) {k : ℕ} (hk : localSafeCutoff l q.1 ≤ k)
    {z : ℂ} (hz : 1 ≤ (Complex.exp z).re) :
    ‖localUnshiftedRankProfileLimit l n q z - localUnshiftedRankProfile l n q k z‖ ≤
      ‖localRankProfileLimit l n q z -
        Model.prescribedNormalizedProfile (Complex.exp z) (localBirth l q.1) (Model.initial n)
          (localSafeCutoff l q.1) k (Model.rankState (localBirth l q.1) (Model.initial n) q.2 k)‖ := by
  exact Model.norm_unshifted_limit_difference_le hz (localBirth l q.1) (Model.initial n) _ hk _

theorem localUnshiftedRankProfile_congr_birth_prefix {l l' : ℝ} (n k : ℕ)
    (u v : ℕ → ℝ) (he : ∀ i < k, localBirth l u i = localBirth l' u i) (z : ℂ) :
    localUnshiftedRankProfile l n (u, v) k z = localUnshiftedRankProfile l' n (u, v) k z := by
  unfold localUnshiftedRankProfile Model.prescribedNormalizedProfile
  rw [Model.rankState_congr_events_prefix (Model.initial n) v k he,
    Model.prescribedNormalizerFrom_congr_prefix (Complex.exp z) _ 0 he le_rfl]

theorem exists_disk_re_exp_gt_one {x : ℝ} (hx : 0 < x) :
    ∃ r > (0 : ℝ), ∀ z : ℂ, dist z (x : ℂ) < r → 1 < (Complex.exp z).re := by
  have he : 1 < (Complex.exp (x : ℂ)).re := by
    simpa only [← Complex.ofReal_exp, Complex.ofReal_re] using Real.one_lt_exp_iff.mpr hx
  have hn : {z : ℂ | 1 < (Complex.exp z).re} ∈ 𝓝 (x : ℂ) :=
    (Complex.continuous_re.comp Complex.continuous_exp).continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds he)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  exact ⟨r, hr, fun z hz ↦ hball hz⟩

/-- A deterministic common moment window whose every normalizer prefix has
modulus at least one, so the same estimates apply without a cutoff. -/
theorem exists_localProfile_unshifted_moment_disk {l₀ x : ℝ} (hl₀ : 1 < l₀)
    (hx : 0 < x) (hxr : x < profileRoot l₀) :
    ∃ p ∈ Set.Ioo (1 : ℝ) 2, ∃ η : ℝ, 0 < η ∧ ∃ r > (0 : ℝ),
      ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < r →
        1 < (Complex.exp z).re ∧ 0 ≤ z.re ∧ z.re < profileRoot l ∧
          p * z.re < 2 * profileRoot l ∧ complexProfileMomentExponent l z p ≤ -1 - η := by
  obtain ⟨p, hp, η, hη, r, hr, hwindow⟩ := exists_localProfile_moment_disk hl₀ hx hxr
  obtain ⟨s, hs, hright⟩ := exists_disk_re_exp_gt_one hx
  refine ⟨p, hp, η, hη, min r s, lt_min hr hs, ?_⟩
  intro l hl z hz
  exact ⟨hright z (lt_min_iff.mp hz).2, hwindow l hl z (lt_min_iff.mp hz).1⟩

end HeightPaper.CountCoupling
