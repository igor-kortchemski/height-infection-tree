module

public import HeightPaper.Probability.LocalProfileUniformLimit
public import HeightPaper.Model.RankProfileBound
public import HeightPaper.Probability.FiniteLocalProfileConvergence

/-! # Parameter stability and tight bounds for the canonical local profile -/

@[expose] public section

open MeasureTheory Complex Metric Set Filter
open scoped Topology ENNReal BigOperators

namespace HeightPaper.CountCoupling

open Model

theorem localBirth_disagreement_probability_le {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (i : ℕ) :
    uniformLaw.real {u | localBirth a u i ≠ localBirth b u i} ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · have hba : b ≤ a := le_of_not_ge hab
    have hh := this hb ha hba
    simpa only [ne_comm, abs_sub_comm] using hh
  have hthreshold := birthThreshold_mono ha hab
  have heq : {u | localBirth a u i ≠ localBirth b u i} =
      {u | birthThreshold a < u i ∧ u i ≤ birthThreshold b} := by
    ext u
    simp only [mem_ofPred_eq, localBirth, ne_eq, decide_eq_decide]
    constructor
    · intro h
      by_cases hua : u i ≤ birthThreshold a
      · exact False.elim (h ⟨fun _ ↦ hua.trans hthreshold, fun _ ↦ hua⟩)
      · exact ⟨lt_of_not_ge hua, by tauto⟩
    · rintro ⟨hua, hub⟩ he
      exact (not_le_of_gt hua) (he.mpr hub)
  rw [heq, uniformLaw_interval_real i (birthThreshold_nonneg ha)
    hthreshold (birthThreshold_le_one hb), abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
  exact birthThreshold_sub_le ha hab

theorem localBirth_prefix_disagreement_probability_le {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (K : ℕ) :
    uniformLaw.real {u | ∃ i < K, localBirth a u i ≠ localBirth b u i} ≤
      (K : ℝ) * |a - b| := by
  have heq : {u | ∃ i < K, localBirth a u i ≠ localBirth b u i} =
      ⋃ i ∈ Finset.range K, {u | localBirth a u i ≠ localBirth b u i} := by
    ext u
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, hne⟩
      exact ⟨i, hi, hne⟩
    · rintro ⟨i, hi, hne⟩
      exact ⟨i, hi, hne⟩
  rw [heq]
  apply (measureReal_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range K, |a - b| :=
      Finset.sum_le_sum (fun i _ ↦ localBirth_disagreement_probability_le ha hb i)
    _ = _ := by simp

/-- Uniform upper tightness follows from one deterministic finite-prefix
bound and the actual uniform joint tail theorem. -/
theorem localProfile_unshifted_disk_upper_tight {l₀ x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hr : 0 ≤ r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ B > (0 : ℝ), ∀ l ≥ l₀, ∀ n : ℕ,
      birthParentLaw.real {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
        ∃ z ∈ closedBall (x : ℂ) r, B < ‖localUnshiftedRankProfileLimit l n q z‖} < δ := by
  obtain ⟨A, _, hA⟩ := localProfile_unshifted_disk_limit_tail_uniform hl₀ hp hp2 hη
    hr hrR hRρ hright hwindow (show (0 : ℝ) < 1 by norm_num) hδ
  let W₀ := Real.exp (x + r)
  have hW₀ : ∀ z ∈ closedBall (x : ℂ) r, ‖Complex.exp z‖ ≤ W₀ := by
    intro z hz
    have hdist := mem_closedBall.mp hz
    have hle : (z - (x : ℂ)).re ≤ ‖z - (x : ℂ)‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    rw [dist_eq_norm] at hdist
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [sub_re, Complex.ofReal_re] at hle
    linarith
  let W := max W₀ 1
  have hW : 1 ≤ W := le_max_right _ _
  refine ⟨W ^ (A + 1) + 1, by positivity, ?_⟩
  intro l hl n
  apply (measureReal_mono (μ := birthParentLaw) (show _ ⊆
    localUnshiftedProfileDiskLimitBad l n A (closedBall (x : ℂ) r) 1 from ?_)).trans_lt
    (hA l hl n A le_rfl)
  rintro q ⟨hs, z, hz, he⟩
  refine ⟨hs, z, hz, ?_⟩
  have hnorm : ‖localUnshiftedRankProfile l n q A z‖ ≤ W ^ (A + 1) := by
    apply norm_rank_unshifted_profile_le hW
      ((hW₀ z hz).trans (le_max_left _ _))
      (hright z (closedBall_subset_closedBall hrR.le hz))
  have ht := norm_le_norm_add_norm_sub
    (localUnshiftedRankProfile l n q A z) (localUnshiftedRankProfileLimit l n q z)
  have hdif : 1 < ‖localUnshiftedRankProfileLimit l n q z -
      localUnshiftedRankProfile l n q A z‖ := by
    by_contra h
    have hle : ‖localUnshiftedRankProfileLimit l n q z -
        localUnshiftedRankProfile l n q A z‖ ≤ 1 := le_of_not_gt h
    rw [norm_sub_rev] at hle
    linarith [he, ht, hnorm]
  simpa only [norm_sub_rev] using hdif

theorem localWalk_eq_of_birth_prefix {a b : ℝ} (u : ℕ → ℝ) {A k : ℕ}
    (he : ∀ i < A, localBirth a u i = localBirth b u i) (hk : k ≤ A) :
    localWalk a u k = localWalk b u k := by
  unfold localWalk
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [he i ((Finset.mem_range.mp hi).trans_le hk)]

def localProfileParameterBad (a b : ℝ) (n : ℕ) (K : Set ℂ) (ε : ℝ) :
    Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {q | (∀ i, 0 < (localWalk a q.1 i : ℝ)) ∧
    (¬(∀ i, 0 < (localWalk b q.1 i : ℝ)) ∨ ∃ z ∈ K,
      ε < ‖localUnshiftedRankProfileLimit a n q z - localUnshiftedRankProfileLimit b n q z‖)}

/-- The canonical unshifted local profile is uniformly continuous in
probability in the epidemic parameter on a common near-real disk. Survival
disagreement is included in the error event. -/
theorem localProfile_unshifted_disk_parameter_stability {l₀ x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hr : 0 ≤ r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ t > (0 : ℝ), ∀ a ≥ l₀, ∀ b ≥ l₀, |a - b| < t → ∀ n : ℕ,
      birthParentLaw.real (localProfileParameterBad a b n (closedBall (x : ℂ) r) ε) < δ := by
  have hquarter : 0 < δ / 4 := by positivity
  obtain ⟨A₀, hA₀, htail⟩ := localProfile_unshifted_disk_limit_tail_uniform hl₀ hp hp2 hη
    hr hrR hRρ hright hwindow (half_pos hε) hquarter
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((lateLowerFailure_tendsto hl₀).eventually (Iio_mem_nhds hquarter))
  let A := max A₀ N
  have hA : 1 ≤ A := hA₀.trans (le_max_left _ _)
  refine ⟨δ / (4 * ((A : ℝ) + 1)), by positivity, ?_⟩
  intro a ha b hb hab n
  let P : Set (ℕ → ℝ) := {u | ∃ i < A, localBirth a u i ≠ localBirth b u i}
  let S := lateLowerFailure l₀ A
  let F := localUnshiftedProfileDiskLimitBad a n A (closedBall (x : ℂ) r) (ε / 2)
  let G := localUnshiftedProfileDiskLimitBad b n A (closedBall (x : ℂ) r) (ε / 2)
  have hP : birthParentLaw.real {q | q.1 ∈ P} < δ / 4 := by
    apply (birthParentLaw_real_fst_le P).trans_lt
    apply (localBirth_prefix_disagreement_probability_le (by linarith) (by linarith) A).trans_lt
    have hh := (lt_div_iff₀ (by positivity : 0 < 4 * ((A : ℝ) + 1))).mp hab
    nlinarith [abs_nonneg (a - b)]
  have hS : birthParentLaw.real {q | q.1 ∈ S} < δ / 4 :=
    (birthParentLaw_real_fst_le S).trans_lt (hN A (le_max_right _ _))
  have hF : birthParentLaw.real F < δ / 4 := htail a ha n A (le_max_left _ _)
  have hG : birthParentLaw.real G < δ / 4 := htail b hb n A (le_max_left _ _)
  have hsub : localProfileParameterBad a b n (closedBall (x : ℂ) r) ε ⊆
      ({q | q.1 ∈ P} ∪ {q | q.1 ∈ S}) ∪ (F ∪ G) := by
    rintro q ⟨hs, hbad⟩
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or] at hnot
    have hprefix : ∀ i < A, localBirth a q.1 i = localBirth b q.1 i := by
      intro i hi
      by_contra hh
      exact hnot.1.1 ⟨i, hi, hh⟩
    have hsb : ∀ i, 0 < (localWalk b q.1 i : ℝ) := by
      intro i
      by_cases hi : i ≤ A
      · rw [← localWalk_eq_of_birth_prefix q.1 hprefix hi]
        exact hs i
      · have hAi : A ≤ i := by omega
        have hlo : localDrift l₀ / 2 * i ≤ (localWalk l₀ q.1 i : ℝ) :=
          le_of_not_gt (fun hh ↦ hnot.1.2 ⟨i, hAi, hh⟩)
        have hip : (0 : ℝ) < i := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < A) hAi)
        exact (mul_pos (half_pos (localDrift_pos hl₀)) hip).trans_le
          (hlo.trans (Int.cast_le.mpr (localWalk_mono (by linarith) hb q.1 i)))
    obtain ⟨z, hz, he⟩ := hbad.resolve_left (not_not.mpr hsb)
    have hf := le_of_not_gt (fun h ↦ hnot.2.1 ⟨hs, z, hz, h⟩)
    have hg := le_of_not_gt (fun h ↦ hnot.2.2 ⟨hsb, z, hz, h⟩)
    have heq := localUnshiftedRankProfile_congr_birth_prefix n A q.1 q.2 hprefix z
    have he' : ε < ‖localUnshiftedRankProfileLimit a n q z -
        localUnshiftedRankProfileLimit b n q z‖ := by
      simpa only [norm_sub_rev] using he
    have ht := norm_sub_le_norm_sub_add_norm_sub (localUnshiftedRankProfileLimit a n q z)
      (localUnshiftedRankProfile a n q A z) (localUnshiftedRankProfileLimit b n q z)
    have hf' : ‖localUnshiftedRankProfileLimit a n q z -
        localUnshiftedRankProfile a n q A z‖ ≤ ε / 2 := by
      simpa only [norm_sub_rev] using hf
    have hg' : ‖localUnshiftedRankProfile a n q A z -
        localUnshiftedRankProfileLimit b n q z‖ ≤ ε / 2 := by
      simpa only [heq] using hg
    nlinarith [ht, he', hf', hg']
  have hh := (measureReal_mono (μ := birthParentLaw) hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _)
      (measureReal_union_le _ _)))
  linarith

/-- Every admissible real tilt has one deterministic disk carrying both
uniform upper tightness and uniform parameter stability. -/
theorem exists_localProfile_stable_disk {l₀ x : ℝ} (hl₀ : 1 < l₀)
    (hx : 0 < x) (hxr : x < profileRoot l₀) :
    ∃ r > (0 : ℝ),
      (∀ δ > (0 : ℝ), ∃ B > (0 : ℝ), ∀ l ≥ l₀, ∀ n : ℕ,
        birthParentLaw.real {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
          ∃ z ∈ closedBall (x : ℂ) r, B < ‖localUnshiftedRankProfileLimit l n q z‖} < δ) ∧
      (∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ), ∃ t > (0 : ℝ),
        ∀ a ≥ l₀, ∀ b ≥ l₀, |a - b| < t → ∀ n : ℕ,
          birthParentLaw.real (localProfileParameterBad a b n (closedBall (x : ℂ) r) ε) < δ) := by
  obtain ⟨p, hp, η, hη, ρ, hρ, hwindow⟩ := exists_localProfile_unshifted_moment_disk hl₀ hx hxr
  have hr : 0 ≤ ρ / 4 := by positivity
  have hrR : ρ / 4 < ρ / 2 := by linarith
  have hRρ : ρ / 2 < ρ := by linarith
  have hright : ∀ z ∈ closedBall (x : ℂ) (ρ / 2), 1 ≤ (Complex.exp z).re := by
    intro z hz
    exact (hwindow l₀ le_rfl z ((mem_closedBall.mp hz).trans_lt hRρ)).1.le
  have hm : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η :=
    fun l hl z hz ↦ (hwindow l hl z hz).2
  refine ⟨ρ / 4, by positivity, ?_, ?_⟩
  · intro δ hδ
    exact localProfile_unshifted_disk_upper_tight hl₀ hp.1 hp.2.le hη hr hrR hRρ hright hm hδ
  · intro ε hε δ hδ
    exact localProfile_unshifted_disk_parameter_stability hl₀ hp.1 hp.2.le hη
      hr hrR hRρ hright hm hε hδ

end HeightPaper.CountCoupling
