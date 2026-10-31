module

public import HeightPaper.Probability.LocalProfileAnalyticModulus
public import HeightPaper.Probability.LocalProfileCompactStability

/-! # Compact real-tilt modulus of the local analytic limit -/

@[expose] public section

open MeasureTheory Set Metric
open scoped Topology BigOperators

namespace HeightPaper.CountCoupling

/-- Each admissible real point has a deterministic disk on which the limit is
analytic almost surely and bounded in probability uniformly in the parameter. -/
theorem exists_localProfile_analytic_upper_disk {l₀ x : ℝ} (hl₀ : 1 < l₀)
    (hx : x ∈ Ioo 0 (profileRoot l₀)) :
    ∃ r > (0 : ℝ),
      (∀ l ≥ l₀, ∀ n : ℕ, ∀ᵐ q ∂birthParentLaw,
        (∀ i, 0 < (localWalk l q.1 i : ℝ)) →
          DifferentiableOn ℂ (localUnshiftedRankProfileLimit l n q) (ball (x : ℂ) r)) ∧
      (∀ δ > (0 : ℝ), ∃ B > (0 : ℝ), ∀ l ≥ l₀, ∀ n : ℕ,
        birthParentLaw.real {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
          ∃ z ∈ closedBall (x : ℂ) r,
            B < ‖localUnshiftedRankProfileLimit l n q z‖} < δ) := by
  obtain ⟨p, hp, η, hη, ρ, hρ, hw⟩ :=
    exists_localProfile_unshifted_moment_disk hl₀ hx.1 hx.2
  have hr : 0 ≤ ρ / 4 := by positivity
  have hrR : ρ / 4 < ρ / 2 := by linarith
  have hRρ : ρ / 2 < ρ := by linarith
  have hright : ∀ z ∈ closedBall (x : ℂ) (ρ / 2), 1 ≤ (Complex.exp z).re := by
    intro z hz
    exact (hw l₀ le_rfl z ((mem_closedBall.mp hz).trans_lt hRρ)).1.le
  have hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η :=
    fun l hl z hz => (hw l hl z hz).2
  refine ⟨ρ / 4, by positivity, ?_, ?_⟩
  · intro l hl n
    exact localUnshiftedRankProfileLimit_joint_ae_differentiable_disk
      (hl₀.trans_le hl) hp.1 hp.2.le hη hr hrR hRρ hright (hwindow l hl) n
  · intro δ hδ
    exact localProfile_unshifted_disk_upper_tight hl₀ hp.1 hp.2.le hη
      hr hrR hRρ hright hwindow hδ

/-- The local limit has a stochastic modulus simultaneously at every point
of a compact interior real-tilt set, uniformly in the epidemic parameter. -/
theorem localProfile_unshifted_compact_modulus_uniform {l₀ : ℝ} (hl₀ : 1 < l₀)
    {K : Set ℝ} (hK : IsCompact K) (hKd : K ⊆ Ioo 0 (profileRoot l₀))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ t > (0 : ℝ), ∀ l ≥ l₀, ∀ n : ℕ,
      birthParentLaw.real {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
        ∃ x ∈ K, ∃ z ∈ closedBall (x : ℂ) t,
          ε < ‖localUnshiftedRankProfileLimit l n q z -
            localUnshiftedRankProfileLimit l n q (x : ℂ)‖} < δ := by
  classical
  by_cases hKne : K.Nonempty
  swap
  · refine ⟨1, by norm_num, ?_⟩
    intro l hl n
    have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    simpa only [he, mem_empty_iff_false, false_and, exists_false, and_false,
      Set.ofPred_false, measureReal_empty] using hδ
  choose r hr hana hupper using fun x : K =>
    exists_localProfile_analytic_upper_disk hl₀ (hKd x.property)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℝ) (r x / 4))
    (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩,
      mem_ball_self (div_pos (hr ⟨x, hx⟩) (by norm_num))⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hy, _⟩ := mem_iUnion.mp hy
    exact ⟨y, hy⟩
  have hd : 0 < δ / ((s.card : ℝ) + 1) := by positivity
  choose B hB hBtight using fun x : K => hupper x (δ / ((s.card : ℝ) + 1)) hd
  let t : ℝ := s.inf' hsne (fun x => min (r x / 4) (ε * r x / (16 * B x)))
  have ht : 0 < t := (Finset.lt_inf'_iff hsne).mpr (fun x _ => by
    exact lt_min (div_pos (hr x) (by norm_num))
      (div_pos (mul_pos hε (hr x)) (mul_pos (by norm_num) (hB x))))
  refine ⟨t, ht, ?_⟩
  intro l hl n
  let E : K → Set ((ℕ → ℝ) × (ℕ → ℝ)) := fun x =>
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ z ∈ closedBall ((x : ℝ) : ℂ) (r x),
        B x < ‖localUnshiftedRankProfileLimit l n q z‖}
  have hAE : ∀ᵐ q ∂birthParentLaw, ∀ x ∈ s,
      (∀ i, 0 < (localWalk l q.1 i : ℝ)) →
        DifferentiableOn ℂ (localUnshiftedRankProfileLimit l n q)
          (ball ((x : ℝ) : ℂ) (r x)) :=
    (ae_ball_iff s.countable_toSet).mpr (fun x _ => hana x l hl n)
  have hsub : ∀ᵐ q ∂birthParentLaw,
      q ∈ {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
        ∃ x ∈ K, ∃ z ∈ closedBall (x : ℂ) t,
          ε < ‖localUnshiftedRankProfileLimit l n q z -
            localUnshiftedRankProfileLimit l n q (x : ℂ)‖} →
      q ∈ ⋃ x ∈ s, E x := by
    filter_upwards [hAE] with q hq
    rintro ⟨hqsurv, y, hy, z, hz, hbad⟩
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hs hy)
    obtain ⟨hx, hyx⟩ := mem_iUnion.mp hx
    by_contra hnot
    have hnotE : q ∉ E x := by
      intro he
      exact hnot (mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, he⟩⟩)
    have hbound : ∀ w ∈ ball ((x : ℝ) : ℂ) (r x),
        ‖localUnshiftedRankProfileLimit l n q w‖ ≤ B x := by
      intro w hw
      exact le_of_not_gt (fun hh => hnotE ⟨hqsurv, w, ball_subset_closedBall hw, hh⟩)
    have hyxC : dist (y : ℂ) ((x : ℝ) : ℂ) < r x / 4 := by
      simpa only [mem_ball, Complex.isometry_ofReal.dist_eq] using hyx
    have hball : ball (y : ℂ) (r x / 2) ⊆ ball ((x : ℝ) : ℂ) (r x) := by
      intro w hw
      have htri := dist_triangle w (y : ℂ) ((x : ℝ) : ℂ)
      have hwy : dist w (y : ℂ) < r x / 2 := hw
      exact mem_ball.mpr (by linarith [hr x])
    have hdiff := analytic_norm_sub_center_le (half_pos (hr x))
      ((hq x hx hqsurv).mono hball) (fun w hw => hbound w (hball hw))
      (show z ∈ ball (y : ℂ) (r x / 2) by
        have hzt : dist z (y : ℂ) ≤ t := mem_closedBall.mp hz
        have htr : t ≤ r x / 4 :=
          (Finset.inf'_le _ hx).trans (min_le_left _ _)
        exact mem_ball.mpr (by linarith [hr x]))
    have hzt : ‖z - (y : ℂ)‖ ≤ t := by
      simpa only [dist_eq_norm] using (mem_closedBall.mp hz)
    have htr : t ≤ ε * r x / (16 * B x) :=
      (Finset.inf'_le _ hx).trans (min_le_right _ _)
    have hcoef : 0 ≤ 2 * B x / (r x / 2) := by positivity [hr x, hB x]
    have hsmall : 2 * B x / (r x / 2) * t ≤ ε / 4 := by
      have hh := mul_le_mul_of_nonneg_left htr hcoef
      have heq : 2 * B x / (r x / 2) * (ε * r x / (16 * B x)) = ε / 4 := by
        have hrnz : r x ≠ 0 := ne_of_gt (hr x)
        have hBnz : B x ≠ 0 := ne_of_gt (hB x)
        field_simp [hrnz, hBnz]
        ring
      rw [heq] at hh
      exact hh
    have hle : ‖localUnshiftedRankProfileLimit l n q z -
        localUnshiftedRankProfileLimit l n q (y : ℂ)‖ ≤ ε :=
      (hdiff.trans ((mul_le_mul_of_nonneg_left hzt hcoef).trans hsmall)).trans
        (by linarith)
    exact (not_lt_of_ge hle) hbad
  have hm : birthParentLaw {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ x ∈ K, ∃ z ∈ closedBall (x : ℂ) t,
        ε < ‖localUnshiftedRankProfileLimit l n q z -
          localUnshiftedRankProfileLimit l n q (x : ℂ)‖} ≤
      birthParentLaw (⋃ x ∈ s, E x) := measure_mono_ae hsub
  have hh := (ENNReal.toReal_mono (measure_ne_top _ _) hm).trans
    (measureReal_biUnion_finset_le s E)
  have hsum : (∑ x ∈ s, birthParentLaw.real (E x)) ≤
      (s.card : ℝ) * (δ / ((s.card : ℝ) + 1)) := by
    calc
      _ ≤ ∑ _x ∈ s, δ / ((s.card : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro x hx
        exact (hBtight x l hl n).le
      _ = _ := by simp
  have hnum : (s.card : ℝ) * (δ / ((s.card : ℝ) + 1)) < δ := by
    have he : (δ / ((s.card : ℝ) + 1)) * ((s.card : ℝ) + 1) = δ :=
      div_mul_cancel₀ δ (by positivity)
    nlinarith
  exact hh.trans_lt (hsum.trans_lt hnum)

end HeightPaper.CountCoupling
