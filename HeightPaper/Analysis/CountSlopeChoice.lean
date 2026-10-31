module

public import HeightPaper.Analysis.Parameters

/-! # Sharp count slopes induce arbitrarily close normalizer exponents -/

public section

open Filter Set
open scoped Topology

namespace HeightPaper

/-- The early active-count drift gives exactly the profile growth factor
under the count-to-normalizer coefficient transformation. -/
theorem countSlopeCoefficient_eq_growthFactor {l : ℝ} (hl : 1 < l) :
    (1 + 1 / ((l - 1) / (l + 1))) / 2 = growthFactor l := by
  have h₁ : l - 1 ≠ 0 := (sub_pos.mpr hl).ne'
  have h₂ : l + 1 ≠ 0 := by linarith
  unfold growthFactor
  field_simp
  ring

/-- Lower and upper early-count slopes can be chosen on the correct sides of
the drift while both induced normalizer exponents stay in a prescribed common
neighborhood of the exact profile growth factor. -/
theorem exists_count_slopes_near_growthFactor {l η : ℝ} (hl : 1 < l) (hη : 0 < η) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo < (l - 1) / (l + 1) ∧
      (l - 1) / (l + 1) < hi ∧ hi < 1 ∧
      |(1 + 1 / hi) / 2 - growthFactor l| < η ∧
      |(1 + 1 / lo) / 2 - growthFactor l| < η := by
  let c := (l - 1) / (l + 1)
  have hc : 0 < c := div_pos (sub_pos.mpr hl) (by linarith)
  have hc1 : c < 1 := (div_lt_one (by linarith : 0 < l + 1)).mpr (by linarith)
  have hcont : ContinuousAt (fun x : ℝ ↦ (1 + 1 / x) / 2) c := by
    exact (continuousAt_const.add (continuousAt_const.div continuousAt_id hc.ne')).div_const 2
  have hnear : ∀ᶠ x in 𝓝 c, |(1 + 1 / x) / 2 - growthFactor l| < η := by
    have hh := hcont.tendsto.eventually (Metric.ball_mem_nhds ((1 + 1 / c) / 2) hη)
    have heq : (1 + 1 / c) / 2 = growthFactor l := countSlopeCoefficient_eq_growthFactor hl
    simpa only [Metric.mem_ball, Real.dist_eq, heq] using hh
  obtain ⟨d, hd, hbound⟩ := Metric.eventually_nhds_iff.mp hnear
  let e := min (c / 2) (min ((1 - c) / 2) (d / 2))
  have he : 0 < e := lt_min (half_pos hc) (lt_min (half_pos (sub_pos.mpr hc1)) (half_pos hd))
  have hec : e ≤ c / 2 := min_le_left _ _
  have he1 : e ≤ (1 - c) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hed : e < d := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hd)
  refine ⟨c - e, c + e, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
  · apply hbound
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos he]
    exact hed
  · apply hbound
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos he]
    exact hed

end HeightPaper
