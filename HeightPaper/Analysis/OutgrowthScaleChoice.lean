module

public import HeightPaper.Analysis.Critical

/-!
# Strict geometric comparison means near the limiting offspring mean

Both sides of the dangling-tree height estimate use geometric means slightly
above or below the limiting epidemic pressure. Continuity of the logarithmic
height scale supplies the required strict numerical margins.
-/

@[expose] public section

open Filter Set Metric
open scoped Topology

namespace HeightPaper.Model

theorem exists_outgrowth_comparison_means {l f ε : ℝ}
    (hl : 1 < l) (hε : 0 < ε) :
    ∃ mU mL : ℝ,
      offspringMean l < mU ∧ mU < 1 ∧
      0 < mL ∧ mL < offspringMean l ∧
      f / (-Real.log mU) < f / outgrowthRate l + ε ∧
      f / outgrowthRate l - ε < f / (-Real.log mL) := by
  let m := offspringMean l
  have hm : 0 < m := offspringMean_pos hl
  have hm1 : m < 1 := offspringMean_lt_one hl
  have hlog : -Real.log m ≠ 0 := by
    simpa only [outgrowthRate] using (outgrowthRate_pos hl).ne'
  have hcont : ContinuousAt (fun x : ℝ ↦ f / (-Real.log x)) m :=
    continuousAt_const.div ((Real.continuousAt_log hm.ne').neg) hlog
  have hnear : ∀ᶠ x : ℝ in 𝓝 m,
      f / outgrowthRate l - ε < f / (-Real.log x) ∧
      f / (-Real.log x) < f / outgrowthRate l + ε := by
    have h := hcont.tendsto.eventually
      (Ioo_mem_nhds (by linarith : f / outgrowthRate l - ε <
        f / outgrowthRate l)
        (by linarith : f / outgrowthRate l <
          f / outgrowthRate l + ε))
    simpa only [outgrowthRate] using h
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let dU := min (r / 2) ((1 - m) / 2)
  let dL := min (r / 2) (m / 2)
  have hdU : 0 < dU := lt_min (half_pos hr) (half_pos (sub_pos.mpr hm1))
  have hdL : 0 < dL := lt_min (half_pos hr) (half_pos hm)
  have hUr : dU < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hLr : dL < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hU1 : m + dU < 1 := by
    have := min_le_right (r / 2) ((1 - m) / 2)
    dsimp [dU]
    linarith
  have hL0 : 0 < m - dL := by
    have := min_le_right (r / 2) (m / 2)
    dsimp [dL]
    linarith
  have hnearU := hball (show dist (m + dU) m < r by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hdU]
    exact hUr)
  have hnearL := hball (show dist (m - dL) m < r by
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hdL]
    exact hLr)
  exact ⟨m + dU, m - dL, by dsimp [m]; linarith, hU1,
    hL0, by dsimp [m]; linarith, hnearU.2, hnearL.1⟩

end HeightPaper.Model
