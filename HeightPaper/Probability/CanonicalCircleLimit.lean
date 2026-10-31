module

public import HeightPaper.Probability.AnalyticBoundarySeries

/-! # A deterministic measurable-witness criterion for the canonical analytic limit -/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

namespace HeightPaper

/-- The summable boundary witness yields the explicit canonical limit, on
all smaller disks, without any probability-space or measurability premise. -/
theorem analyticSequenceLimit_tendstoUniformlyOn_of_summable_circleL1
    {Ω : Type*} (F : ℕ → Ω → ℂ → ℂ) (ω : Ω) (c : ℂ) {R r : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hF : ∀ m, DifferentiableOn ℂ (F m ω) (closedBall c R))
    (hs : Summable (fun m => circleL1 c R (fun z => F (m + 1) ω z - F m ω z))) :
    TendstoUniformlyOn (fun m => F m ω) (analyticSequenceLimit F ω) atTop (closedBall c r) ∧
      DifferentiableOn ℂ (analyticSequenceLimit F ω) (ball c r) := by
  have hd := fun m => (hF (m + 1)).sub (hF m)
  have hconv := analytic_series_uniform_of_circleL1 hr hrR
    (fun m z => F (m + 1) ω z - F m ω z) hd hs
  have hana := analytic_series_differentiable_of_circleL1 hr hrR
    (fun m z => F (m + 1) ω z - F m ω z) hd hs
  constructor
  · have hconst : TendstoUniformlyOn (fun (_ : ℕ) z => F 0 ω z) (F 0 ω)
        atTop (closedBall c r) := by
      rw [tendstoUniformlyOn_iff]
      intro ε hε
      exact Eventually.of_forall (fun _ _ _ => by simpa using hε)
    have ht := hconst.add hconv
    convert ht using 1
    · ext n z
      simp only [Pi.add_apply]
      rw [Finset.sum_range_sub (fun i => F i ω z)]
      ring
    · rfl
  · exact ((hF 0).mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall hrR.le))).add hana

end HeightPaper
