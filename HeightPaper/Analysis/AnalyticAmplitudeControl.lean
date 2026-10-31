module

public import Mathlib.Analysis.Complex.Schwarz

/-!
# Variation of an analytic normalizer residual

A bounded analytic residual has a deterministic modulus of continuity at the
real saddle. Multiplying by a profile close to its limiting central value
therefore preserves the central approximation, without moving the residual
outside the oscillatory integral or assuming that it converges.
-/

@[expose] public section

open Metric Set

namespace HeightPaper

/-- A centered form of the Schwarz estimate that only needs a norm bound. -/
theorem analytic_norm_sub_center_le {c z : ℂ} {R M : ℝ} (hR : 0 < R)
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball c R))
    (hbound : ∀ w ∈ ball c R, ‖G w‖ ≤ M) (hz : z ∈ ball c R) :
    ‖G z - G c‖ ≤ (2 * M / R) * ‖z - c‖ := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hmaps : MapsTo G (ball c R) (closedBall (G c) (2 * M)) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hbound w hw, hbound c hc])
  simpa only [dist_eq_norm] using Complex.dist_le_div_mul_dist_of_mapsTo_ball hG hmaps hz

/-- The two errors in the corrected saddle amplitude: profile convergence
and analytic residual variation. The central residual may vary with time. -/
theorem analytic_product_amplitude_error {c z : ℂ} {R M η : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball c R))
    (hbound : ∀ w ∈ ball c R, ‖G w‖ ≤ M) (hz : z ∈ ball c R)
    {A L : ℂ} (hclose : ‖A - L‖ ≤ η) :
    ‖A * G z - L * G c‖ ≤ η * M + ‖L‖ * (2 * M / R) * ‖z - c‖ := by
  have he : A * G z - L * G c = (A - L) * G z + L * (G z - G c) := by ring
  rw [he]
  calc
    _ ≤ ‖A - L‖ * ‖G z‖ + ‖L‖ * ‖G z - G c‖ := by
      simpa only [norm_mul] using norm_add_le ((A - L) * G z) (L * (G z - G c))
    _ ≤ η * M + ‖L‖ * ((2 * M / R) * ‖z - c‖) := by
      apply add_le_add
      · calc
          _ = ‖G z‖ * ‖A - L‖ := mul_comm _ _
          _ ≤ M * η := mul_le_mul (hbound z hz) hclose (norm_nonneg _) hM
          _ = _ := mul_comm _ _
      · exact mul_le_mul_of_nonneg_left (analytic_norm_sub_center_le hR hG hbound hz) (norm_nonneg _)
    _ = _ := by ring

/-- Upper bounds for the amplitude and its central value use only upper
bounds for the profile and residual. -/
theorem product_amplitude_norm_le {A L G : ℂ} {K M η : ℝ}
    (hK : ‖L‖ ≤ K) (_hM : 0 ≤ M) (hG : ‖G‖ ≤ M) (hclose : ‖A - L‖ ≤ η) :
    ‖A * G‖ ≤ (K + η) * M := by
  have hA : ‖A‖ ≤ K + η := by
    calc
      _ = ‖(A - L) + L‖ := by rw [sub_add_cancel]
      _ ≤ ‖A - L‖ + ‖L‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  rw [norm_mul]
  exact mul_le_mul hA hG (norm_nonneg _) (by linarith [norm_nonneg A])

end HeightPaper
