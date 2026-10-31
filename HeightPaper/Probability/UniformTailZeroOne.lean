module

public import HeightPaper.Probability.UniformWalk
public import Mathlib.Probability.Independence.ZeroOne

/-!
# Finite-change invariant events on the uniform sequence space

A measurable event unchanged by arbitrary alterations of finitely many
coordinates belongs to the literal tail sigma-algebra.  Its probability is
therefore zero or one; no completion or almost-everywhere invariance hypothesis
is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set

namespace HeightPaper.CountCoupling

abbrev uniformCoordinateSpace (k : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  MeasurableSpace.comap (fun u ↦ u k) inferInstance

/-- Replace the initial segment by a fixed value while preserving the tail. -/
def zeroPrefix (N : ℕ) (u : ℕ → ℝ) : ℕ → ℝ :=
  fun k ↦ if N ≤ k then u k else 0

theorem zeroPrefix_eq_tail (N : ℕ) (u : ℕ → ℝ) (k : ℕ) (hk : N ≤ k) :
    zeroPrefix N u k = u k := by simp only [zeroPrefix, ite_eq_left hk]

theorem measurable_zeroPrefix_tail (N : ℕ) :
    @Measurable (ℕ → ℝ) (ℕ → ℝ) (⨆ k ≥ N, uniformCoordinateSpace k) inferInstance
      (zeroPrefix N) := by
  let : MeasurableSpace (ℕ → ℝ) := ⨆ k ≥ N, uniformCoordinateSpace k
  apply measurable_pi_iff.mpr
  intro k
  by_cases hk : N ≤ k
  · simp only [zeroPrefix, ite_eq_left hk]
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le k (le_iSup_of_le hk le_rfl)
  · have hm : @Measurable (ℕ → ℝ) ℝ (⨆ k ≥ N, uniformCoordinateSpace k) inferInstance
        (fun _ ↦ 0) := measurable_const
    simpa only [zeroPrefix, ite_eq_right hk] using hm

theorem measurableSet_uniform_tail_of_finite_changes {E : Set (ℕ → ℝ)}
    (hE : MeasurableSet E)
    (hchange : ∀ N u v, (∀ k ≥ N, u k = v k) → (u ∈ E ↔ v ∈ E)) :
    MeasurableSet[limsup uniformCoordinateSpace atTop] E := by
  rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
  intro N
  have he : E = zeroPrefix N ⁻¹' E := by
    ext u
    exact hchange N u (zeroPrefix N u) (fun k hk ↦ (zeroPrefix_eq_tail N u k hk).symm)
  rw [he]
  exact measurable_zeroPrefix_tail N hE

/-- Kolmogorov's zero-one law in the form needed by reset-depth events. -/
theorem uniformLaw_zero_one_of_finite_changes {E : Set (ℕ → ℝ)}
    (hE : MeasurableSet E)
    (hchange : ∀ N u v, (∀ k ≥ N, u k = v k) → (u ∈ E ↔ v ∈ E)) :
    uniformLaw E = 0 ∨ uniformLaw E = 1 := by
  apply measure_zero_or_one_of_measurableSet_limsup_atTop
    (s := uniformCoordinateSpace)
  · intro k
    exact (measurable_pi_apply k).comap_le
  · exact uniformLaw_independent.iIndep
  · exact measurableSet_uniform_tail_of_finite_changes hE hchange

end HeightPaper.CountCoupling
