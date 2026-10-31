module

public import HeightPaper.Model.ProfilePathMoments

/-!
# Comparing positive real profile tilts

Jensen's inequality propagates a lower profile estimate from one positive tilt
to a larger tilt. At small nonnegative tilts the normalized profile is at least
one. These are deterministic inputs to a possible finite-moment bootstrap;
no stochastic convergence is asserted here.
-/

@[expose] public section

namespace HeightPaper.Model

noncomputable def realNormalizedLaplace (x : ℝ) (s : State) : ℝ :=
  activeWeight (Real.exp x) s / (infectious s : ℝ)

theorem realNormalizedLaplace_nonneg (x : ℝ) (s : State) :
    0 ≤ realNormalizedLaplace x s :=
  div_nonneg (Finset.sum_nonneg fun _ _ ↦ pow_nonneg (Real.exp_nonneg x) _) (Nat.cast_nonneg _)

theorem one_le_realNormalizedLaplace {x : ℝ} (hx : 0 ≤ x) (s : State)
    (ha : s.active.Nonempty) : 1 ≤ realNormalizedLaplace x s := by
  have hi : (0 : ℝ) < infectious s := by exact_mod_cast ha.card_pos
  apply (le_div_iff₀ hi).mpr
  simp only [one_mul]
  calc
    (infectious s : ℝ) = ∑ _v ∈ s.active, (1 : ℝ) := by simp [infectious]
    _ ≤ activeWeight (Real.exp x) s := by
      apply Finset.sum_le_sum
      intro v _
      exact one_le_pow₀ (Real.one_le_exp_iff.mpr hx)

theorem realNormalizedLaplace_rpow_le (x : ℝ) (s : State) (ha : s.active.Nonempty)
    {p : ℝ} (hp : 1 ≤ p) :
    (realNormalizedLaplace x s) ^ p ≤ realNormalizedLaplace (p * x) s := by
  have h := norm_normalizedLaplace_rpow_le (x : ℂ) s ha hp
  rw [← Complex.ofReal_exp, normalizedActiveWeight_ofReal, Complex.norm_real,
    Real.norm_eq_abs, Complex.ofReal_re] at h
  change |realNormalizedLaplace x s| ^ p ≤ realNormalizedLaplace (p * x) s at h
  rw [abs_of_nonneg (realNormalizedLaplace_nonneg x s)] at h
  exact h

/-- Moving to a larger tilt loses only the explicitly displayed Jensen
exponent. This is useful for lower-bound bootstrap arguments. -/
theorem realNormalizedLaplace_tilt_lower {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (s : State) (ha : s.active.Nonempty) :
    (realNormalizedLaplace x s) ^ (y / x) ≤ realNormalizedLaplace y s := by
  have hp : 1 ≤ y / x := (le_div_iff₀ hx).mpr (by simpa using hxy)
  simpa only [div_mul_cancel₀ _ hx.ne'] using realNormalizedLaplace_rpow_le x s ha hp

end HeightPaper.Model
