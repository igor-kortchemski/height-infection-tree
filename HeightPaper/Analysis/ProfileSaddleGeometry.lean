module

public import HeightPaper.Analysis.ComplexMomentExponent
public import HeightPaper.Analysis.TiltBootstrap
public import Mathlib.Topology.Order.Compact

/-! # Uniform moment margins and the exact saddle lattice -/

@[expose] public section

open Set
open scoped NNReal

namespace HeightPaper

/-- One moment order and one strictly summable margin work simultaneously on
both compact parameter and positive real-tilt sets. -/
theorem exists_uniform_compact_profile_moment_margin {I : Set ℝ≥0} {K : Set ℝ}
    (hI : IsCompact I) (hK : IsCompact K)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ K ⊆ Ioo (0 : ℝ) (profileRoot l)) :
    ∃ p ∈ Ioo (1 : ℝ) 2, ∃ η > 0, ∀ l ∈ I, ∀ x ∈ K,
      complexProfileMomentExponent l (x : ℂ) p ≤ -1 - η := by
  by_cases hIne : I.Nonempty
  swap
  · exact ⟨3 / 2, ⟨by norm_num, by norm_num⟩, 1, by norm_num,
      fun l hl ↦ False.elim (hIne ⟨l, hl⟩)⟩
  by_cases hKne : K.Nonempty
  swap
  · exact ⟨3 / 2, ⟨by norm_num, by norm_num⟩, 1, by norm_num,
      fun _ _ x hx ↦ False.elim (hKne ⟨x, hx⟩)⟩
  obtain ⟨l₀, hl₀, hmin⟩ := hI.exists_isLeast hIne
  obtain ⟨X, hX, hmax⟩ := hK.exists_isGreatest hKne
  obtain ⟨p, hp, η, hη, r, hr, hm⟩ := exists_uniform_complex_profile_moment_decay
    (hparams l₀ hl₀).1 ((hparams l₀ hl₀).2 hX).1.le ((hparams l₀ hl₀).2 hX).2
  refine ⟨p, hp, η, hη, fun l hl x hx ↦ ?_⟩
  have hmono := profileMomentExponent_mono_tilt (hparams l hl).1 hp.1.le
    ((hparams l hl).2 hx).1.le ((hparams l hl).2 hX).1.le (hmax hx)
  change profileMomentExponent l x p ≤ profileMomentExponent l X p at hmono
  rw [← complexProfileMomentExponent_ofReal, ← complexProfileMomentExponent_ofReal] at hmono
  exact hmono.trans (hm l (by exact_mod_cast hmin hl) (X : ℂ) (by simpa using hr))

noncomputable def saddleTilt (γ a : ℝ) (r : ℕ) : ℝ := Real.log ((r : ℝ) / (γ * a))

theorem saddleTilt_eq_of_lattice {γ a x : ℝ} {r : ℕ} (hγ : 0 < γ) (ha : 0 < a)
    (hr : (r : ℝ) = γ * Real.exp x * a) : saddleTilt γ a r = x := by
  unfold saddleTilt
  have he : (r : ℝ) / (γ * a) = Real.exp x := by rw [hr]; field_simp
  rw [he, Real.log_exp]

theorem lattice_eq_of_saddleTilt {γ a : ℝ} {r : ℕ} (hγ : 0 < γ) (ha : 0 < a)
    (hr : 0 < r) : (r : ℝ) = γ * Real.exp (saddleTilt γ a r) * a := by
  rw [saddleTilt, Real.exp_log (div_pos (by exact_mod_cast hr) (mul_pos hγ ha))]
  field_simp

/-- A finite superset of all nonnegative integer heights at real tilts below
`X`; the extra endpoint avoids any rounding convention in the saddle identity. -/
noncomputable def saddleHeightRange (γ a X : ℝ) : Finset ℕ :=
  Finset.range (⌈γ * Real.exp X * a⌉₊ + 1)

theorem mem_saddleHeightRange_of_lattice {γ a X x : ℝ} {r : ℕ}
    (hγ : 0 ≤ γ) (ha : 0 ≤ a) (hx : x ≤ X)
    (hr : (r : ℝ) = γ * Real.exp x * a) : r ∈ saddleHeightRange γ a X := by
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  have hle : (r : ℝ) ≤ ⌈γ * Real.exp X * a⌉₊ := by
    calc
      _ = γ * Real.exp x * a := hr
      _ ≤ γ * Real.exp X * a := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) hγ) ha
      _ ≤ _ := Nat.le_ceil _
  exact_mod_cast hle

theorem saddleHeightRange_card_le {γ a X : ℝ} (hγ : 0 ≤ γ) (ha : 0 ≤ a) :
    ((saddleHeightRange γ a X).card : ℝ) ≤ γ * Real.exp X * a + 2 := by
  simp only [saddleHeightRange, Finset.card_range, Nat.cast_add, Nat.cast_one]
  have hh := Nat.ceil_lt_add_one (show 0 ≤ γ * Real.exp X * a by positivity)
  linarith

end HeightPaper
