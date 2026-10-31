module

public import HeightPaper.Probability.FiniteLocalShiftedMoment
public import HeightPaper.Probability.FiniteProfileMomentStrictDecay

/-!
# Uniform higher moments for the finite-to-local comparison

At a fixed admissible positive real tilt, a single conditional higher
moment constant controls the finite/local difference outside measurable
count-word exceptions of arbitrarily small probability.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

theorem finiteShifted_localLimit_parent_difference_moment_uniform
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ Ioo (1 : ℝ) 2, ∃ C : ℝ, 0 ≤ C ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
        ∃ B : Set (ℕ → ℝ), MeasurableSet B ∧ uniformLaw.real B < ε ∧
          (∀ᵐ u ∂uniformLaw,
            u ∈ finiteSurvival l n ⌊T * n⌋₊ →
            u ∈ localSurvival l →
            finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ A n →
            u ∉ B →
              Integrable (fun v ↦ ‖finiteShiftedRankProfile l n ⌊T * n⌋₊
                (u, v) (A n) (x : ℂ) -
                localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ q) uniformLaw ∧
              (∫ v, ‖finiteShiftedRankProfile l n ⌊T * n⌋₊
                (u, v) (A n) (x : ℂ) -
                localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ q ∂uniformLaw) ≤ C) := by
  have hthird : 0 < 2 * ε / 3 := by positivity
  obtain ⟨q, hq, η, hη, r, hr, D, hD, K, Clocal, hClocal, hexp, hlocal⟩ :=
    localRankProfileLimit_parentMoment_uniform_tight hl₀ hx hthird
  have hthird' : 0 < ε / 3 := by positivity
  obtain ⟨Cfinite, hCfinite, Nfinite, hfinite⟩ :=
    finiteProfileMoment_strictDecay_uniform hI hT hparams hη hthird'
  obtain ⟨NA, hNA⟩ := eventually_atTop.mp (hA.eventually (eventually_ge_atTop 1))
  let C := (2 : ℝ) ^ (q - 1) * (Cfinite + Clocal)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨q, hq, C, hC, max Nfinite NA, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let B₁ := finiteProfileStrictDecayBad Cfinite η (l : ℝ) n H
  let B₂ := localProfileMomentBad q η r x D (l : ℝ)
  let B₃ : Set (ℕ → ℝ) := {u | K < localSafeCutoff (l : ℝ) u}
  let B := B₁ ∪ (B₂ ∪ B₃)
  have hB : MeasurableSet B :=
    (measurableSet_finiteProfileStrictDecayBad _ _ _ _ _).union
      ((measurableSet_localProfileMomentBad _ _ _ _ _ _).union
        (measurableSet_lt measurable_const (measurable_localSafeCutoff _)))
  obtain ⟨h₂, h₃, hgood⟩ := hlocal (l : ℝ) (hIlower l hl)
  have h₁ := hfinite n ((le_max_left _ _).trans hn) l hl
  have hBsmall : uniformLaw.real B < ε := by
    have hu := measureReal_union_le (μ := uniformLaw) B₁ (B₂ ∪ B₃)
    have hu₂ := measureReal_union_le (μ := uniformLaw) B₂ B₃
    dsimp only [B]
    linarith
  refine ⟨B, hB, hBsmall, ?_⟩
  filter_upwards [hgood] with u hu hs hls hcut hnot
  have hnot₁ : u ∉ B₁ := fun h ↦ hnot (Or.inl h)
  have hnot₂ : u ∉ B₂ := fun h ↦ hnot (Or.inr (Or.inl h))
  have hnot₃ : u ∉ B₃ := fun h ↦ hnot (Or.inr (Or.inr h))
  have hK : localSafeCutoff (l : ℝ) u ≤ K := le_of_not_gt hnot₃
  have hlsreal : ∀ i, 0 < (localWalk (l : ℝ) u i : ℝ) := by
    intro i
    exact_mod_cast hls i
  have hlocalMoment := hu hlsreal hnot₂ hK 0
  have hAn : 1 ≤ A n := hNA n ((le_max_right _ _).trans hn)
  have hroot : profileRoot l₀ ≤ profileRoot (l : ℝ) :=
    profileRoot_mono_supercritical hl₀ (hIlower l hl)
  have hx2 : x ≤ 2 * profileRoot (l : ℝ) := by
    have hrootpos := profileRoot_pos (hparams l hl).1
    linarith [hx.2]
  have hfiniteMoment :
      finiteProfileMoment (Complex.exp (x : ℂ)) q l n H u (A n) ≤ Cfinite := by
    apply le_of_not_gt
    intro hbad
    apply hnot₁
    exact ⟨hs, A n, hAn, hAH n, hcut, (x : ℂ),
      by simpa using hx.1.le, by simpa using hx2,
      q, ⟨hq.1, hq.2.le⟩, hexp (l : ℝ) (hIlower l hl), hbad⟩
  exact finiteShifted_localLimit_parent_difference_moment_le (l : ℝ) n H (A n)
    (hAH n) u (x : ℂ) hq.1.le hfiniteMoment hlocalMoment

end HeightPaper.CountCoupling

namespace HeightPaper.CountCoupling

theorem finiteShifted_localLimit_parent_difference_moment_uniform_of_window
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x q η r : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (hq : q ∈ Ioo (1 : ℝ) 2) (hη : 0 < η) (hr : 0 < r)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < r →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ q * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z q ≤ -1 - η)
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
        ∃ B : Set (ℕ → ℝ), MeasurableSet B ∧ uniformLaw.real B < ε ∧
          (∀ᵐ u ∂uniformLaw,
            u ∈ finiteSurvival l n ⌊T * n⌋₊ →
            u ∈ localSurvival l →
            finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ A n →
            u ∉ B →
              Integrable (fun v ↦ ‖finiteShiftedRankProfile l n ⌊T * n⌋₊
                (u, v) (A n) (x : ℂ) -
                localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ q) uniformLaw ∧
              (∫ v, ‖finiteShiftedRankProfile l n ⌊T * n⌋₊
                (u, v) (A n) (x : ℂ) -
                localRankProfileLimit l 0 (u, v) (x : ℂ)‖ ^ q ∂uniformLaw) ≤ C) := by
  have hthird : 0 < 2 * ε / 3 := by positivity
  obtain ⟨D, hD, K, Clocal, hClocal, hlocal⟩ :=
    localRankProfileLimit_parentMoment_uniform_tight_of_window
      hl₀ hx hq hη hr hwindow hthird
  have hexp : ∀ l ≥ l₀, complexProfileMomentExponent l (x : ℂ) q ≤ -1 - η := by
    intro l hl
    exact (hwindow l hl (x : ℂ) (by simpa using hr)).2.2.2
  have hthird' : 0 < ε / 3 := by positivity
  obtain ⟨Cfinite, hCfinite, Nfinite, hfinite⟩ :=
    finiteProfileMoment_strictDecay_uniform hI hT hparams hη hthird'
  obtain ⟨NA, hNA⟩ := eventually_atTop.mp (hA.eventually (eventually_ge_atTop 1))
  let C := (2 : ℝ) ^ (q - 1) * (Cfinite + Clocal)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, max Nfinite NA, ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let B₁ := finiteProfileStrictDecayBad Cfinite η (l : ℝ) n H
  let B₂ := localProfileMomentBad q η r x D (l : ℝ)
  let B₃ : Set (ℕ → ℝ) := {u | K < localSafeCutoff (l : ℝ) u}
  let B := B₁ ∪ (B₂ ∪ B₃)
  have hB : MeasurableSet B :=
    (measurableSet_finiteProfileStrictDecayBad _ _ _ _ _).union
      ((measurableSet_localProfileMomentBad _ _ _ _ _ _).union
        (measurableSet_lt measurable_const (measurable_localSafeCutoff _)))
  obtain ⟨h₂, h₃, hgood⟩ := hlocal (l : ℝ) (hIlower l hl)
  have h₁ := hfinite n ((le_max_left _ _).trans hn) l hl
  have hBsmall : uniformLaw.real B < ε := by
    have hu := measureReal_union_le (μ := uniformLaw) B₁ (B₂ ∪ B₃)
    have hu₂ := measureReal_union_le (μ := uniformLaw) B₂ B₃
    dsimp only [B]
    linarith
  refine ⟨B, hB, hBsmall, ?_⟩
  filter_upwards [hgood] with u hu hs hls hcut hnot
  have hnot₁ : u ∉ B₁ := fun h ↦ hnot (Or.inl h)
  have hnot₂ : u ∉ B₂ := fun h ↦ hnot (Or.inr (Or.inl h))
  have hnot₃ : u ∉ B₃ := fun h ↦ hnot (Or.inr (Or.inr h))
  have hK : localSafeCutoff (l : ℝ) u ≤ K := le_of_not_gt hnot₃
  have hlsreal : ∀ i, 0 < (localWalk (l : ℝ) u i : ℝ) := by
    intro i
    exact_mod_cast hls i
  have hlocalMoment := hu hlsreal hnot₂ hK 0
  have hAn : 1 ≤ A n := hNA n ((le_max_right _ _).trans hn)
  have hroot : profileRoot l₀ ≤ profileRoot (l : ℝ) :=
    profileRoot_mono_supercritical hl₀ (hIlower l hl)
  have hx2 : x ≤ 2 * profileRoot (l : ℝ) := by
    have hrootpos := profileRoot_pos (hparams l hl).1
    linarith [hx.2]
  have hfiniteMoment :
      finiteProfileMoment (Complex.exp (x : ℂ)) q l n H u (A n) ≤ Cfinite := by
    apply le_of_not_gt
    intro hbad
    apply hnot₁
    exact ⟨hs, A n, hAn, hAH n, hcut, (x : ℂ),
      by simpa using hx.1.le, by simpa using hx2,
      q, ⟨hq.1, hq.2.le⟩, hexp (l : ℝ) (hIlower l hl), hbad⟩
  exact finiteShifted_localLimit_parent_difference_moment_le (l : ℝ) n H (A n)
    (hAH n) u (x : ℂ) hq.1.le hfiniteMoment hlocalMoment


end HeightPaper.CountCoupling
