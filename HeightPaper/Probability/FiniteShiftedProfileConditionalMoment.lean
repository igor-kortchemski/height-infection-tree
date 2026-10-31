module

public import HeightPaper.Probability.FiniteShiftedProfileMovingModulus

/-!
# Conditional small-tilt moments of the finite shifted profile

The profile modulus in joint probability and a strictly higher conditional
moment imply the source's conditional lower-moment modulus at moving times.
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

open Model

/-- The actual finite shifted profile has a vanishing conditional moment of
its small-tilt difference, uniformly over compact rate families and shrinking
compact tilt sets.  The lower moment order is chosen strictly below the order
available in the summable complex window. -/
theorem uniform_finiteShiftedProfile_shrinking_tilts_conditional_moment
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x q η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (hq : q ∈ Ioc (1 : ℝ) 2) (hη : 0 < η)
    (hr : 0 < r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ q * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z q ≤ -1 - η)
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    (Kset : ℕ → Set ℂ) (hK : ∀ n, IsCompact (Kset n))
    (hxK : ∀ n, (x : ℂ) ∈ Kset n)
    (hdiam : Tendsto (fun n ↦ Metric.diam (Kset n)) atTop (𝓝 0))
    {p : ℝ} (hp : 0 < p) (hpq : p < q)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real {u | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u i) ∧
        finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ A n ∧
        ∃ z ∈ Kset n,
          ε < ∫ v, ‖finiteShiftedRankProfile l n ⌊T * n⌋₊ (u, v) (A n) z -
            finiteShiftedRankProfile l n ⌊T * n⌋₊ (u, v) (A n) (x : ℂ)‖ ^ p
            ∂uniformLaw} < δ := by
  have hhalf : 0 < δ / 2 := by positivity
  obtain ⟨C, hC, Nmom, hmom⟩ :=
    finiteShiftedTiltMoment_strictDecay_uniform hI hT hparams hη hhalf
  obtain ⟨a, B, δtail, ha, haB, hδtail, hnum⟩ :=
    exists_conditional_moment_truncation hp hpq hε (C := C)
  have hjoint : 0 < δ * δtail / 2 := by positivity
  obtain ⟨Nprob, hprob⟩ :=
    uniform_finiteShiftedProfile_shrinking_tilts_probability hI hl₀ hT
      hparams hIlower hx hq hη hr hrR hRρ hright hwindow
      A hA hAH Kset hK hxK hdiam ha hjoint
  obtain ⟨Ndiam, hdiamN⟩ := eventually_atTop.mp
    (hdiam.eventually (Iio_mem_nhds hr))
  obtain ⟨NA, hAN⟩ := eventually_atTop.mp
    (hA.eventually (eventually_ge_atTop 1))
  refine ⟨max Nmom (max Nprob (max Ndiam NA)), ?_⟩
  intro n hn l hl
  have hnM : Nmom ≤ n := (le_max_left _ _).trans hn
  have hnP : Nprob ≤ n := (le_max_left _ _).trans
    ((le_max_right _ _).trans hn)
  have hnD : Ndiam ≤ n := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnA : NA ≤ n := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hcenter := hwindow (l : ℝ) (hIlower l hl) (x : ℂ)
    (by simpa using (hr.trans hrR).trans hRρ)
  have hcenter0 : 0 ≤ (x : ℂ).re := (hcenter).1
  have hcenter2 : (x : ℂ).re ≤ 2 * profileRoot l := by
    obtain ⟨_, hxroot, _, _⟩ := hcenter
    linarith
  have hcenterDecay : complexProfileMomentExponent l (x : ℂ) q ≤ -1 - η :=
    hcenter.2.2.2
  have hwindowK (z : ℂ) (hz : z ∈ Kset n) :
      0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
        complexProfileMomentExponent l z q ≤ -1 - η := by
    have hdist : dist z (x : ℂ) < ρ := by
      have hh := Metric.dist_le_diam_of_mem (hK n).isBounded hz (hxK n)
      exact hh.trans_lt ((hdiamN n hnD).trans_le (by linarith : r ≤ ρ))
    obtain ⟨hz0, hzroot, _, hzdecay⟩ :=
      hwindow (l : ℝ) (hIlower l hl) z hdist
    exact ⟨hz0, by linarith, hzdecay⟩
  have hbound := finiteShiftedProfile_conditional_tilt_moment_le_joint_tail
    l n ⌊T * n⌋₊ (A n) (hAN n hnA) (hAH n)
    (Kset n) (x : ℂ) η C a B p q δtail ε
    hcenter0 hcenter2 hq hcenterDecay hwindowK
    ha haB hp.le hpq hδtail hnum
  have hmoment := hmom n hnM l hl
  have hjointProb := hprob n hnP l hl
  have htail : birthParentLaw.real {r | ((∀ i ≤ ⌊T * n⌋₊,
      0 < finiteWalk l n r.1 i) ∧
      finiteSafeCutoff l n ⌊T * n⌋₊ r.1 ≤ A n) ∧ ∃ z ∈ Kset n,
        a < ‖finiteShiftedRankProfile l n ⌊T * n⌋₊ r (A n) z -
          finiteShiftedRankProfile l n ⌊T * n⌋₊ r (A n) (x : ℂ)‖} <
      δ * δtail / 2 := by
    simpa only [and_assoc] using hjointProb
  have htailDiv : birthParentLaw.real {r | ((∀ i ≤ ⌊T * n⌋₊,
      0 < finiteWalk l n r.1 i) ∧
      finiteSafeCutoff l n ⌊T * n⌋₊ r.1 ≤ A n) ∧ ∃ z ∈ Kset n,
        a < ‖finiteShiftedRankProfile l n ⌊T * n⌋₊ r (A n) z -
          finiteShiftedRankProfile l n ⌊T * n⌋₊ r (A n) (x : ℂ)‖} / δtail <
      δ / 2 := (div_lt_iff₀ hδtail).mpr (by linarith)
  exact lt_of_le_of_lt hbound (by linarith)

/-- For every admissible real tilt one can choose a moment order in the
paper's range before the error tolerances, uniformly over a compact rate
family.  This is the finite uniform-parent version of the small-tilt lemma. -/
theorem exists_uniform_finiteShiftedProfile_conditional_tilt_order
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀))
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop)
    (hAH : ∀ n, A n ≤ ⌊T * n⌋₊)
    (Kset : ℕ → Set ℂ) (hK : ∀ n, IsCompact (Kset n))
    (hxK : ∀ n, (x : ℂ) ∈ Kset n)
    (hdiam : Tendsto (fun n ↦ Metric.diam (Kset n)) atTop (𝓝 0)) :
    ∃ p ∈ Ioc (1 : ℝ) 2, ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
        uniformLaw.real {u | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u i) ∧
          finiteSafeCutoff l n ⌊T * n⌋₊ u ≤ A n ∧
          ∃ z ∈ Kset n,
            ε < ∫ v, ‖finiteShiftedRankProfile l n ⌊T * n⌋₊ (u, v) (A n) z -
              finiteShiftedRankProfile l n ⌊T * n⌋₊ (u, v) (A n) (x : ℂ)‖ ^ p
              ∂uniformLaw} < δ := by
  obtain ⟨q, hq, η, hη, ρ, hρ, hw⟩ :=
    exists_localProfile_unshifted_moment_disk hl₀ hx.1 hx.2
  let p : ℝ := (1 + q) / 2
  have hp : 0 < p := by dsimp [p]; linarith [hq.1]
  have hpq : p < q := by dsimp [p]; linarith [hq.1]
  have hpRange : p ∈ Ioc (1 : ℝ) 2 := by
    dsimp [p]
    constructor <;> linarith [hq.1, hq.2]
  have hr : 0 < ρ / 4 := by positivity
  have hrR : ρ / 4 < ρ / 2 := by linarith
  have hRρ : ρ / 2 < ρ := by linarith
  have hright : ∀ z ∈ closedBall (x : ℂ) (ρ / 2),
      1 ≤ (Complex.exp z).re := by
    intro z hz
    exact (hw l₀ le_rfl z ((mem_closedBall.mp hz).trans_lt hRρ)).1.le
  have hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ q * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z q ≤ -1 - η :=
    fun l hl z hz ↦ (hw l hl z hz).2
  refine ⟨p, hpRange, ?_⟩
  intro ε hε δ hδ
  exact uniform_finiteShiftedProfile_shrinking_tilts_conditional_moment
    hI hl₀ hT hparams hIlower hx ⟨hq.1, hq.2.le⟩ hη
    hr hrR hRρ hright hwindow A hA hAH Kset hK hxK hdiam
    hp hpq hε hδ

end HeightPaper.CountCoupling
