module

public import HeightPaper.Probability.FiniteLocalProfileConvergence
public import HeightPaper.Probability.LocalProfileUniformLimit

/-! # Finite-to-local profile comparison with the local tail discharged -/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal BigOperators

namespace HeightPaper.CountCoupling

/-- On a common admissible complex disk, the finite epidemic profile at a
macroscopic time approaches the actual local limit uniformly in probability. -/
theorem uniform_finiteLocalProfile_comparison
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hp : p ∈ Ioc (1 : ℝ) 2) (hη : 0 < η)
    (hr : 0 ≤ r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real (finiteLocalProfileBad l n ⌊T * n⌋₊
        (closedBall (x : ℂ) r) ε) < δ := by
  have hfinite : ∀ l ∈ I, ∀ z ∈ closedBall (x : ℂ) R,
      0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η := by
    intro l hl z hz
    obtain ⟨hz0, hzroot, _, hm⟩ :=
      hwindow l (hIlower l hl) z ((mem_closedBall.mp hz).trans_lt hRρ)
    have hroot : 0 ≤ profileRoot l := (profileRoot_pos (hparams l hl).1).le
    exact ⟨hz0, by linarith, hm⟩
  apply uniform_finiteLocalProfile_comparison_of_local_tail hI hT hparams
    (x : ℂ) hr hrR hp hη hfinite
    (fun z hz => hright z (closedBall_subset_closedBall hrR.le hz))
    (fun ε hε δ hδ => ?_) hε hδ
  obtain ⟨A, _, hA⟩ := localProfile_unshifted_disk_limit_tail_uniform
    hl₀ hp.1 hp.2 hη hr hrR hRρ hright hwindow hε hδ
  exact ⟨A, fun l hl j hj => by
    simpa only [localUnshiftedProfileDiskLimitBad, Int.cast_pos] using
      hA l (hIlower l hl) 0 j hj⟩

/-- Each admissible real tilt has a deterministic disk on which the actual
finite-to-local comparison holds uniformly over the parameter compact. -/
theorem exists_uniform_finiteLocalProfile_comparison_disk
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hx : x ∈ Ioo 0 (profileRoot l₀)) :
    ∃ r > (0 : ℝ), ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
        birthParentLaw.real (finiteLocalProfileBad l n ⌊T * n⌋₊
          (closedBall (x : ℂ) r) ε) < δ := by
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
  refine ⟨ρ / 4, by positivity, ?_⟩
  intro ε hε δ hδ
  exact uniform_finiteLocalProfile_comparison hI hl₀ hT hparams hIlower
    ⟨hp.1, hp.2.le⟩ hη hr hrR hRρ hright hwindow hε hδ

/-- The finite epidemic profile approaches the local analytic limit on every
compact real tilt set, uniformly over a compact parameter family. -/
theorem uniform_finiteLocalProfile_compact_comparison
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    {K : Set ℝ} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKd : K ⊆ Ioo 0 (profileRoot l₀))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real (finiteLocalProfileBad l n ⌊T * n⌋₊
        (Complex.ofReal '' K) ε) < δ := by
  classical
  choose r hr hcmp using fun x : K =>
    exists_uniform_finiteLocalProfile_comparison_disk hI hl₀ hT hparams hIlower
      (hKd x.property)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℝ) (r x))
    (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hy, _⟩ := mem_iUnion.mp hy
    exact ⟨y, hy⟩
  have hd : 0 < δ / ((s.card : ℝ) + 1) := by positivity
  choose N hN using fun x : K => hcmp x ε hε (δ / ((s.card : ℝ) + 1)) hd
  refine ⟨s.sup' hsne N, ?_⟩
  intro n hn l hl
  let E : K → Set ((ℕ → ℝ) × (ℕ → ℝ)) := fun x =>
    finiteLocalProfileBad l n ⌊T * n⌋₊ (closedBall ((x : ℝ) : ℂ) (r x)) ε
  have hsub : finiteLocalProfileBad l n ⌊T * n⌋₊ (Complex.ofReal '' K) ε ⊆
      ⋃ x ∈ s, E x := by
    rintro q ⟨hq, hbad⟩
    rcases hbad with hbad | ⟨z, hz, he⟩
    · obtain ⟨x, hx⟩ := hsne
      exact mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, hq, Or.inl hbad⟩⟩
    · obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨x, hx⟩ := mem_iUnion.mp (hs hy)
      obtain ⟨hx, hyx⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, hq, Or.inr ⟨(y : ℂ), ?_, he⟩⟩⟩
      have hh : dist y (x : ℝ) < r x := hyx
      simpa only [mem_closedBall, Complex.isometry_ofReal.dist_eq] using hh.le
  have hh := (measureReal_mono (μ := birthParentLaw) hsub (measure_ne_top _ _)).trans
    (measureReal_biUnion_finset_le s E)
  have hsum : (∑ x ∈ s, birthParentLaw.real (E x)) ≤
      (s.card : ℝ) * (δ / ((s.card : ℝ) + 1)) := by
    calc
      _ ≤ ∑ _x ∈ s, δ / ((s.card : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro x hx
        exact (hN x n ((Finset.le_sup' N hx).trans hn) l hl).le
      _ = _ := by simp
  have hnum : (s.card : ℝ) * (δ / ((s.card : ℝ) + 1)) < δ := by
    have he : (δ / ((s.card : ℝ) + 1)) * ((s.card : ℝ) + 1) = δ :=
      div_mul_cancel₀ δ (by positivity)
    nlinarith
  exact hh.trans_lt (hsum.trans_lt hnum)

end HeightPaper.CountCoupling
