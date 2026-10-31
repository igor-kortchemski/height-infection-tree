module

public import HeightPaper.Probability.FiniteLocalProfileIntegrated

/-! # Finite-to-local comparison on a common complex neighborhood -/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal BigOperators

namespace HeightPaper.CountCoupling

/-- A compact admissible real tilt set has a common complex neighborhood on
which the actual finite epidemic profile approaches the local analytic limit,
uniformly over a compact parameter family. -/
theorem uniform_finiteLocalProfile_compact_disk_comparison
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    {K : Set ℝ} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKd : K ⊆ Ioo 0 (profileRoot l₀))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ t > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real (finiteLocalProfileBad l n ⌊T * n⌋₊
        (⋃ x ∈ K, closedBall (x : ℂ) t) ε) < δ := by
  classical
  choose r hr hcmp using fun x : K =>
    exists_uniform_finiteLocalProfile_comparison_disk hI hl₀ hT hparams hIlower
      (hKd x.property)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℝ) (r x / 4))
    (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩,
      mem_ball_self (div_pos (hr ⟨x, hx⟩) (by norm_num))⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hy, _⟩ := mem_iUnion.mp hy
    exact ⟨y, hy⟩
  let t : ℝ := s.inf' hsne (fun x => r x / 4)
  have ht : 0 < t := (Finset.lt_inf'_iff hsne).mpr (fun x _ =>
    div_pos (hr x) (by norm_num))
  have hd : 0 < δ / ((s.card : ℝ) + 1) := by positivity
  choose N hN using fun x : K => hcmp x ε hε (δ / ((s.card : ℝ) + 1)) hd
  refine ⟨t, ht, s.sup' hsne N, ?_⟩
  intro n hn l hl
  let E : K → Set ((ℕ → ℝ) × (ℕ → ℝ)) := fun x =>
    finiteLocalProfileBad l n ⌊T * n⌋₊ (closedBall ((x : ℝ) : ℂ) (r x)) ε
  have hsub : finiteLocalProfileBad l n ⌊T * n⌋₊
      (⋃ x ∈ K, closedBall (x : ℂ) t) ε ⊆ ⋃ x ∈ s, E x := by
    rintro q ⟨hq, hbad⟩
    rcases hbad with hbad | ⟨z, hz, he⟩
    · obtain ⟨x, hx⟩ := hsne
      exact mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, hq, Or.inl hbad⟩⟩
    · obtain ⟨y, hy⟩ := mem_iUnion.mp hz
      obtain ⟨hy, hzy⟩ := mem_iUnion.mp hy
      obtain ⟨x, hx⟩ := mem_iUnion.mp (hs hy)
      obtain ⟨hx, hyx⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, hq, Or.inr ⟨z, ?_, he⟩⟩⟩
      have hyxC : dist (y : ℂ) ((x : ℝ) : ℂ) < r x / 4 := by
        simpa only [mem_ball, Complex.isometry_ofReal.dist_eq] using hyx
      have hzt : dist z (y : ℂ) ≤ t := mem_closedBall.mp hzy
      have htr : t ≤ r x / 4 := Finset.inf'_le _ hx
      exact mem_closedBall.mpr (by linarith [dist_triangle z (y : ℂ) ((x : ℝ) : ℂ)])
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
