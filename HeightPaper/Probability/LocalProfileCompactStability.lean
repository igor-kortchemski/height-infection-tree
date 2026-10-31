module

public import HeightPaper.Probability.LocalProfileStability

/-! # Compact real-tilt bounds for the canonical local profile -/

@[expose] public section

open MeasureTheory Complex Metric Set Filter
open scoped Topology ENNReal BigOperators

namespace HeightPaper.CountCoupling

/-- Finitely many stable disks give uniform parameter stability on every
compact real subset of the admissible interval. -/
theorem localProfile_unshifted_compact_parameter_stability {l₀ : ℝ} (hl₀ : 1 < l₀)
    {K : Set ℝ} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKd : K ⊆ Ioo 0 (profileRoot l₀)) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ t > (0 : ℝ), ∀ a ≥ l₀, ∀ b ≥ l₀, |a - b| < t → ∀ n : ℕ,
      birthParentLaw.real (localProfileParameterBad a b n (Complex.ofReal '' K) ε) < δ := by
  classical
  choose r hr hu hp using fun x : K ↦
    exists_localProfile_stable_disk hl₀ (hKd x.property).1 (hKd x.property).2
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K ↦ ball (x : ℝ) (r x))
    (fun _ ↦ isOpen_ball) (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hy, _⟩ := mem_iUnion.mp hy
    exact ⟨y, hy⟩
  have hd : 0 < δ / ((s.card : ℝ) + 1) := by positivity
  choose t ht hstab using fun x : K ↦ hp x ε hε (δ / ((s.card : ℝ) + 1)) hd
  refine ⟨s.inf' hsne t, (Finset.lt_inf'_iff hsne).mpr (fun x _ ↦ ht x), ?_⟩
  intro a ha b hb hab n
  let E : K → Set ((ℕ → ℝ) × (ℕ → ℝ)) := fun x ↦
    localProfileParameterBad a b n (closedBall ((x : ℝ) : ℂ) (r x)) ε
  have hsub : localProfileParameterBad a b n (Complex.ofReal '' K) ε ⊆ ⋃ x ∈ s, E x := by
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
  have heach : ∀ x ∈ s, birthParentLaw.real (E x) ≤ δ / ((s.card : ℝ) + 1) := by
    intro x hx
    exact (hstab x a ha b hb (hab.trans_le (Finset.inf'_le t hx)) n).le
  have hsum : (∑ x ∈ s, birthParentLaw.real (E x)) ≤
      (s.card : ℝ) * (δ / ((s.card : ℝ) + 1)) := by
    calc
      _ ≤ ∑ _x ∈ s, δ / ((s.card : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro x hx
        exact heach x hx
      _ = _ := by simp
  have hnum : (s.card : ℝ) * (δ / ((s.card : ℝ) + 1)) < δ := by
    have he : (δ / ((s.card : ℝ) + 1)) * ((s.card : ℝ) + 1) = δ :=
      div_mul_cancel₀ δ (by positivity)
    nlinarith
  exact hh.trans_lt (hsum.trans_lt hnum)

/-- Uniform upper tightness on a compact real set. -/
theorem localProfile_unshifted_compact_upper_tight {l₀ : ℝ} (hl₀ : 1 < l₀)
    {K : Set ℝ} (hK : IsCompact K) (hKd : K ⊆ Ioo 0 (profileRoot l₀))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ B > (0 : ℝ), ∀ l ≥ l₀, ∀ n : ℕ,
      birthParentLaw.real {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
        ∃ x ∈ K, B < ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖} < δ := by
  classical
  by_cases hKne : K.Nonempty
  swap
  · refine ⟨1, by norm_num, ?_⟩
    intro l hl n
    have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    simpa only [he, mem_empty_iff_false, false_and, exists_false, and_false,
      Set.ofPred_false, measureReal_empty] using hδ
  choose r hr hu hp using fun x : K ↦
    exists_localProfile_stable_disk hl₀ (hKd x.property).1 (hKd x.property).2
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K ↦ ball (x : ℝ) (r x))
    (fun _ ↦ isOpen_ball) (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hy, _⟩ := mem_iUnion.mp hy
    exact ⟨y, hy⟩
  have hd : 0 < δ / ((s.card : ℝ) + 1) := by positivity
  choose B hB hb using fun x : K ↦ hu x (δ / ((s.card : ℝ) + 1)) hd
  have hBpos : 0 < s.sup' hsne B := by
    obtain ⟨x, hx⟩ := hsne
    exact (hB x).trans_le (Finset.le_sup' B hx)
  refine ⟨s.sup' hsne B, hBpos, ?_⟩
  intro l hl n
  let E : K → Set ((ℕ → ℝ) × (ℕ → ℝ)) := fun x ↦
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ z ∈ closedBall ((x : ℝ) : ℂ) (r x), B x < ‖localUnshiftedRankProfileLimit l n q z‖}
  have hsub : {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ x ∈ K, s.sup' hsne B < ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖} ⊆
      ⋃ x ∈ s, E x := by
    rintro q ⟨hq, y, hy, he⟩
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hs hy)
    obtain ⟨hx, hyx⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, hq, (y : ℂ), ?_, ?_⟩⟩
    · have hh : dist y (x : ℝ) < r x := hyx
      simpa only [mem_closedBall, Complex.isometry_ofReal.dist_eq] using hh.le
    · exact (Finset.le_sup' B hx).trans_lt he
  have hh := (measureReal_mono (μ := birthParentLaw) hsub (measure_ne_top _ _)).trans
    (measureReal_biUnion_finset_le s E)
  have hsum : (∑ x ∈ s, birthParentLaw.real (E x)) ≤
      (s.card : ℝ) * (δ / ((s.card : ℝ) + 1)) := by
    calc
      _ ≤ ∑ _x ∈ s, δ / ((s.card : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro x hx
        exact (hb x l hl n).le
      _ = _ := by simp
  have hnum : (s.card : ℝ) * (δ / ((s.card : ℝ) + 1)) < δ := by
    have he : (δ / ((s.card : ℝ) + 1)) * ((s.card : ℝ) + 1) = δ :=
      div_mul_cancel₀ δ (by positivity)
    nlinarith
  exact hh.trans_lt (hsum.trans_lt hnum)

end HeightPaper.CountCoupling
