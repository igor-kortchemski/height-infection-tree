module

public import HeightPaper.Probability.LocalProfileCompactStability
public import HeightPaper.Probability.LocalProfilePointwisePositive

/-! # Compact-parameter lower tightness for the local profile limit -/

@[expose] public section

open MeasureTheory Complex Metric Set Filter
open scoped Topology ENNReal NNReal BigOperators

namespace HeightPaper.CountCoupling

/-- Compact parameter covering upgrades the fixed-parameter lower-tail
estimate using uniform parameter stability on the entire real tilt set. -/
theorem localProfile_unshifted_compact_lower_tight_of_pointwise {l₀ : ℝ} (hl₀ : 1 < l₀)
    {I K : Set ℝ} (hI : IsCompact I) (hIlower : ∀ l ∈ I, l₀ ≤ l)
    (hK : IsCompact K) (hKd : K ⊆ Ioo 0 (profileRoot l₀))
    (hpoint : ∀ l ∈ I, ∀ δ > (0 : ℝ), ∃ c > (0 : ℝ), ∀ n : ℕ,
      birthParentLaw.real {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
        ∃ x ∈ K, ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖ < c} < δ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c > (0 : ℝ), ∀ l ∈ I, ∀ n : ℕ,
      birthParentLaw.real {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
        ∃ x ∈ K, ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖ < c} < δ := by
  classical
  by_cases hIne : I.Nonempty
  swap
  · refine ⟨1, by norm_num, ?_⟩
    exact fun l hl ↦ False.elim (hIne ⟨l, hl⟩)
  by_cases hKne : K.Nonempty
  swap
  · refine ⟨1, by norm_num, ?_⟩
    intro l hl n
    have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    simpa only [he, mem_empty_iff_false, false_and, exists_false, and_false,
      Set.ofPred_false, measureReal_empty] using hδ
  choose c hc hsmall using fun l : I ↦ hpoint l l.property (δ / 2) (half_pos hδ)
  choose t ht hstable using fun l : I ↦ localProfile_unshifted_compact_parameter_stability
    hl₀ hK hKne hKd (half_pos (hc l)) (half_pos hδ)
  obtain ⟨s, hs⟩ := hI.elim_finite_subcover (fun l : I ↦ ball (l : ℝ) (t l))
    (fun _ ↦ isOpen_ball) (fun l hl ↦ mem_iUnion.mpr ⟨⟨l, hl⟩, mem_ball_self (ht ⟨l, hl⟩)⟩)
  have hsne : s.Nonempty := by
    obtain ⟨l, hl⟩ := hIne
    obtain ⟨b, hb⟩ := mem_iUnion.mp (hs hl)
    obtain ⟨hb, _⟩ := mem_iUnion.mp hb
    exact ⟨b, hb⟩
  let c₀ := s.inf' hsne (fun l ↦ c l / 2)
  have hc₀ : 0 < c₀ := (Finset.lt_inf'_iff hsne).mpr (fun l _ ↦ half_pos (hc l))
  refine ⟨c₀, hc₀, ?_⟩
  intro l hl n
  obtain ⟨b, hb⟩ := mem_iUnion.mp (hs hl)
  obtain ⟨hb, hlb⟩ := mem_iUnion.mp hb
  have hclose : |l - (b : ℝ)| < t b := by simpa only [mem_ball, Real.dist_eq] using hlb
  let E := localProfileParameterBad l b n (Complex.ofReal '' K) (c b / 2)
  let F : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i, 0 < (localWalk b q.1 i : ℝ)) ∧
      ∃ x ∈ K, ‖localUnshiftedRankProfileLimit b n q (x : ℂ)‖ < c b}
  have hE : birthParentLaw.real E < δ / 2 :=
    hstable b l (hIlower l hl) b (hIlower b b.property) hclose n
  have hF : birthParentLaw.real F < δ / 2 := hsmall b n
  have hsub : {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ x ∈ K, ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖ < c₀} ⊆ E ∪ F := by
    rintro q ⟨hq, x, hx, he⟩
    by_cases hqE : q ∈ E
    · exact Or.inl hqE
    · right
      have hsurv : ∀ i, 0 < (localWalk b q.1 i : ℝ) := by
        by_contra hh
        exact hqE ⟨hq, Or.inl hh⟩
      have hdiff : ‖localUnshiftedRankProfileLimit l n q (x : ℂ) -
          localUnshiftedRankProfileLimit b n q (x : ℂ)‖ ≤ c b / 2 := by
        apply le_of_not_gt
        intro hh
        exact hqE ⟨hq, Or.inr ⟨(x : ℂ), ⟨x, hx, rfl⟩, hh⟩⟩
      refine ⟨hsurv, x, hx, ?_⟩
      have hcle : c₀ ≤ c b / 2 := Finset.inf'_le _ hb
      have hnorm := norm_le_norm_add_norm_sub
        (localUnshiftedRankProfileLimit l n q (x : ℂ))
        (localUnshiftedRankProfileLimit b n q (x : ℂ))
      rw [norm_sub_rev] at hdiff
      rw [norm_sub_rev] at hnorm
      nlinarith [he, hnorm, hdiff, hcle]
  have hh := (measureReal_mono (μ := birthParentLaw) hsub).trans (measureReal_union_le E F)
  linarith

/-- The compact lower-tail estimate for the actual local profile limit,
uniform in the epidemic parameter and the initial susceptible count. -/
theorem localProfile_unshifted_compact_lower_tight {l₀ : ℝ} (hl₀ : 1 < l₀)
    {I K : Set ℝ} (hI : IsCompact I) (hIlower : ∀ l ∈ I, l₀ ≤ l)
    (hK : IsCompact K) (hKd : K ⊆ Ioo 0 (profileRoot l₀))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c > (0 : ℝ), ∀ l ∈ I, ∀ n : ℕ,
      birthParentLaw.real {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
        ∃ x ∈ K, ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖ < c} < δ := by
  apply localProfile_unshifted_compact_lower_tight_of_pointwise hl₀ hI hIlower hK hKd
    (fun l hlI ε hε => ?_) hδ
  have hl : 1 < l := hl₀.trans_le (hIlower l hlI)
  exact localUnshiftedRankProfileLimit_compact_lower_tight hl hK (by
    intro x hx
    exact ⟨(hKd hx).1, (hKd hx).2.trans_le
      (profileRoot_mono_supercritical hl₀ (hIlower l hlI))⟩) hε

/-- The same estimate with the epidemic parameter in its natural nonnegative
carrier, ready for the finite epidemic estimates. -/
theorem localProfile_unshifted_compact_lower_tight_nnreal {l₀ : ℝ} (hl₀ : 1 < l₀)
    {I : Set ℝ≥0} (hI : IsCompact I) (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    {K : Set ℝ} (hK : IsCompact K) (hKd : K ⊆ Ioo 0 (profileRoot l₀))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c > (0 : ℝ), ∀ l ∈ I, ∀ n : ℕ,
      birthParentLaw.real {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
        ∃ x ∈ K, ‖localUnshiftedRankProfileLimit l n q (x : ℂ)‖ < c} < δ := by
  have hIreal : IsCompact ((fun l : ℝ≥0 => (l : ℝ)) '' I) :=
    hI.image NNReal.continuous_coe
  obtain ⟨c, hc, hb⟩ := localProfile_unshifted_compact_lower_tight hl₀ hIreal
    (by rintro a ⟨l, hl, rfl⟩; exact hIlower l hl) hK hKd hδ
  exact ⟨c, hc, fun l hl n => hb l ⟨l, hl, rfl⟩ n⟩

end HeightPaper.CountCoupling
