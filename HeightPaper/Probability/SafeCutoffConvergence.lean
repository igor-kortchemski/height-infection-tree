module

public import HeightPaper.Probability.FiniteSafeCutoff
public import HeightPaper.Probability.SurvivalCoupling

/-!
# Agreement of the exact survival-clipped safe cutoffs

Tight cutoffs lie in a fixed prefix with high probability. On that prefix the
uniform coupling agrees, and the survival indicators agree with high
probability. Consequently the two clipped integer cutoffs are exactly equal
with probability tending to one, uniformly on the source compact parameter sets.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology Classical NNReal

namespace HeightPaper.CountCoupling

noncomputable def survivingFiniteSafeCutoff (l : ℝ) (n H : ℕ) (u : ℕ → ℝ) : ℕ :=
  if ∀ j ≤ H, 0 < finiteWalk l n u j then finiteSafeCutoff l n H u else 0

noncomputable def survivingLocalSafeCutoff (l : ℝ) (u : ℕ → ℝ) : ℕ :=
  if ∀ j, 0 < localWalk l u j then localSafeCutoff l u else 0

/-- Deterministic prefix agreement, apart from the null exceptional local
unsafe-set event, reduces cutoff disagreement to four controlled events. -/
theorem safeCutoff_disagreement_probability_le {l : ℝ} (hl : 1 < l)
    (n H K : ℕ) (hKH : K ≤ H) :
    uniformLaw.real {u | survivingFiniteSafeCutoff l n H u ≠ survivingLocalSafeCutoff l u} ≤
      uniformLaw.real {u | K < survivingFiniteSafeCutoff l n H u} +
      uniformLaw.real {u | K < localSafeCutoff l u} +
      uniformLaw.real {u | ¬ ((∀ j ≤ H, 0 < finiteWalk l n u j) ↔
        ∀ j, 0 < localWalk l u j)} +
      uniformLaw.real {u | ∃ j ≤ K, finiteWalk l n u j ≠ localWalk l u j} := by
  let E₁ : Set (ℕ → ℝ) := {u | K < survivingFiniteSafeCutoff l n H u}
  let E₂ : Set (ℕ → ℝ) := {u | K < localSafeCutoff l u}
  let E₃ : Set (ℕ → ℝ) := {u | ¬ ((∀ j ≤ H, 0 < finiteWalk l n u j) ↔
    ∀ j, 0 < localWalk l u j)}
  let E₄ : Set (ℕ → ℝ) := {u | ∃ j ≤ K, finiteWalk l n u j ≠ localWalk l u j}
  have hsub : {u | survivingFiniteSafeCutoff l n H u ≠ survivingLocalSafeCutoff l u}
      ≤ᵐ[uniformLaw] (E₁ ∪ E₂) ∪ (E₃ ∪ E₄) := by
    filter_upwards [localSafeCutoff_ae_bddAbove hl] with u hb
    intro hu
    by_contra hnot
    have h₁ : u ∉ E₁ := fun h ↦ hnot (Or.inl (Or.inl h))
    have h₂ : u ∉ E₂ := fun h ↦ hnot (Or.inl (Or.inr h))
    have h₃ : u ∉ E₃ := fun h ↦ hnot (Or.inr (Or.inl h))
    have h₄ : u ∉ E₄ := fun h ↦ hnot (Or.inr (Or.inr h))
    have hsurv : (∀ j ≤ H, 0 < finiteWalk l n u j) ↔ ∀ j, 0 < localWalk l u j :=
      Classical.not_not.mp h₃
    by_cases ha : ∀ j ≤ H, 0 < finiteWalk l n u j
    · have hla := hsurv.mp ha
      have hfK : finiteSafeCutoff l n H u ≤ K := by
        apply le_of_not_gt
        intro h
        apply h₁
        simpa only [E₁, mem_ofPred_eq, survivingFiniteSafeCutoff, ite_eq_left ha] using h
      have hlK : localSafeCutoff l u ≤ K := le_of_not_gt h₂
      have hprefix : ∀ j ≤ K, finiteWalk l n u j = localWalk l u j :=
        fun j hj ↦ Classical.not_not.mp (fun h ↦ h₄ ⟨j, hj, h⟩)
      have heq := finiteSafeCutoff_eq_local_of_prefix l n H K u hKH hb hfK hlK hprefix
      apply hu
      simp only [survivingFiniteSafeCutoff, survivingLocalSafeCutoff,
        ite_eq_left ha, ite_eq_left hla, heq]
    · have hla : ¬ ∀ j, 0 < localWalk l u j := fun h ↦ ha (hsurv.mpr h)
      apply hu
      simp only [survivingFiniteSafeCutoff, survivingLocalSafeCutoff,
        ite_eq_right ha, ite_eq_right hla]
  have hprob : uniformLaw.real
      {u | survivingFiniteSafeCutoff l n H u ≠ survivingLocalSafeCutoff l u} ≤
      uniformLaw.real ((E₁ ∪ E₂) ∪ (E₃ ∪ E₄)) :=
    ENNReal.toReal_mono (measure_ne_top uniformLaw ((E₁ ∪ E₂) ∪ (E₃ ∪ E₄)))
      (measure_mono_ae hsub)
  have hu := measureReal_union_le (μ := uniformLaw) (E₁ ∪ E₂) (E₃ ∪ E₄)
  have h12 := measureReal_union_le (μ := uniformLaw) E₁ E₂
  have h34 := measureReal_union_le (μ := uniformLaw) E₃ E₄
  change uniformLaw.real {u | survivingFiniteSafeCutoff l n H u ≠ survivingLocalSafeCutoff l u} ≤
    uniformLaw.real E₁ + uniformLaw.real E₂ + uniformLaw.real E₃ + uniformLaw.real E₄
  linarith

/-- The source's clipped `Jⁿ` and `J` are equal with probability tending to
one, weakly uniformly on compact supercritical parameter sets. -/
theorem safeCutoff_survival_disagreement_uniform {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I, uniformLaw.real
      {u | survivingFiniteSafeCutoff l n ⌊T * n⌋₊ u ≠ survivingLocalSafeCutoff l u} < ε := by
  by_cases hne : I.Nonempty
  swap
  · exact ⟨0, fun n hn l hl ↦ False.elim (hne ⟨l, hl⟩)⟩
  obtain ⟨l₀, hl₀, hmin⟩ := hI.exists_isLeast hne
  obtain ⟨L, hL⟩ := hI.bddAbove
  have hl₀1 : 1 < (l₀ : ℝ) := (hparams l₀ hl₀).1
  have hδ : 0 < ε / 5 := by positivity
  obtain ⟨Kf, Nf, hfinite⟩ := finiteSafeCutoff_survival_uniform_tight hI hT hparams hδ
  obtain ⟨Kl, hlocal⟩ := localSafeCutoff_uniform_tight hl₀1 hδ
  obtain ⟨Ns, hsurv⟩ := uniform_survival_disagreement hI hT hparams hδ
  let K := max Kf Kl
  have hlimH : Tendsto (fun n : ℕ ↦ ⌊T * n⌋₊) atTop atTop :=
    (tendsto_nat_floor_atTop (α := ℝ)).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hT)
  obtain ⟨Nh, hNh⟩ := eventually_atTop.mp (hlimH.eventually (eventually_ge_atTop K))
  have hlimP : Tendsto (fun n : ℕ ↦ (L : ℝ) * (K : ℝ) ^ 2 / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  obtain ⟨Np, hNp⟩ := eventually_atTop.mp (hlimP.eventually (Iio_mem_nhds hδ))
  refine ⟨Nf + Ns + Nh + Np + K + 1, ?_⟩
  intro n hn l hl
  have hnpos : 0 < n := by omega
  have hKn : K ≤ n := by omega
  have hKH : K ≤ ⌊T * n⌋₊ := hNh n (by omega)
  have hlmin : (l₀ : ℝ) ≤ l := by exact_mod_cast hmin hl
  have hlL : (l : ℝ) ≤ L := by exact_mod_cast hL hl
  have hf : uniformLaw.real {u | K < survivingFiniteSafeCutoff l n ⌊T * n⌋₊ u} < ε / 5 := by
    apply lt_of_le_of_lt (measureReal_mono (μ := uniformLaw) ?_) (hfinite n (by omega) l hl)
    intro u hu
    exact (le_max_left Kf Kl).trans_lt hu
  have hloc : uniformLaw.real {u | K < localSafeCutoff l u} ≤ ε / 5 := by
    apply (measureReal_mono (μ := uniformLaw) ?_).trans (hlocal l hlmin)
    intro u hu
    exact (le_max_right Kf Kl).trans_lt hu
  have hs : uniformLaw.real {u | ¬ ((∀ j ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u j) ↔
      ∀ j, 0 < localWalk l u j)} < ε / 5 := hsurv n (by omega) l hl
  have hp : uniformLaw.real {u | ∃ j ≤ K, finiteWalk l n u j ≠ localWalk l u j} < ε / 5 := by
    apply lt_of_le_of_lt (prefix_disagreement_probability_le_uniform hnpos hKn l
      ⟨l.coe_nonneg, hlL⟩) (hNp n (by omega))
  have hbound := safeCutoff_disagreement_probability_le (hparams l hl).1 n ⌊T * n⌋₊ K hKH
  linarith

end HeightPaper.CountCoupling
