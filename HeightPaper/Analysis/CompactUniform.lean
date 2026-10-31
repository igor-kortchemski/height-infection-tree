module

public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compact-parameter tightness from converging parameter sequences

A subsequence can be filled with its limit without changing its selected
values. This turns tightness along every converging parameter sequence into
weak uniform tightness on a compact parameter set. The probability supremum
is outside the parameter quantifier; no common probability space is assumed.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace HeightPaper

theorem exists_tendsto_extension {α : Type*} [TopologicalSpace α]
    {x : ℕ → α} {a : α} (hx : Tendsto x atTop (𝓝 a))
    {v : ℕ → ℕ} (hv : StrictMono v) :
    ∃ y : ℕ → α, Tendsto y atTop (𝓝 a) ∧ ∀ j, y (v j) = x j := by
  classical
  let y : ℕ → α := fun n ↦ if h : ∃ j, v j = n then x h.choose else a
  refine ⟨y, ?_, ?_⟩
  · apply tendsto_def.mpr
    intro s hs
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hx.eventually hs)
    filter_upwards [eventually_ge_atTop (v J)] with n hn
    change (if h : ∃ j, v j = n then x h.choose else a) ∈ s
    split_ifs with h
    · apply hJ
      apply hv.le_iff_le.mp
      simpa only [h.choose_spec] using hn
    · exact mem_of_mem_nhds hs
  · intro j
    dsimp [y]
    rw [dite_eq_left (show ∃ i, v i = v j from ⟨j, rfl⟩)]
    congr 1
    exact hv.injective (Exists.choose_spec (show ∃ i, v i = v j from ⟨j, rfl⟩))

/-- An antitone family of upper-tail probabilities is tight uniformly on a
compact parameter set if it is tight along every parameter sequence converging
to a point of that set. The constant is chosen before the parameter and size. -/
theorem compact_uniform_tight_of_sequence {α : Type*} [TopologicalSpace α]
    [FirstCountableTopology α] {K : Set α} (hK : IsCompact K)
    (p : ℕ → α → ℕ → ℝ) (hp : ∀ n a, Antitone (p n a))
    (hseq : ∀ a ∈ K, ∀ x : ℕ → α, Tendsto x atTop (𝓝 a) →
      ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ᶠ n in atTop, p n (x n) M < ε) :
    ∀ ε > (0 : ℝ), ∃ M N : ℕ, ∀ n ≥ N, ∀ a ∈ K, p n a M < ε := by
  classical
  intro ε hε
  by_contra h
  push Not at h
  have hfreq : ∀ M, ∃ᶠ n in atTop, ∃ a ∈ K, ε ≤ p n a M := by
    intro M
    rw [frequently_atTop]
    intro N
    obtain ⟨n, hn, a, ha, hbad⟩ := h M N
    exact ⟨n, hn, a, ha, hbad⟩
  obtain ⟨v, hv, hbad⟩ := extraction_forall_of_frequently hfreq
  choose x hx hpx using hbad
  obtain ⟨a, ha, w, hw, hconv⟩ := hK.tendsto_subseq hx
  obtain ⟨y, hy, heq⟩ := exists_tendsto_extension hconv (hv.comp hw)
  obtain ⟨M, hM⟩ := hseq a ha y hy ε hε
  have hsel := (hv.comp hw).tendsto_atTop.eventually hM
  obtain ⟨j, hj, hlarge⟩ := (hsel.and
    (hw.tendsto_atTop.eventually (eventually_ge_atTop M))).exists
  have hgood : p (v (w j)) (x (w j)) M < ε := by
    have heqj : y (v (w j)) = x (w j) := heq j
    simpa only [Function.comp_apply, heqj] using hj
  exact not_lt_of_ge ((hpx (w j)).trans (hp _ _ hlarge)) hgood

end HeightPaper
