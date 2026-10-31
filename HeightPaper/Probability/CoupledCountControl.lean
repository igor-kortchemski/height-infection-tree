module

public import HeightPaper.Probability.CountCouplingLaw
public import HeightPaper.Probability.UniformCountControl

/-!
# Transfer of the uniform count control to the source coupling

This uses the complete count-history law, including dependence between times.
Survival is imposed at every time for the signed unabsorbed walk, and is
equivalent to positivity of the terminal absorbed count.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper.CountCoupling

def countHistoryRatioTail (M : ℝ) (H : ℕ) : Set (Fin (H + 1) → ℕ × ℕ) :=
  {c | 0 < (c (Fin.last H)).2 ∧ ∃ i : Fin (H + 1), M < (i.val : ℝ) / (c i).2}

def coupledCountRatioTail (M l : ℝ) (n H : ℕ) : Set (ℕ → ℝ) :=
  {u | (∀ j ≤ H, 0 < finiteWalk l n u j) ∧
    ∃ k ≤ H, M < (k : ℝ) / (finiteWalk l n u k : ℝ)}

theorem countHistoryRatioTail_preimage_uniform (M l : ℝ) (n H : ℕ) :
    uniformCountHistory l n H ⁻¹' countHistoryRatioTail M H = coupledCountRatioTail M l n H := by
  ext u
  change (0 < (absorbedCounts l n u H).2 ∧
    ∃ i : Fin (H + 1), M < (i.val : ℝ) / ((absorbedCounts l n u i.val).2 : ℝ)) ↔ _
  constructor
  · rintro ⟨hH, i, hi⟩
    have hpos : ∀ j ≤ H, 0 < (absorbedCounts l n u j).2 :=
      fun j hj ↦ absorbedCounts_pos_past l n u hj hH
    refine ⟨(finiteWalk_survival_iff l n u H).mpr hpos, i.val, by omega, ?_⟩
    have heq : ((absorbedCounts l n u i.val).2 : ℝ) = (finiteWalk l n u i.val : ℝ) := by
      exact_mod_cast absorbedCounts_cast_eq_of_pos l n u i.val (hpos i.val (by omega))
    simpa only [heq] using hi
  · rintro ⟨hpos, k, hk, hbad⟩
    have ha := (finiteWalk_survival_iff l n u H).mp hpos
    refine ⟨ha H le_rfl, ⟨k, by omega⟩, ?_⟩
    have heq : ((absorbedCounts l n u k).2 : ℝ) = (finiteWalk l n u k : ℝ) := by
      exact_mod_cast absorbedCounts_cast_eq_of_pos l n u k (ha k hk)
    simpa only [heq] using hbad

theorem countHistoryRatioTail_preimage_state (M : ℝ) (H : ℕ) :
    stateCountHistory ⁻¹' countHistoryRatioTail M H = Model.survivingCountRatioTail M H := by
  ext p
  have heval (i : Fin (H + 1)) : p.eval i.val = p.state i := by
    simp only [Model.FinitePath.eval, Nat.min_eq_left (show i.val ≤ H by omega)]
  change (0 < Model.infectious p.last ∧
    ∃ i : Fin (H + 1), M < (i.val : ℝ) / Model.infectious (p.state i)) ↔ _
  constructor
  · rintro ⟨ha, i, hi⟩
    refine ⟨Finset.card_pos.mp ha, i.val, by omega, ?_⟩
    simpa only [heval i] using hi
  · rintro ⟨ha, k, hk, hb⟩
    refine ⟨ha.card_pos, ⟨k, by omega⟩, ?_⟩
    simpa only [heval ⟨k, by omega⟩] using hb

/-- Exact identity of the whole-time supremum event under the two laws. -/
theorem coupledCountRatioTail_probability (M : ℝ) (l : ℝ≥0) (n H : ℕ) :
    uniformLaw.real (coupledCountRatioTail M l n H) =
      (Model.pathMeasure (l / n) n H).real (Model.survivingCountRatioTail M H) := by
  have hA : MeasurableSet (countHistoryRatioTail M H) := Set.to_countable _ |>.measurableSet
  have h := congrArg (fun μ : Measure (Fin (H + 1) → ℕ × ℕ) ↦ μ (countHistoryRatioTail M H))
    (uniformCountHistory_eq_epidemic l n H)
  rw [Measure.map_apply (measurable_uniformCountHistory l n H) hA,
    Measure.map_apply (Model.FinitePath.measurable _) hA,
    countHistoryRatioTail_preimage_uniform, countHistoryRatioTail_preimage_state] at h
  exact congrArg ENNReal.toReal h

/-- First half of the source count-control lemma on its actual common uniform
space, with time uniformity inside probability and compact-parameter
uniformity outside probability. -/
theorem coupled_count_ratio_uniform_tight {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      uniformLaw.real (coupledCountRatioTail M l n ⌊T * n⌋₊) < ε := by
  obtain ⟨M, N, h⟩ := Model.uniform_surviving_count_ratio_tight hI hT hparams hε
  refine ⟨M, N, ?_⟩
  intro n hn l hl
  rw [coupledCountRatioTail_probability]
  exact h n hn l hl

end HeightPaper.CountCoupling
