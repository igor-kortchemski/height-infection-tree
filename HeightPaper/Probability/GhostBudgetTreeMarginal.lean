module

public import HeightPaper.Probability.GhostTreeLaw

/-!
# Pathwise budget marginal of the padded epidemic tree

The padded tree cannot go extinct in its chosen horizon. Its susceptible
counter therefore follows the paper's unabsorbed budget chain under the same
birth uniform sequence, including after the source walk first hits zero.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

theorem ghostBudgetTree_counts (l : ℝ) (n H : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) {k : ℕ} (hk : k ≤ H) :
    (uniformTreeStateFrom l n (ghostBudgetStart n H) q k).susceptible =
        finiteSusceptible l n q.1 k ∧
      H + 1 ≤ infectious (uniformTreeStateFrom l n (ghostBudgetStart n H) q k) + k := by
  induction k with
  | zero =>
    simp [uniformTreeStateFrom]
  | succ k ih =>
    obtain ⟨hS, hA⟩ := ih (by omega)
    let s := uniformTreeStateFrom l n (ghostBudgetStart n H) q k
    have hactive : s.active.Nonempty := by
      apply Finset.card_pos.mp
      change 0 < infectious s
      change H + 1 ≤ infectious s + k at hA
      omega
    have hb : budgetBirth l n s.susceptible (q.1 k) = finiteBirth l n q.1 k := by
      rw [hS]
      rfl
    rw [uniformTreeStateFrom, uniformTreeUpdate, hb]
    have hc := counts_rankUpdate (finiteBirth l n q.1 k) s hactive (q.2 k)
    simp only [counts] at hc
    change H + 1 ≤ infectious s + k at hA
    change (rankUpdate (finiteBirth l n q.1 k) s (q.2 k)).susceptible = _ ∧
      H + 1 ≤ infectious (rankUpdate (finiteBirth l n q.1 k) s (q.2 k)) + (k + 1)
    cases hbirth : finiteBirth l n q.1 k <;>
      simp only [hbirth, Bool.false_eq_true, ↓reduceIte] at hc ⊢
    · have hs := congrArg Prod.fst hc
      have hi := congrArg Prod.snd hc
      rw [finiteSusceptible_succ, hbirth]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨hs.trans hS, by omega⟩
    · have hs := congrArg Prod.fst hc
      have hi := congrArg Prod.snd hc
      rw [finiteSusceptible_succ, hbirth]
      simp only [↓reduceIte]
      exact ⟨by rw [hS] at hs; exact hs, by omega⟩

theorem ghostBudgetTree_infectious_eq_walk (l : ℝ) (n H : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) {k : ℕ} (hk : k ≤ H) :
    (infectious (uniformTreeStateFrom l n (ghostBudgetStart n H) q k) : ℤ) =
      H + finiteWalk l n q.1 k := by
  induction k with
  | zero => simp [uniformTreeStateFrom]
  | succ k ih =>
    have hprior := ih (by omega)
    let s := uniformTreeStateFrom l n (ghostBudgetStart n H) q k
    change (infectious s : ℤ) = H + finiteWalk l n q.1 k at hprior
    have hS := (ghostBudgetTree_counts l n H q (by omega : k ≤ H)).1
    have hactive : s.active.Nonempty := by
      apply Finset.card_pos.mp
      change 0 < infectious s
      have hh := (ghostBudgetTree_counts l n H q (by omega : k ≤ H)).2
      change H + 1 ≤ infectious s + k at hh
      omega
    have hb : budgetBirth l n s.susceptible (q.1 k) = finiteBirth l n q.1 k := by
      rw [hS]
      rfl
    have hc := counts_rankUpdate (finiteBirth l n q.1 k) s hactive (q.2 k)
    simp only [counts] at hc
    have hi := congrArg Prod.snd hc
    have hIpos : 0 < infectious s := hactive.card_pos
    rw [uniformTreeStateFrom, uniformTreeUpdate, hb, finiteWalk_succ]
    change (infectious (rankUpdate (finiteBirth l n q.1 k) s (q.2 k)) : ℤ) =
      H + (finiteWalk l n q.1 k +
        if finiteBirth l n q.1 k then 1 else -1)
    cases hbirth : finiteBirth l n q.1 k <;>
      simp only [hbirth, Bool.false_eq_true, ↓reduceIte] at hi ⊢ <;>
      omega

theorem ghostBudgetTree_susceptible_law (l : ℝ≥0) (n H : ℕ)
    {k : ℕ} (hk : k ≤ H) :
    uniformLaw.map (fun u ↦ finiteSusceptible l n u k) =
      (kernelPathMeasure (fun _ ↦ step (l / n)) (ghostBudgetStart n H) k).map
        (fun q ↦ q.last.susceptible) := by
  have hpath : (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      finiteSusceptible (l : ℝ) n q.1 k) =
      (fun q : FinitePath k ↦ q.last.susceptible) ∘
        uniformTreeHistoryFrom l n (ghostBudgetStart n H) k := by
    funext q
    exact (ghostBudgetTree_counts (l : ℝ) n H q hk).1.symm
  have hm : Measurable (fun u : ℕ → ℝ ↦ finiteSusceptible (l : ℝ) n u k) :=
    measurable_finiteSusceptible (l : ℝ) n k
  calc
    _ = birthParentLaw.map ((fun u : ℕ → ℝ ↦
        finiteSusceptible (l : ℝ) n u k) ∘ Prod.fst) := by
      rw [← Measure.map_map hm measurable_fst, birthParentLaw_map_fst]
    _ = birthParentLaw.map (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
        finiteSusceptible (l : ℝ) n q.1 k) := rfl
    _ = birthParentLaw.map ((fun q : FinitePath k ↦ q.last.susceptible) ∘
        uniformTreeHistoryFrom l n (ghostBudgetStart n H) k) := by rw [hpath]
    _ = (birthParentLaw.map (uniformTreeHistoryFrom l n (ghostBudgetStart n H) k)).map
        (fun q : FinitePath k ↦ q.last.susceptible) := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_uniformTreeHistoryFrom _ _ _ _)]
    _ = _ := by rw [uniformTreeHistoryFrom_law]

theorem ghostBudgetTree_state_law (l : ℝ≥0) (n H k : ℕ) :
    birthParentLaw.map
      (fun q ↦ uniformTreeStateFrom l n (ghostBudgetStart n H) q k) =
      (FinitePMF.kernelEvolve (PMF.pure (ghostBudgetStart n H))
        (fun _ ↦ step (l / n)) k).toMeasure := by
  have hlast : (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      uniformTreeStateFrom (l : ℝ) n (ghostBudgetStart n H) q k) =
      FinitePath.last ∘ uniformTreeHistoryFrom l n (ghostBudgetStart n H) k := by
    rfl
  rw [hlast, ← Measure.map_map (FinitePath.measurable _)
    (measurable_uniformTreeHistoryFrom _ _ _ _),
    uniformTreeHistoryFrom_law]
  simpa only [FinitePath.eval_last] using
    kernelPathMeasure_map_eval (fun _ ↦ step (l / n))
      (ghostBudgetStart n H) k k le_rfl

end HeightPaper.CountCoupling
