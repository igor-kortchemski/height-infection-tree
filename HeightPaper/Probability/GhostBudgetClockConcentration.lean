module

public import HeightPaper.Probability.GhostBudgetHarmonicIdentity
public import HeightPaper.Probability.GhostStoppedComparison

/-!
# Harmonic clock concentration for the continued susceptible chain

The padded epidemic realizes the unabsorbed susceptible budget at any fixed
horizon. Above a susceptible threshold, its law agrees with the stopped law,
so the stopped martingale tail estimate applies to the exact budget clock.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace HeightPaper.CountCoupling

open Model

noncomputable def budgetClockError (rate : ℝ≥0) (n m k : ℕ) : ℝ :=
  (n : ℝ) - m - k - ((harmonic m : ℝ) - harmonic n) / rate

theorem finiteSusceptible_budgetClockError_above_eq_stopped
    (a : ℝ≥0) (n H threshold : ℕ) (hthreshold : 0 < threshold)
    {ε : ℝ} :
    uniformLaw.real {u | threshold ≤ finiteSusceptible (a : ℝ) n u H ∧
      ε ≤ |budgetClockError (a / n) n (finiteSusceptible (a : ℝ) n u H) H / n|} =
      (stoppedCountLaw (a / n) threshold (ghostBudgetStart n H) H).toMeasure.real
        {s | threshold ≤ s.susceptible ∧
          ε ≤ |(finalSizeInvariant (a / n) s -
            finalSizeInvariant (a / n) (ghostBudgetStart n H)) / n|} := by
  let B : Set ℕ := {m | threshold ≤ m ∧
    ε ≤ |budgetClockError (a / n) n m H / n|}
  let A : Set State := {s | threshold ≤ s.susceptible ∧
    ε ≤ |(finalSizeInvariant (a / n) s -
      finalSizeInvariant (a / n) (ghostBudgetStart n H)) / n|}
  have hB : MeasurableSet B := trivial
  have hA : MeasurableSet A := trivial
  have hbudget : Measurable (fun u : ℕ → ℝ ↦
      finiteSusceptible (a : ℝ) n u H) := measurable_finiteSusceptible _ _ _
  have hU : uniformLaw.real {u | threshold ≤ finiteSusceptible (a : ℝ) n u H ∧
      ε ≤ |budgetClockError (a / n) n (finiteSusceptible (a : ℝ) n u H) H / n|} =
      birthParentLaw.real {q | threshold ≤ finiteSusceptible (a : ℝ) n q.1 H ∧
        ε ≤ |budgetClockError (a / n) n (finiteSusceptible (a : ℝ) n q.1 H) H / n|} := by
    calc
      _ = (uniformLaw.map (fun u ↦ finiteSusceptible (a : ℝ) n u H)).real B := by
        rw [Measure.real, Measure.real, Measure.map_apply hbudget hB]
        rfl
      _ = (birthParentLaw.map (fun q ↦
          finiteSusceptible (a : ℝ) n q.1 H)).real B := by
        have hmap : birthParentLaw.map (fun q ↦
            finiteSusceptible (a : ℝ) n q.1 H) =
            uniformLaw.map (fun u ↦ finiteSusceptible (a : ℝ) n u H) := by
          calc
            _ = (birthParentLaw.map Prod.fst).map
                (fun u ↦ finiteSusceptible (a : ℝ) n u H) := by
                  rw [Measure.map_map hbudget measurable_fst]
                  rfl
            _ = _ := by rw [birthParentLaw_map_fst]
        rw [hmap]
      _ = _ := by
        change ((birthParentLaw.map ((fun u : ℕ → ℝ ↦
          finiteSusceptible (a : ℝ) n u H) ∘ Prod.fst)) B).toReal = _
        rw [Measure.map_apply (hbudget.comp measurable_fst) hB]
        rfl
  have hpoint (q : (ℕ → ℝ) × (ℕ → ℝ)) :
      (threshold ≤ finiteSusceptible (a : ℝ) n q.1 H ∧
        ε ≤ |budgetClockError (a / n) n
          (finiteSusceptible (a : ℝ) n q.1 H) H / n|) ↔
      uniformTreeStateFrom (a : ℝ) n (ghostBudgetStart n H) q H ∈ A := by
    change (threshold ≤ finiteSusceptible (a : ℝ) n q.1 H ∧
        ε ≤ |budgetClockError (a / n) n
          (finiteSusceptible (a : ℝ) n q.1 H) H / n|) ↔
      (threshold ≤ (uniformTreeStateFrom (a : ℝ) n
          (ghostBudgetStart n H) q H).susceptible ∧
        ε ≤ |(finalSizeInvariant (a / n)
          (uniformTreeStateFrom (a : ℝ) n (ghostBudgetStart n H) q H) -
          finalSizeInvariant (a / n) (ghostBudgetStart n H)) / n|)
    rw [(ghostBudgetTree_counts (a : ℝ) n H q le_rfl).1]
    rw [ghostBudget_harmonic_increment_eq (a / n) (a : ℝ) n H q le_rfl]
    rfl
  have hset : {q : (ℕ → ℝ) × (ℕ → ℝ) |
      threshold ≤ finiteSusceptible (a : ℝ) n q.1 H ∧
        ε ≤ |budgetClockError (a / n) n
          (finiteSusceptible (a : ℝ) n q.1 H) H / n|} =
      (fun q ↦ uniformTreeStateFrom (a : ℝ) n (ghostBudgetStart n H) q H) ⁻¹' A := by
    ext q
    exact hpoint q
  have hcompare :
      (FinitePMF.kernelEvolve (PMF.pure (ghostBudgetStart n H))
        (fun _ ↦ step (a / n)) H).toMeasure.real A =
      (stoppedCountLaw (a / n) threshold (ghostBudgetStart n H) H).toMeasure.real A := by
    let C : Set State := {s | ε ≤ |(finalSizeInvariant (a / n) s -
      finalSizeInvariant (a / n) (ghostBudgetStart n H)) / n|}
    have heq : A = C ∩ {s | threshold ≤ s.susceptible} := by
      ext s
      simp only [A, C, Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [heq]
    exact (congrArg ENNReal.toReal
      (stoppedCountLaw_measure_above_start (a / n) threshold
        (ghostBudgetStart n H) H hthreshold C)).symm
  calc
    _ = birthParentLaw.real {q | threshold ≤ finiteSusceptible (a : ℝ) n q.1 H ∧
        ε ≤ |budgetClockError (a / n) n
          (finiteSusceptible (a : ℝ) n q.1 H) H / n|} := hU
    _ = birthParentLaw.real
        ((fun q ↦ uniformTreeStateFrom (a : ℝ) n (ghostBudgetStart n H) q H) ⁻¹' A) := by
      rw [hset]
    _ = (FinitePMF.kernelEvolve (PMF.pure (ghostBudgetStart n H))
        (fun _ ↦ step (a / n)) H).toMeasure.real A := by
      rw [Measure.real, Measure.real,
        ← ghostBudgetTree_state_law a n H H,
        Measure.map_apply (measurable_uniformTreeStateFrom _ _ _ _) hA]
    _ = _ := hcompare

theorem finiteSusceptible_budgetClockError_above_le
    (a : ℝ≥0) (n H threshold : ℕ) (ha : 0 < a)
    (hn : 0 < n) (hthreshold : 0 < threshold)
    {ε : ℝ} (hε : 0 < ε) :
    uniformLaw.real {u | threshold ≤ finiteSusceptible (a : ℝ) n u H ∧
      ε ≤ |budgetClockError (a / n) n (finiteSusceptible (a : ℝ) n u H) H / n|} ≤
      (H : ℝ) / (((a / n : ℝ≥0) : ℝ) * threshold * (ε * n) ^ 2) := by
  rw [finiteSusceptible_budgetClockError_above_eq_stopped a n H threshold hthreshold]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htail := stoppedCountLaw_finalSizeInvariant_tail_le (a / n) threshold
    (ghostBudgetStart n H) (div_pos ha (by exact_mod_cast hn)) hthreshold H
    (mul_pos hε hnR)
  apply le_trans _ htail
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro s hs
  change ε * n ≤ |finalSizeInvariant (a / n) s -
    finalSizeInvariant (a / n) (ghostBudgetStart n H)|
  have hh : ε ≤ |(finalSizeInvariant (a / n) s -
      finalSizeInvariant (a / n) (ghostBudgetStart n H)) / n| := hs.2
  rw [abs_div, abs_of_pos hnR, le_div_iff₀ hnR] at hh
  exact hh

end HeightPaper.CountCoupling
