module

public import HeightPaper.Probability.EarlyJointDistribution
public import HeightPaper.Probability.EarlyHeightJointLaw

/-!
# Joint early coordinates and logarithmic cutoff height

The real-threshold early triple is discrete, while the logarithmic cutoff
height tends to either zero or the deterministic surviving coefficient. The
middle CDF separates those two branches jointly with every discrete event.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal symmDiff Classical

namespace HeightPaper.CountCoupling

/-- At any threshold strictly between the two height limits, the joint CDF
selects precisely the early-extinction branch of the limiting triple. -/
theorem realThresholdEarlyTriple_heightLog_middle_cdf_tendsto
    (rates : ℕ → ℝ≥0) {l δ t : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (ht : 0 < t)
    (hta : t < growthFactor l * Real.exp (profileRoot l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (B : Set ((ℕ × Bool) × ℕ)) :
    Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | realThresholdEarlyTriple l δ n p ∈ B ∧
          (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
            Real.log n ≤ t}) atTop
      (𝓝 (birthParentLaw.real
        {q | localEarlyTriple l q ∈ B ∧
          (localEarlyTriple l q).1.2 = false})) := by
  let a := growthFactor l * Real.exp (profileRoot l)
  let ε := min (t / 2) ((a - t) / 2)
  have hε : 0 < ε := lt_min (half_pos ht) (half_pos (sub_pos.mpr hta))
  have hεt : ε < t := (min_le_left _ _).trans_lt (half_lt_self ht)
  have hεa : ε < a - t :=
    (min_le_right _ _).trans_lt (half_lt_self (sub_pos.mpr hta))
  let C : Set ((ℕ × Bool) × ℕ) := {z | z ∈ B ∧ z.1.2 = false}
  have hC := realThresholdEarlyTriple_event_probability_tendsto
    rates hl hδ hrates C
  have hbad := realThresholdHeightLogBad_probability_tendsto_zero
    rates hl hδ hrates hε
  have hdiff : Tendsto (fun n ↦
      |(Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | realThresholdEarlyTriple l δ n p ∈ B ∧
          (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
            Real.log n ≤ t} -
       (Model.pathMeasure (rates n) n (2 * n + 1)).real
         (realThresholdEarlyTriple l δ n ⁻¹' C)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hbad
    apply Eventually.of_forall
    intro n
    let μ := Model.pathMeasure (rates n) n (2 * n + 1)
    let A : Set (Model.FinitePath (2 * n + 1)) :=
      {p | realThresholdEarlyTriple l δ n p ∈ B ∧
        (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
          Real.log n ≤ t}
    let D : Set (Model.FinitePath (2 * n + 1)) :=
      realThresholdEarlyTriple l δ n ⁻¹' C
    let F := realThresholdHeightLogBad l δ ε n
    have hsub : (A ∆ D) ⊆ F := by
      intro p hp
      by_contra hnot
      have hreal : (realThresholdEarlyTriple l δ n p).1.2 =
          decide ((1 - δ) * fluidExtinctionTime l * n ≤
            ((2 * p.last.vertices - 1 : ℕ) : ℝ)) := rfl
      have hclose : |(Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
          Real.log n -
          if (1 - δ) * fluidExtinctionTime l * n ≤
              ((2 * p.last.vertices - 1 : ℕ) : ℝ) then a else 0| < ε := by
        exact lt_of_not_ge hnot
      have hbranch :
          ((Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
            Real.log n ≤ t) ↔
          (realThresholdEarlyTriple l δ n p).1.2 = false := by
        by_cases hs : (1 - δ) * fluidExtinctionTime l * n ≤
            ((2 * p.last.vertices - 1 : ℕ) : ℝ)
        · have hfalse : (realThresholdEarlyTriple l δ n p).1.2 ≠ false := by
            rw [hreal]
            simp [hs]
          have hc : a - ε <
              (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
                Real.log n := by
            have hh := (abs_lt.mp (by simpa only [ite_eq_left hs] using hclose)).1
            linarith
          constructor
          · intro hh
            linarith [hc, hεa]
          · intro hh
            exact False.elim (hfalse hh)
        · have htrue : (realThresholdEarlyTriple l δ n p).1.2 = false := by
            rw [hreal]
            simp [hs]
          have hc : (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
              Real.log n < ε := by
            have hh := (abs_lt.mp (by simpa only [ite_eq_right hs, sub_zero] using hclose)).2
            exact hh
          constructor
          · intro _
            exact htrue
          · intro _
            exact (hc.trans hεt).le
      have heq : p ∈ A ↔ p ∈ D := by
        simp only [A, D, C, mem_ofPred_eq, mem_preimage]
        exact and_congr Iff.rfl hbranch
      rcases hp with ⟨hpA, hpD⟩ | ⟨hpD, hpA⟩
      · exact hpD (heq.mp hpA)
      · exact hpA (heq.mpr hpD)
    exact (abs_measureReal_sub_le_measureReal_symmDiff
      (μ := μ) (show MeasurableSet A from trivial).nullMeasurableSet
      (show MeasurableSet D from trivial).nullMeasurableSet).trans
        (measureReal_mono hsub (measure_ne_top _ _))
  have hzero := (tendsto_zero_iff_abs_tendsto_zero _).mpr hdiff
  have hresult := hzero.add hC
  have hlimit : (localEarlyTriple l ⁻¹' C) =
      {q | localEarlyTriple l q ∈ B ∧
        (localEarlyTriple l q).1.2 = false} := rfl
  rw [hlimit] at hresult
  simpa only [sub_add_cancel, zero_add] using hresult

/-- Above the surviving height coefficient, the extra height condition is
asymptotically automatic jointly with any early-triple event. -/
theorem realThresholdEarlyTriple_heightLog_upper_cdf_tendsto
    (rates : ℕ → ℝ≥0) {l δ t : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hta : growthFactor l * Real.exp (profileRoot l) < t)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (B : Set ((ℕ × Bool) × ℕ)) :
    Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | realThresholdEarlyTriple l δ n p ∈ B ∧
          (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
            Real.log n ≤ t}) atTop
      (𝓝 (birthParentLaw.real (localEarlyTriple l ⁻¹' B))) := by
  let a := growthFactor l * Real.exp (profileRoot l)
  let ε := (t - a) / 2
  have ha : 0 < a := mul_pos (growthFactor_pos hl) (Real.exp_pos _)
  have hε : 0 < ε := half_pos (sub_pos.mpr hta)
  have hεt : ε < t := by dsimp [ε]; linarith
  have hεta : a + ε < t := by dsimp [ε]; linarith
  have hB := realThresholdEarlyTriple_event_probability_tendsto
    rates hl hδ hrates B
  have hbad := realThresholdHeightLogBad_probability_tendsto_zero
    rates hl hδ hrates hε
  have hdiff : Tendsto (fun n ↦
      |(Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | realThresholdEarlyTriple l δ n p ∈ B ∧
          (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
            Real.log n ≤ t} -
       (Model.pathMeasure (rates n) n (2 * n + 1)).real
         (realThresholdEarlyTriple l δ n ⁻¹' B)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hbad
    apply Eventually.of_forall
    intro n
    let μ := Model.pathMeasure (rates n) n (2 * n + 1)
    let A : Set (Model.FinitePath (2 * n + 1)) :=
      {p | realThresholdEarlyTriple l δ n p ∈ B ∧
        (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
          Real.log n ≤ t}
    let D : Set (Model.FinitePath (2 * n + 1)) :=
      realThresholdEarlyTriple l δ n ⁻¹' B
    let F := realThresholdHeightLogBad l δ ε n
    have hsub : (A ∆ D) ⊆ F := by
      intro p hp
      by_contra hnot
      have hclose : |(Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
          Real.log n -
          if (1 - δ) * fluidExtinctionTime l * n ≤
              ((2 * p.last.vertices - 1 : ℕ) : ℝ) then a else 0| < ε :=
        lt_of_not_ge hnot
      have hheight :
          (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
            Real.log n ≤ t := by
        by_cases hs : (1 - δ) * fluidExtinctionTime l * n ≤
            ((2 * p.last.vertices - 1 : ℕ) : ℝ)
        · have hh := (abs_lt.mp
            (by simpa only [ite_eq_left hs] using hclose)).2
          linarith
        · have hh := (abs_lt.mp
            (by simpa only [ite_eq_right hs, sub_zero] using hclose)).2
          linarith
      have heq : p ∈ A ↔ p ∈ D := by
        simp only [A, D, mem_ofPred_eq, mem_preimage]
        exact and_iff_left hheight
      rcases hp with ⟨hpA, hpD⟩ | ⟨hpD, hpA⟩
      · exact hpD (heq.mp hpA)
      · exact hpA (heq.mpr hpD)
    exact (abs_measureReal_sub_le_measureReal_symmDiff
      (μ := μ) (show MeasurableSet A from trivial).nullMeasurableSet
      (show MeasurableSet D from trivial).nullMeasurableSet).trans
        (measureReal_mono hsub (measure_ne_top _ _))
  have hzero := (tendsto_zero_iff_abs_tendsto_zero _).mpr hdiff
  have hresult := hzero.add hB
  simpa only [sub_add_cancel, zero_add] using hresult

/-- Below zero the joint CDF vanishes, since cutoff height is nonnegative. -/
theorem realThresholdEarlyTriple_heightLog_lower_cdf_tendsto
    (rates : ℕ → ℝ≥0) (l δ : ℝ) {t : ℝ} (ht : t < 0)
    (B : Set ((ℕ × Bool) × ℕ)) :
    Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | realThresholdEarlyTriple l δ n p ∈ B ∧
          (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
            Real.log n ≤ t}) atTop (𝓝 0) := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos hnR
  have hset : {p : Model.FinitePath (2 * n + 1) |
      realThresholdEarlyTriple l δ n p ∈ B ∧
        (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
          Real.log n ≤ t} = ∅ := by
    ext p
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro _
    have hnonneg : 0 ≤
        (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) /
          Real.log n := div_nonneg (Nat.cast_nonneg _) hlog.le
    linarith
  rw [hset, measureReal_empty]

end HeightPaper.CountCoupling
