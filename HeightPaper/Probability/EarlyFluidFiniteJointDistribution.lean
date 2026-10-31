module

public import HeightPaper.Probability.EarlyHeightFullJointDistribution

/-!
# Finite-dimensional joint weak convergence with the fluid coordinates

At any prescribed infectious and susceptible observation times, the early
triple, logarithmic cutoff height, and two fluid coordinates converge jointly
under the original complete epidemic path law.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal Classical

namespace HeightPaper.CountCoupling

theorem realThresholdEarlyTriple_heightLog_fluidAt_tendstoInDistribution
    (rates : ℕ → ℝ≥0) {l δ ti ts : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hti : 0 ≤ ti)
    (hts : ts ∈ Icc (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    TendstoInDistribution
      (fun (n : ℕ) p ↦
        ((realThresholdEarlyTriple l δ n p,
          (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) / Real.log n),
         ((Model.infectious (p.eval ⌊ti * n⌋₊) : ℝ) / n,
          (p.eval ⌊ts * n⌋₊).susceptible / (n : ℝ))))
      atTop
      (fun q ↦
        ((localEarlyTriple l q,
          if (localEarlyTriple l q).1.2 then
            growthFactor l * Real.exp (profileRoot l) else 0),
         (if (localEarlyTriple l q).1.2 then fluidInfectious l ti else 0,
          if (localEarlyTriple l q).1.2 then fluidSusceptible l ts else 1)))
      (fun n ↦ Model.pathMeasure (rates n) n (2 * n + 1))
      birthParentLaw := by
  let a := growthFactor l * Real.exp (profileRoot l)
  let T : (n : ℕ) → Model.FinitePath (2 * n + 1) → ((ℕ × Bool) × ℕ) :=
    fun n ↦ realThresholdEarlyTriple l δ n
  let H : (n : ℕ) → Model.FinitePath (2 * n + 1) → ℝ :=
    fun n p ↦ (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) / Real.log n
  let I : (n : ℕ) → Model.FinitePath (2 * n + 1) → ℝ :=
    fun n p ↦ (Model.infectious (p.eval ⌊ti * n⌋₊) : ℝ) / n
  let S : (n : ℕ) → Model.FinitePath (2 * n + 1) → ℝ :=
    fun n p ↦ (p.eval ⌊ts * n⌋₊).susceptible / (n : ℝ)
  let enc : ((ℕ × Bool) × ℕ) → ((ℕ × ℕ) × ℕ) :=
    fun z ↦ ((z.1.1, if z.1.2 then 1 else 0), z.2)
  let dec : ((ℕ × ℕ) × ℕ) → ((ℕ × Bool) × ℕ) :=
    fun z ↦ ((z.1.1, decide (z.1.2 = 1)), z.2)
  have hdecenc (z : ((ℕ × Bool) × ℕ)) : dec (enc z) = z := by
    rcases z with ⟨⟨k, b⟩, h⟩
    cases b <;> simp [dec, enc]
  let g : ((ℕ × Bool) × ℕ) →
      ((((ℕ × ℕ) × ℕ) × ℝ) × (ℝ × ℝ)) :=
    fun z ↦ ((enc z, if z.1.2 then a else 0),
      (if z.1.2 then fluidInfectious l ti else 0,
       if z.1.2 then fluidSusceptible l ts else 1))
  let X : (n : ℕ) → Model.FinitePath (2 * n + 1) →
      ((((ℕ × ℕ) × ℕ) × ℝ) × (ℝ × ℝ)) := fun n p ↦ g (T n p)
  let Y : (n : ℕ) → Model.FinitePath (2 * n + 1) →
      ((((ℕ × ℕ) × ℕ) × ℝ) × (ℝ × ℝ)) :=
    fun n p ↦ ((enc (T n p), H n p), (I n p, S n p))
  have hg : Continuous g := continuous_of_discreteTopology
  have htriple := realThresholdEarlyTriple_tendstoInDistribution
    rates hl hδ hrates
  have hgraph : TendstoInDistribution X atTop (g ∘ localEarlyTriple l)
      (fun n ↦ Model.pathMeasure (rates n) n (2 * n + 1))
      birthParentLaw := by
    simpa only [X, T, Function.comp_def] using htriple.continuous_comp hg
  have hX : ∀ n, Measurable (X n) := fun n ↦ Model.FinitePath.measurable _
  have hY : ∀ n, Measurable (Y n) := fun n ↦ Model.FinitePath.measurable _
  have hXY (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n ↦ (Model.pathMeasure (rates n) n (2 * n + 1)).real
        {p | ε ≤ dist (Y n p) (X n p)}) atTop (𝓝 0) := by
    have hheight := realThresholdHeightLogBad_probability_tendsto_zero
      rates hl hδ hrates hε
    have hfluid := realThreshold_joint_fluid_compact_time_concentration
      rates hl hδ hti hrates hε
    have hsum := hheight.add hfluid
    simp only [add_zero] at hsum
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
    apply Eventually.of_forall
    intro n
    let B : Set (Model.FinitePath (2 * n + 1)) :=
      realThresholdHeightLogBad l δ ε n ∪ realThresholdJointFluidBad l δ ti ε n
    have hsub : {p | ε ≤ dist (Y n p) (X n p)} ⊆ B := by
      intro p hp
      by_contra hnot
      have hh : |H n p - (if (T n p).1.2 then a else 0)| < ε := by
        have hnotH : p ∉ realThresholdHeightLogBad l δ ε n :=
          fun h ↦ hnot (Or.inl h)
        have hreal : (if (T n p).1.2 then a else 0) =
            if (1 - δ) * fluidExtinctionTime l * n ≤
                ((2 * p.last.vertices - 1 : ℕ) : ℝ) then a else 0 := by
          simp [T, realThresholdEarlyTriple, realThresholdEarlyPair]
        change ¬ ε ≤ |H n p - (if (1 - δ) * fluidExtinctionTime l * n ≤
          ((2 * p.last.vertices - 1 : ℕ) : ℝ) then a else 0)| at hnotH
        rw [← hreal] at hnotH
        exact lt_of_not_ge hnotH
      have hi : |I n p - (if (T n p).1.2 then fluidInfectious l ti else 0)| < ε := by
        have hnotF : p ∉ realThresholdJointFluidBad l δ ti ε n :=
          fun h ↦ hnot (Or.inr h)
        have hreal : (if (T n p).1.2 then fluidInfectious l ti else 0) =
            if (1 - δ) * fluidExtinctionTime l * n ≤
                ((2 * p.last.vertices - 1 : ℕ) : ℝ) then fluidInfectious l ti else 0 := by
          simp [T, realThresholdEarlyTriple, realThresholdEarlyPair]
        by_contra hlarge
        apply hnotF
        left
        refine ⟨ti, ⟨hti, le_rfl⟩, ?_⟩
        change ε ≤ |I n p - (if (1 - δ) * fluidExtinctionTime l * n ≤
          ((2 * p.last.vertices - 1 : ℕ) : ℝ) then fluidInfectious l ti else 0)|
        rw [← hreal]
        exact le_of_not_gt hlarge
      have hs : |S n p - (if (T n p).1.2 then fluidSusceptible l ts else 1)| < ε := by
        have hnotF : p ∉ realThresholdJointFluidBad l δ ti ε n :=
          fun h ↦ hnot (Or.inr h)
        have hreal : (if (T n p).1.2 then fluidSusceptible l ts else 1) =
            if (1 - δ) * fluidExtinctionTime l * n ≤
                ((2 * p.last.vertices - 1 : ℕ) : ℝ) then fluidSusceptible l ts else 1 := by
          simp [T, realThresholdEarlyTriple, realThresholdEarlyPair]
        by_contra hlarge
        apply hnotF
        right
        refine ⟨ts, hts, ?_⟩
        change ε ≤ |S n p - (if (1 - δ) * fluidExtinctionTime l * n ≤
          ((2 * p.last.vertices - 1 : ℕ) : ℝ) then fluidSusceptible l ts else 1)|
        rw [← hreal]
        exact le_of_not_gt hlarge
      have hdist : dist (Y n p) (X n p) < ε := by
        simp only [Y, X, g, Prod.dist_eq, dist_self]
        rw [max_eq_right (dist_nonneg)]
        exact max_lt (by simpa only [Real.dist_eq] using hh)
          (max_lt (by simpa only [Real.dist_eq] using hi)
            (by simpa only [Real.dist_eq] using hs))
      exact (not_le.mpr hdist) hp
    let μ := Model.pathMeasure (rates n) n (2 * n + 1)
    have h := (measureReal_mono (μ := μ) hsub (measure_ne_top _ _)).trans
      (measureReal_union_le (μ := μ) _ _)
    simpa only [B] using h
  have hweak := HeightPaper.tendstoInDistribution_of_dist_probability_zero_varying
    hgraph hX hY hXY
  let d : (((((ℕ × ℕ) × ℕ) × ℝ) × (ℝ × ℝ))) →
      (((((ℕ × Bool) × ℕ) × ℝ) × (ℝ × ℝ))) :=
    fun z ↦ ((dec z.1.1, z.1.2), z.2)
  have hdec : Continuous dec := continuous_of_discreteTopology
  have hd : Continuous d :=
    (((hdec.comp continuous_fst).prodMk continuous_snd).comp continuous_fst).prodMk
      continuous_snd
  have hfinal := hweak.continuous_comp hd
  have hdY (n : ℕ) (p : Model.FinitePath (2 * n + 1)) :
      d (Y n p) = ((T n p, H n p), (I n p, S n p)) := by
    simp only [d, Y, hdecenc]
  have hdg (z : ((ℕ × Bool) × ℕ)) :
      d (g z) = ((z, if z.1.2 then a else 0),
        (if z.1.2 then fluidInfectious l ti else 0,
         if z.1.2 then fluidSusceptible l ts else 1)) := by
    simp only [d, g, hdecenc]
  simpa only [Function.comp_def, hdY, hdg, T, H, I, S, a] using hfinal

end HeightPaper.CountCoupling
