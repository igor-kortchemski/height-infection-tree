module

public import HeightPaper.Probability.VaryingSourceStability
public import HeightPaper.Probability.EarlyHeightMarginalDistribution

/-!
# Joint weak convergence of early coordinates and cutoff height

The real-threshold early triple and normalized cutoff height converge together
as a random element of the product of the discrete early-coordinate space and
the real line. The proof uses the varying-source stability lemma because the
finite path probability space depends on the population size.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal Classical

namespace HeightPaper.CountCoupling

theorem realThresholdEarlyTriple_heightLog_tendstoInDistribution
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    TendstoInDistribution
      (fun (n : ℕ) p ↦
        (realThresholdEarlyTriple l δ n p,
          (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) / Real.log n))
      atTop
      (fun q ↦
        (localEarlyTriple l q,
          if (localEarlyTriple l q).1.2 then
            growthFactor l * Real.exp (profileRoot l) else 0))
      (fun n ↦ Model.pathMeasure (rates n) n (2 * n + 1))
      birthParentLaw := by
  let a := growthFactor l * Real.exp (profileRoot l)
  let T : (n : ℕ) → Model.FinitePath (2 * n + 1) → ((ℕ × Bool) × ℕ) :=
    fun n ↦ realThresholdEarlyTriple l δ n
  let H : (n : ℕ) → Model.FinitePath (2 * n + 1) → ℝ :=
    fun n p ↦ (Model.height (p.eval (Model.sourceCutoff l δ n)) : ℝ) / Real.log n
  let enc : ((ℕ × Bool) × ℕ) → ((ℕ × ℕ) × ℕ) :=
    fun z ↦ ((z.1.1, if z.1.2 then 1 else 0), z.2)
  let dec : ((ℕ × ℕ) × ℕ) → ((ℕ × Bool) × ℕ) :=
    fun z ↦ ((z.1.1, decide (z.1.2 = 1)), z.2)
  have hdecenc (z : ((ℕ × Bool) × ℕ)) : dec (enc z) = z := by
    rcases z with ⟨⟨k, b⟩, h⟩
    cases b <;> simp [dec, enc]
  let g : ((ℕ × Bool) × ℕ) → (((ℕ × ℕ) × ℕ) × ℝ) :=
    fun z ↦ (enc z, if z.1.2 then a else 0)
  let X : (n : ℕ) → Model.FinitePath (2 * n + 1) →
      (((ℕ × ℕ) × ℕ) × ℝ) := fun n p ↦ g (T n p)
  let Y : (n : ℕ) → Model.FinitePath (2 * n + 1) →
      (((ℕ × ℕ) × ℕ) × ℝ) := fun n p ↦ (enc (T n p), H n p)
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
    have hbad := realThresholdHeightLogBad_probability_tendsto_zero
      rates hl hδ hrates hε
    have hsets (n : ℕ) :
        {p | ε ≤ dist (Y n p) (X n p)} =
          realThresholdHeightLogBad l δ ε n := by
      ext p
      have hreal : (if (T n p).1.2 then a else 0) =
          if (1 - δ) * fluidExtinctionTime l * n ≤
              ((2 * p.last.vertices - 1 : ℕ) : ℝ) then a else 0 := by
        simp [T, realThresholdEarlyTriple, realThresholdEarlyPair]
      simp only [mem_ofPred_eq, X, Y, g, Prod.dist_eq, dist_self,
        Real.dist_eq, realThresholdHeightLogBad]
      rw [max_eq_right (abs_nonneg _)]
      change ε ≤ |H n p - (if (T n p).1.2 then a else 0)| ↔
        ε ≤ |H n p - (if (1 - δ) * fluidExtinctionTime l * n ≤
          ((2 * p.last.vertices - 1 : ℕ) : ℝ) then a else 0)|
      rw [hreal]
    simpa only [hsets] using hbad
  have hweak := HeightPaper.tendstoInDistribution_of_dist_probability_zero_varying
    hgraph hX hY hXY
  let d : ((((ℕ × ℕ) × ℕ) × ℝ)) → ((((ℕ × Bool) × ℕ) × ℝ)) :=
    fun z ↦ (dec z.1, z.2)
  have hdec : Continuous dec := continuous_of_discreteTopology
  have hd : Continuous d := (hdec.comp continuous_fst).prodMk continuous_snd
  have hfinal := hweak.continuous_comp hd
  have hdY (n : ℕ) (p : Model.FinitePath (2 * n + 1)) :
      d (Y n p) = (T n p, H n p) := by
    simp only [d, Y, hdecenc]
  have hdg (z : ((ℕ × Bool) × ℕ)) :
      d (g z) = (z, if z.1.2 then a else 0) := by
    simp only [d, g, hdecenc]
  simpa only [Function.comp_def, hdY, hdg, T, H, a] using hfinal

end HeightPaper.CountCoupling
