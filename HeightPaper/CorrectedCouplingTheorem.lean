module

public import HeightPaper.Probability.CorrectedCouplingForestValidity
public import HeightPaper.Probability.CorrectedCouplingHeightComparison

/-!
# The authorized correction of `lem:couplage`

The favorable event is `sourceCorrectedGood`: recovery bounds hold through
the terminal extinction event, with no condition after extinction. This is
the corrected statement, not the false event in the printed lemma.

The middle retains the complete joint source word/forest law. Both bounding
families have genuine iid geometric Bienaymé tree laws. Root-preserving
parent-edge embeddings hold almost surely on the corrected event, and one
height constant works uniformly in N, root, source law, and real threshold.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper

open CountCoupling PlaneForward PlaneTree

def CorrectedCouplingForSource (p q : unitInterval) (C : ℝ) (N : ℕ)
    (μ : Measure (ℕ → Bool)) (r : List Bool → ℝ) : Prop :=
  ∃ (X : ((Fin 2 × ℕ) → ℝ) → ℕ → Bool)
    (M : ((Fin 2 × ℕ) → ℝ) → ForestCode)
    (L U : ((Fin 2 × ℕ) → ℝ) → Fin N → FiniteShape),
    Measurable X ∧ Measurable M ∧ Measurable L ∧ Measurable U ∧
    pairedUniformLaw.map (fun w ↦ (X w, M w)) =
      (μ.prod uniformLaw).map (fun z ↦ (z.1, trajectoryForestCode N (sourceForestTrajectory N z.1 z.2))) ∧
    pairedUniformLaw.map (fun w i ↦ (L w i).tree) =
      Measure.pi (fun _ : Fin N ↦ bienaymeLaw (geometricMeasure q)) ∧
    pairedUniformLaw.map (fun w i ↦ (U w i).tree) =
      Measure.pi (fun _ : Fin N ↦ bienaymeLaw (geometricMeasure p)) ∧
    iIndepFun (fun i : Fin N ↦ fun w ↦ (L w i).tree) pairedUniformLaw ∧
    iIndepFun (fun i : Fin N ↦ fun w ↦ (U w i).tree) pairedUniformLaw ∧
    (∀ᵐ w ∂pairedUniformLaw, RootedForest.WellRooted (forestOfCode N (M w))) ∧
    (∀ᵐ w ∂pairedUniformLaw, sourceCorrectedGood N p q r (X w) →
      Nonempty (RootedForest.Embedding (planeForest (fun i ↦ (L w i).tree)) (forestOfCode N (M w))) ∧
      Nonempty (RootedForest.Embedding (forestOfCode N (M w)) (planeForest (fun i ↦ (U w i).tree)))) ∧
    (∀ (i : Fin N) (h : ℝ), 0 ≤ h →
      (1 / C) * (1 / (q : ℝ) - 1) ^ h ≤ pairedUniformLaw.real {w | h ≤ ((L w i).height : ℝ)} ∧
      pairedUniformLaw.real {w | h ≤ ((L w i).height : ℝ)} ≤
        pairedUniformLaw.real {w | h ≤ ((U w i).height : ℝ)} ∧
      pairedUniformLaw.real {w | h ≤ ((U w i).height : ℝ)} ≤ C * (1 / (p : ℝ) - 1) ^ h)

def CorrectedCouplingStatement : Prop :=
  ∀ (p q : unitInterval), 1 / 2 < (p : ℝ) → p ≤ q → (q : ℝ) < 1 →
  ∃ C > (0 : ℝ), ∀ (N : ℕ), 0 < N →
  ∀ (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ] (r : List Bool → ℝ),
    (∀ a, 0 ≤ r a ∧ r a ≤ 1) →
    (∀ (k : ℕ) (a : List Bool) (b : Bool), a.length = k →
      μ {x | sourceCouplingPrefix x (k + 1) = a ++ [b]} =
        μ {x | sourceCouplingPrefix x k = a} * adaptiveStepMass (r a) b) →
    CorrectedCouplingForSource p q C N μ r

/-- The complete corrected coupling, with the constant quantified before all
source and component parameters. -/
theorem correctedCouplingTheorem : CorrectedCouplingStatement := by
  intro p q hp hpq hq1
  obtain ⟨C, hC, htail⟩ := exists_bounding_real_height_tail_comparison p q hp hpq hq1
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ r hr hfactor
  let _ := hμ
  have hpqR : (p : ℝ) ≤ (q : ℝ) := hpq
  have hp1 : (p : ℝ) ≤ 1 := hpqR.trans q.2.2
  let X := correctedCouplingEmittedWord (Finset.range N) p q r
  let M := correctedMiddleLimitCode N p q r
  let L := terminalBoundShape N p q r false
  let U := terminalBoundShape N p q r true
  refine ⟨X, M, L, U, measurable_correctedCouplingEmittedWord _ _ _ _,
    measurable_correctedMiddleLimitCode _ _ _ _, measurable_terminalBoundShape _ _ _ _ _,
    measurable_terminalBoundShape _ _ _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact correctedMiddleLimitCode_joint_law N hN hp hpqR hp1 μ r hr hfactor
  · change pairedUniformLaw.map (terminalBoundTree N p q r false) = _
    simpa only [boundForestParameter, Bool.false_eq_true, ↓reduceIte] using
      terminalBoundTree_law_eq_pi N hN p q hp hpq r false
  · change pairedUniformLaw.map (terminalBoundTree N p q r true) = _
    simpa only [boundForestParameter, ↓reduceIte] using
      terminalBoundTree_law_eq_pi N hN p q hp hpq r true
  · exact terminalBoundTree_independent N hN p q hp hpq r false
  · exact terminalBoundTree_independent N hN p q hp hpq r true
  · exact correctedMiddleLimitCode_ae_wellRooted N hN hp hpqR q.2.2 r
  · exact correctedCoupling_rooted_sandwich_ae N hN hp hpqR q.2.2 r
  · exact fun i h hh ↦ htail N hN r i h hh

/-- No conditional-rate hypotheses need be supplied for an arbitrary binary
source measure: its canonical cylinder ratios satisfy them automatically. -/
theorem correctedCoupling_canonical (p q : unitInterval) (hp : 1 / 2 < (p : ℝ))
    (hpq : p ≤ q) (hq1 : (q : ℝ) < 1) :
    ∃ C > (0 : ℝ), ∀ (N : ℕ), 0 < N →
      ∀ (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ],
        CorrectedCouplingForSource p q C N μ (sourceRecoveryRate μ) := by
  obtain ⟨C, hC, hsource⟩ := correctedCouplingTheorem p q hp hpq hq1
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ
  let _ := hμ
  exact hsource N hN μ (sourceRecoveryRate μ) (sourceRecoveryRate_mem_unit μ) (sourceRecoveryRate_factors μ)

end HeightPaper
