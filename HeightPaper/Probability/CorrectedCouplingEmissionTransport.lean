module

public import HeightPaper.Probability.CorrectedCouplingLogicalToken

/-!
# Transport of a predictable emission law

Only the event deciding emission may depend on the parent coordinate.
The emitted recovery coordinate retains its uniform law on any causal
history, with the mass of that history as weight.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace HeightPaper.CountCoupling

theorem emission_mapped_recovery_on_event
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (R : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hR : ∀ n, Measurable (R n))
    (hind : ∀ n, IndepFun (X n) (R n) μ)
    (hlaw : ∀ n, μ.map (R n) = unitUniform)
    (D : ℕ → Set α) (hD : ∀ n, MeasurableSet (D n))
    (hd : Pairwise (Disjoint on fun n ↦ (X n) ⁻¹' D n))
    (H : Set Ω) (hcover : (⋃ n, (X n) ⁻¹' D n) =ᵐ[μ] H)
    (T : Ω → β) (hT : Measurable T) (F : ℝ → β) (hF : Measurable F)
    (hcongr : ∀ n, T =ᵐ[μ.restrict ((X n) ⁻¹' D n)] F ∘ R n) :
    (μ.restrict H).map T = μ H • unitUniform.map F := by
  let E := fun n ↦ (X n) ⁻¹' D n
  have hE (n : ℕ) : MeasurableSet (E n) := (hD n).preimage (hX n)
  let M := Measure.sum (fun n ↦ (μ.restrict (E n)).map (R n))
  have hM : M = μ H • unitUniform := by
    ext B hB
    have hsets : Pairwise (Disjoint on fun n ↦ E n ∩ (R n) ⁻¹' B) := by
      intro i j hij
      exact (hd hij).mono Set.inter_subset_left Set.inter_subset_left
    have hEB (n : ℕ) : MeasurableSet (E n ∩ (R n) ⁻¹' B) :=
      (hE n).inter (hB.preimage (hR n))
    have hmass := emission_joint_probability_of_cover μ X R hX hR hind hlaw D hD hd H
      (measure_congr hcover) B hB
    rw [Measure.smul_apply, smul_eq_mul, ← hmass, measure_iUnion hsets hEB]
    change Measure.sum (fun n ↦ (μ.restrict (E n)).map (R n)) B = _
    rw [Measure.sum_apply _ hB]
    apply tsum_congr
    intro n
    rw [Measure.map_apply (hR n) hB, Measure.restrict_apply (hB.preimage (hR n))]
    exact congrArg μ (Set.inter_comm _ _)
  calc
    _ = Measure.sum (fun n ↦ (μ.restrict (E n)).map T) :=
      map_restrict_eq_sum_of_ae_partition μ H E hE hd hcover T hT
    _ = Measure.sum (fun n ↦ (μ.restrict (E n)).map (F ∘ R n)) := by
      congr 1
      funext n
      exact Measure.map_congr (hcongr n)
    _ = M.map F := by
      change _ = (Measure.sum (fun n ↦ (μ.restrict (E n)).map (R n))).map F
      rw [Measure.map_sum hF.aemeasurable]
      congr 1
      funext n
      exact (Measure.map_map hF (hR n)).symm
    _ = _ := by rw [hM, Measure.map_smul _ hF.aemeasurable]

theorem sourceMiddleTokenLaw_of_empty
    (g : FiniteCouplingGenealogy) (hg : g.1.carrier.active = ∅) (rate : ℝ) :
    sourceMiddleTokenLaw g rate =
      unitUniform.map (fun u ↦ (recoveryThresholdBirth rate u, g)) := by
  let F : ℝ → Bool × FiniteCouplingGenealogy := fun u ↦ (recoveryThresholdBirth rate u, g)
  have hF : Measurable F := (measurable_recoveryThresholdBirth rate).prodMk measurable_const
  have he : sourceMiddleToken g rate = F ∘ Prod.snd := by
    funext z
    change (_, g.sourceStep _ _) = (_, g)
    rw [g.sourceStep_of_empty hg]
  rw [sourceMiddleTokenLaw, he, ← Measure.map_map hF measurable_snd, Measure.map_snd_prod,
    measure_univ, one_smul]

end HeightPaper.CountCoupling
