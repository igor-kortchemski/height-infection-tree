module

public import HeightPaper.Probability.CompactFluidDistribution
public import HeightPaper.Probability.CountableProductInMeasure

/-!
# The joint epidemic limit in the local uniform path topology

Integer time horizons encode the topology of uniform convergence on every
compact infectious time interval. The susceptible trajectory is restricted to
the fluid extinction time, as in the paper.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal PiCountable Classical

namespace HeightPaper.CountCoupling

/-- A single random element containing the early data, cutoff height, and
both fluid paths on all compact infectious time horizons. -/
abbrev LocalFluidJoint (l : ℝ) :=
  (k : ℕ) → CompactFluidJoint l (k : ℝ)

noncomputable instance (l : ℝ) : MeasurableSpace (LocalFluidJoint l) := borel _

instance (l : ℝ) : BorelSpace (LocalFluidJoint l) := ⟨rfl⟩

noncomputable def sourceLocalFluidJoint (l δ : ℝ) (n : ℕ)
    (p : Model.FinitePath (2 * n + 1)) : LocalFluidJoint l :=
  fun k ↦ sourceCompactFluidJoint l δ k n p

noncomputable def localLocalFluidJoint (l : ℝ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) : LocalFluidJoint l :=
  fun k ↦ localCompactFluidJoint l k q

noncomputable def localFluidJointOfTriple (l : ℝ)
    (z : (ℕ × Bool) × ℕ) : LocalFluidJoint l :=
  fun k ↦ {
    early := z
    heightLog := if z.1.2 then
      growthFactor l * Real.exp (profileRoot l) else 0
    fluid := ⟨UniformOnFun.ofFun {Icc (0 : ℝ) (k : ℝ)}
        (fun t ↦ if z.1.2 then fluidInfectious l t else 0),
      UniformOnFun.ofFun {Icc (0 : ℝ) (fluidExtinctionTime l)}
        (fun t ↦ if z.1.2 then fluidSusceptible l t else 1)⟩
  }

private theorem measurable_localLocalFluidJoint (l : ℝ) :
    Measurable (localLocalFluidJoint l) := by
  have hbit : Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      decide (q.1 ∈ localSurvival l)) := by
    apply measurable_to_bool
    convert (measurableSet_localSurvival l).preimage measurable_fst using 1
    ext q
    simp
  have htriple : Measurable (localEarlyTriple l) := by
    exact (((measurable_localEarlyExtinctionTime l).comp measurable_fst).prodMk
      hbit).prodMk (measurable_localEarlyHeight l)
  have heq : localLocalFluidJoint l =
      localFluidJointOfTriple l ∘ localEarlyTriple l := by
    funext q k
    by_cases hs : q.1 ∈ localSurvival l <;>
      simp [localLocalFluidJoint, localFluidJointOfTriple,
        localCompactFluidJoint, localCompactFluidPaths,
        localEarlyTriple, localEarlyTimeSurvivalPair, hs]
  rw [heq]
  exact (measurable_of_countable (localFluidJointOfTriple l)).comp htriple

theorem coupled_sourceLocalFluidJoint_tendstoInMeasure
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    TendstoInMeasure birthParentLaw
      (fun n q ↦ sourceLocalFluidJoint l δ n
        (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q))
      atTop (localLocalFluidJoint l) := by
  apply tendstoInMeasure_countablePi
  intro k
  exact coupled_sourceCompactFluidJoint_tendstoInMeasure
    rates hl hδ (Nat.cast_nonneg k) hrates

theorem coupled_sourceLocalFluidJoint_tendstoInDistribution
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    TendstoInDistribution
      (fun n q ↦ sourceLocalFluidJoint l δ n
        (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q))
      atTop (localLocalFluidJoint l)
      (fun _ ↦ birthParentLaw) birthParentLaw := by
  apply (coupled_sourceLocalFluidJoint_tendstoInMeasure
    rates hl hδ hrates).tendstoInDistribution
  intro n
  exact ((Model.FinitePath.measurable (sourceLocalFluidJoint l δ n)).comp
    (measurable_coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1))).aemeasurable

theorem sourceLocalFluidJoint_tendstoInDistribution
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    TendstoInDistribution (fun n ↦ sourceLocalFluidJoint l δ n) atTop
      (localLocalFluidJoint l)
      (fun n ↦ Model.pathMeasure (rates n) n (2 * n + 1)) birthParentLaw := by
  have hcommon := coupled_sourceLocalFluidJoint_tendstoInDistribution
    rates hl hδ hrates
  refine ⟨fun n ↦ (Model.FinitePath.measurable
      (sourceLocalFluidJoint l δ n)).aemeasurable,
    (measurable_localLocalFluidJoint l).aemeasurable, ?_⟩
  have hmap (n : ℕ) (hn : 0 < n) :
      birthParentLaw.map (fun q ↦ sourceLocalFluidJoint l δ n
        (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q)) =
      (Model.pathMeasure (rates n) n (2 * n + 1)).map
        (sourceLocalFluidJoint l δ n) := by
    let a : ℝ≥0 := rates n * n
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
    have hrate : a / n = rates n := by
      dsimp [a]
      field_simp [hn0]
    have hLaw := coupledTreeHistory_law a n (2 * n + 1)
    rw [hrate] at hLaw
    have hmap' : birthParentLaw.map
        (sourceLocalFluidJoint l δ n ∘ coupledTreeHistory a n (2 * n + 1)) =
        (Model.pathMeasure (rates n) n (2 * n + 1)).map
          (sourceLocalFluidJoint l δ n) := by
      rw [← Measure.map_map (Model.FinitePath.measurable _)
        (measurable_coupledTreeHistory a n (2 * n + 1)), hLaw]
    simpa only [Function.comp_def, a, NNReal.coe_mul, NNReal.coe_natCast] using hmap'
  have heq :
      (fun n ↦ (⟨birthParentLaw.map (fun q ↦ sourceLocalFluidJoint l δ n
        (coupledTreeHistory ((rates n : ℝ) * n) n (2 * n + 1) q)), inferInstance⟩ :
          ProbabilityMeasure (LocalFluidJoint l))) =ᶠ[atTop]
      (fun n ↦ (⟨(Model.pathMeasure (rates n) n (2 * n + 1)).map
        (sourceLocalFluidJoint l δ n), inferInstance⟩ :
          ProbabilityMeasure (LocalFluidJoint l))) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact Subtype.ext (hmap n hn)
  exact hcommon.tendsto.congr' heq

end HeightPaper.CountCoupling
