module

public import HeightPaper.Probability.CorrectedCouplingReferenceHistory

/-!
# Equality of the complete logical token laws

Countable complete-tree histories, rather than one-time height marginals,
determine the full joint event/forest process.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

theorem measure_eq_of_tokenPrefix_laws
    (μ ν : Measure (ℕ → CouplingToken)) [IsFiniteMeasure μ]
    (h : ∀ k : ℕ, μ.map (fun x ↦ couplingTokenPrefix x k) =
      ν.map (fun x ↦ couplingTokenPrefix x k)) : μ = ν := by
  classical
  refine ext_of_generate_finite (measurableCylinders (fun _ : ℕ ↦ CouplingToken))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro C hC
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hC
    let k := I.sup id + 1
    let d : CouplingToken := (false, FiniteCouplingGenealogy.initial ∅)
    let f : List CouplingToken → (∀ i : I, CouplingToken) := fun w i ↦ w.getD i.val d
    have hf (x : ℕ → CouplingToken) : f (couplingTokenPrefix x k) = Finset.restrict I x := by
      funext i
      have hi : i.val < k := Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)
      change (couplingTokenPrefix x k).getD i.val d = x i.val
      rw [List.getD_eq_getElem _ _ (by simpa only [couplingTokenPrefix_length] using hi)]
      simp only [couplingTokenPrefix, List.getElem_ofFn]
    have hm : Measurable f := measurable_of_countable f
    have heq : (Finset.restrict I : (ℕ → CouplingToken) → (∀ i : I, CouplingToken)) =
        f ∘ (fun x ↦ couplingTokenPrefix x k) := by funext x; exact (hf x).symm
    have hmap : μ.map (Finset.restrict I) = ν.map (Finset.restrict I) := by
      rw [heq, ← Measure.map_map hm (measurable_couplingTokenPrefix k),
        ← Measure.map_map hm (measurable_couplingTokenPrefix k), h k]
    have hmI : Measurable (Finset.restrict I : (ℕ → CouplingToken) → (∀ i : I, CouplingToken)) :=
      Measurable.of_eval (fun _ ↦ measurable_pi_apply _)
    change μ ((Finset.restrict I) ⁻¹' S) = ν ((Finset.restrict I) ⁻¹' S)
    simpa only [Measure.map_apply hmI hS] using
      congrArg (fun ρ : Measure (∀ i : I, CouplingToken) ↦ ρ S) hmap
  · have h0 := congrArg (fun ρ : Measure (List CouplingToken) ↦ ρ Set.univ) (h 0)
    simpa [Measure.map_apply (measurable_couplingTokenPrefix 0)] using h0

theorem correctedCoupling_joint_prefix_mass
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hp1 : p ≤ 1)
    (r : List Bool → ℝ) (h : List CouplingToken) :
    pairedUniformLaw (jointPrefixEvent N p q r h) = pairedUniformLaw (referencePrefixEvent N r h) := by
  induction h using List.reverseRecOn with
  | nil => simp [jointPrefixEvent, referencePrefixEvent, referenceJointHistory]
  | append_singleton h t ih =>
      rw [correctedCoupling_joint_cylinder_factor N hN hp hpq hp1 r h t,
        reference_joint_cylinder_factor N r h t, ih]

theorem correctedCouplingLogicalToken_law
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hp1 : p ≤ 1)
    (r : List Bool → ℝ) :
    pairedUniformLaw.map (correctedCouplingLogicalToken N p q r) =
      pairedUniformLaw.map (referenceLogicalToken N r) := by
  have hm : Measurable (correctedCouplingLogicalToken N p q r) :=
    measurable_pi_iff.mpr (measurable_correctedCouplingLogicalToken N p q r)
  have hrm : Measurable (referenceLogicalToken N r) :=
    measurable_pi_iff.mpr (measurable_referenceLogicalToken N r)
  apply measure_eq_of_tokenPrefix_laws
  intro k
  rw [Measure.map_map (measurable_couplingTokenPrefix k) hm,
    Measure.map_map (measurable_couplingTokenPrefix k) hrm]
  apply Measure.ext_of_singleton
  intro h
  rw [Measure.map_apply ((measurable_couplingTokenPrefix k).comp hm) (measurableSet_singleton h),
    Measure.map_apply ((measurable_couplingTokenPrefix k).comp hrm) (measurableSet_singleton h)]
  by_cases hlen : h.length = k
  · subst k
    change pairedUniformLaw {w | couplingTokenPrefix (correctedCouplingLogicalToken N p q r w) h.length = h} =
      pairedUniformLaw {w | couplingTokenPrefix (referenceLogicalToken N r w) h.length = h}
    simpa only [referenceJointHistory_eq_tokenPrefix, jointPrefixEvent, referencePrefixEvent] using
        correctedCoupling_joint_prefix_mass N hN hp hpq hp1 r h
  · have hzero (X : ((Fin 2 × ℕ) → ℝ) → ℕ → CouplingToken) :
        (fun w ↦ couplingTokenPrefix (X w) k) ⁻¹' {h} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have he : couplingTokenPrefix (X w) k = h := hw
      exact hlen ((congrArg List.length he).symm.trans (couplingTokenPrefix_length _ _))
    change pairedUniformLaw ((fun w ↦ couplingTokenPrefix (correctedCouplingLogicalToken N p q r w) k) ⁻¹' {h}) =
      pairedUniformLaw ((fun w ↦ couplingTokenPrefix (referenceLogicalToken N r w) k) ⁻¹' {h})
    rw [hzero, hzero]

end HeightPaper.CountCoupling
