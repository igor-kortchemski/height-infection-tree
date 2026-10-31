module

public import HeightPaper.Probability.CorrectedCouplingEmittedWord
public import HeightPaper.Probability.CorrectedCouplingPastAcceptance

/-!
# The law of the word emitted by the coupled construction

Disjoint predictable emissions preserve the conditional cylinder factors,
including the word's continuation after the middle forest has become empty.
The joint law with the middle genealogy is a separate obligation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace HeightPaper.CountCoupling

theorem firstLongWord_min (W : ℕ → List Bool) (k : ℕ)
    {j : ℕ} (hj : j < firstLongWord W k) : (W j).length ≤ k := by
  classical
  have hnot := Nat.find_min (word_index_exists W k) hj
  by_contra h
  exact hnot (Or.inl (by omega))

theorem correctedCoupling_emission_exists
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ k, ∃ j, k < correctedCouplingClock roots p q r w j) (k : ℕ) :
    ∃ j, correctedCouplingClock roots p q r w j = k ∧
      (correctedCouplingStage roots p q r w j).emit p q r (w (0, j)) = true := by
  let W := fun j ↦ (correctedCouplingStage roots p q r w j).word
  have hgt := firstLongWord_spec W k (hunbounded k)
  cases ht : firstLongWord W k with
  | zero =>
      simp [ht, W, correctedCouplingStage, CorrectedCouplingState.initial] at hgt
  | succ j =>
      have hle := firstLongWord_min W k (show j < firstLongWord W k by rw [ht]; omega)
      change correctedCouplingClock roots p q r w j ≤ k at hle
      have hgt' : k < correctedCouplingClock roots p q r w (j + 1) := by
        simpa only [ht, W, correctedCouplingClock] using hgt
      have hs := correctedCouplingClock_succ roots p q r w j
      cases he : (correctedCouplingStage roots p q r w j).emit p q r (w (0, j))
      · simp only [he, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hs
        omega
      · simp only [he, ↓reduceIte] at hs
        exact ⟨j, by omega, he⟩

theorem correctedCouplingClock_lt_after_emission
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) {i j : ℕ} (hij : i < j)
    (he : (correctedCouplingStage roots p q r w i).emit p q r (w (0, i)) = true) :
    correctedCouplingClock roots p q r w i < correctedCouplingClock roots p q r w j := by
  have hs := correctedCouplingClock_succ roots p q r w i
  simp only [he, ↓reduceIte] at hs
  calc
    correctedCouplingClock roots p q r w i <
        correctedCouplingClock roots p q r w i + 1 := Nat.lt_succ_self _
    _ = correctedCouplingClock roots p q r w (i + 1) := hs.symm
    _ ≤ correctedCouplingClock roots p q r w j :=
      correctedCouplingClock_monotone roots p q r w (Nat.succ_le_of_lt hij)

theorem correctedCoupling_word_emission_cover
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ)
    (hunbounded : ∀ k, ∃ j, k < correctedCouplingClock roots p q r w j)
    (a : List Bool) :
    (∃ j, (correctedCouplingStage roots p q r w j).word = a ∧
      (correctedCouplingStage roots p q r w j).emit p q r (w (0, j)) = true) ↔
      sourceCouplingPrefix (correctedCouplingEmittedWord roots p q r w) a.length = a := by
  constructor
  · rintro ⟨j, hj, _⟩
    have hp := sourceCouplingPrefix_correctedCouplingEmittedWord roots p q r w hunbounded j
    simpa only [correctedCouplingClock, hj] using hp
  · intro ha
    obtain ⟨j, hj, he⟩ := correctedCoupling_emission_exists roots p q r w hunbounded a.length
    have hp := sourceCouplingPrefix_correctedCouplingEmittedWord roots p q r w hunbounded j
    rw [hj] at hp
    exact ⟨j, hp.symm.trans ha, he⟩

theorem correctedCoupling_word_emissions_pairwise
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ) (a : List Bool) :
    Pairwise (Disjoint on fun j : ℕ ↦
      {w : (Fin 2 × ℕ) → ℝ | (correctedCouplingStage roots p q r w j).word = a ∧
        (correctedCouplingStage roots p q r w j).emit p q r (w (0, j)) = true}) := by
  have hlt {i j : ℕ} (hij : i < j) : Disjoint
      {w : (Fin 2 × ℕ) → ℝ | (correctedCouplingStage roots p q r w i).word = a ∧
        (correctedCouplingStage roots p q r w i).emit p q r (w (0, i)) = true}
      {w : (Fin 2 × ℕ) → ℝ | (correctedCouplingStage roots p q r w j).word = a ∧
        (correctedCouplingStage roots p q r w j).emit p q r (w (0, j)) = true} := by
    apply Set.disjoint_left.mpr
    intro w hi hj
    have hc := correctedCouplingClock_lt_after_emission roots p q r w hij hi.2
    have hei := congrArg List.length hi.1
    have hej := congrArg List.length hj.1
    change (correctedCouplingStage roots p q r w i).word.length <
      (correctedCouplingStage roots p q r w j).word.length at hc
    omega
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt h
  · exact (hlt h).symm

noncomputable def couplingEmissionCodeSet (p q : ℝ) (r : List Bool → ℝ)
    (a : List Bool) : Set (FiniteCouplingState × ℝ) :=
  {z | z.1.word = a ∧ z.1.toState.emit p q r z.2 = true}

theorem measurableSet_couplingEmissionCodeSet (p q : ℝ) (r : List Bool → ℝ)
    (a : List Bool) : MeasurableSet (couplingEmissionCodeSet p q r a) := by
  have he : Measurable (fun z : FiniteCouplingState × ℝ ↦
      z.1.toState.emit p q r z.2) :=
    measurable_from_prod_countable_right (fun s ↦ s.measurable_emit p q r)
  exact (((measurable_of_countable (fun s : FiniteCouplingState ↦ s.word)).comp
    measurable_fst) (measurableSet_singleton a)).inter (he (measurableSet_singleton true))

theorem mem_couplingEmissionCodeSet_stage
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (a : List Bool) (j : ℕ) :
    (finiteCouplingStage roots p q r w j, w (0, j)) ∈ couplingEmissionCodeSet p q r a ↔
      (correctedCouplingStage roots p q r w j).word = a ∧
        (correctedCouplingStage roots p q r w j).emit p q r (w (0, j)) = true := by
  rw [← finiteCouplingStage_toState roots p q r w j]
  rfl

theorem unitUniform_threshold_probability {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (b : Bool) :
    unitUniform {u | recoveryThresholdBirth t u = b} = adaptiveStepMass t b := by
  cases b
  · simpa [recoveryThresholdBirth, adaptiveStepMass, not_le] using
      unitUniform_lt_of_unit ht0 ht1
  · simpa [recoveryThresholdBirth, adaptiveStepMass] using
      unitUniform_ge_of_unit ht0 ht1

/-- Every cylinder of the actual emitted word has the prescribed conditional
event factor. The proof includes emissions after middle extinction. -/
theorem correctedCouplingEmittedWord_cylinder_factor
    (N : ℕ) (hN : 0 < N) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (q : ℝ) (r : List Bool → ℝ) (hr : ∀ a, 0 ≤ r a ∧ r a ≤ 1)
    (a : List Bool) (b : Bool) :
    pairedUniformLaw {w | sourceCouplingPrefix
      (correctedCouplingEmittedWord (Finset.range N) p q r w) (a.length + 1) = a ++ [b]} =
    pairedUniformLaw {w | sourceCouplingPrefix
      (correctedCouplingEmittedWord (Finset.range N) p q r w) a.length = a} *
        adaptiveStepMass (r a) b := by
  let roots := Finset.range N
  let X : ℕ → ((Fin 2 × ℕ) → ℝ) → FiniteCouplingState × ℝ :=
    fun j w ↦ (finiteCouplingStage roots p q r w j, w (0, j))
  let E := couplingEmissionCodeSet p q r a
  let H : Set ((Fin 2 × ℕ) → ℝ) := {w | sourceCouplingPrefix
    (correctedCouplingEmittedWord roots p q r w) a.length = a}
  let D : Set ℝ := {u | recoveryThresholdBirth (r a) u = b}
  have hX (j : ℕ) : Measurable (X j) :=
    (measurable_finiteCouplingStage roots p q r j).prodMk (measurable_pi_apply (0, j))
  have hR (j : ℕ) : Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦ w (1, j)) :=
    measurable_pi_apply (1, j)
  have hind (j : ℕ) : IndepFun (X j) (fun w : (Fin 2 × ℕ) → ℝ ↦ w (1, j))
      pairedUniformLaw :=
    causal_state_parent_indep_recovery j _ (measurable_finiteCouplingStage roots p q r j)
      (fun _ _ hh ↦ finiteCouplingStage_congr_prefix roots p q r j hh)
  have hE : MeasurableSet E := measurableSet_couplingEmissionCodeSet p q r a
  have hD : MeasurableSet D :=
    (measurable_recoveryThresholdBirth (r a)) (measurableSet_singleton b)
  have hevents (j : ℕ) : (X j) ⁻¹' E =
      {w | (correctedCouplingStage roots p q r w j).word = a ∧
        (correctedCouplingStage roots p q r w j).emit p q r (w (0, j)) = true} := by
    ext w
    exact mem_couplingEmissionCodeSet_stage roots p q r w a j
  have hpair : Pairwise (Disjoint on fun j ↦ (X j) ⁻¹' E) := by
    simpa only [hevents] using correctedCoupling_word_emissions_pairwise roots p q r a
  have hcover : pairedUniformLaw (⋃ j, (X j) ⁻¹' E) = pairedUniformLaw H := by
    apply measure_congr
    filter_upwards [correctedCouplingClock_ae_unbounded N hN hp hp1 q r] with w hw
    apply propext
    simp only [Set.mem_iUnion, hevents, Set.mem_ofPred_eq]
    exact correctedCoupling_word_emission_cover roots p q r w hw a
  have hmass := emission_joint_probability_of_cover pairedUniformLaw X
    (fun j w ↦ w (1, j)) hX hR hind
    (fun j ↦ pairedUniformLaw_map_eval (1, j)) (fun _ ↦ E) (fun _ ↦ hE)
    hpair H hcover D hD
  have hleft : pairedUniformLaw {w | sourceCouplingPrefix
      (correctedCouplingEmittedWord roots p q r w) (a.length + 1) = a ++ [b]} =
      pairedUniformLaw (⋃ j, (X j) ⁻¹' E ∩ (fun w ↦ w (1, j)) ⁻¹' D) := by
    apply measure_congr
    filter_upwards [correctedCouplingClock_ae_unbounded N hN hp hp1 q r] with w hw
    apply propext
    have hprefix : sourceCouplingPrefix (correctedCouplingEmittedWord roots p q r w)
        (a.length + 1) = a ++ [b] ↔
        sourceCouplingPrefix (correctedCouplingEmittedWord roots p q r w) a.length = a ∧
          correctedCouplingEmittedWord roots p q r w a.length = b := by
      simpa [sourceCylinder, List.length_append] using
        mem_sourceCylinder_append (correctedCouplingEmittedWord roots p q r w) a b
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage, hevents]
    rw [hprefix]
    constructor
    · rintro ⟨ha, hb⟩
      obtain ⟨j, hj, he⟩ := (correctedCoupling_word_emission_cover roots p q r w hw a).mpr ha
      have hletter := correctedCouplingEmittedWord_at_emission roots p q r w hw j he
      simp only [correctedCouplingClock, hj] at hletter
      exact ⟨j, ⟨hj, he⟩, by simpa only [D, Set.mem_ofPred_eq, hj, ← hletter] using hb⟩
    · rintro ⟨j, ⟨hj, he⟩, hb⟩
      have hletter := correctedCouplingEmittedWord_at_emission roots p q r w hw j he
      simp only [correctedCouplingClock, hj] at hletter
      exact ⟨(correctedCoupling_word_emission_cover roots p q r w hw a).mp ⟨j, hj, he⟩,
        hletter.trans hb⟩
  rw [hleft, hmass, unitUniform_threshold_probability (hr a).1 (hr a).2 b]

/-- The actual emitted process, rather than an unrelated adaptive word,
has the prescribed complete source law. -/
theorem correctedCouplingEmittedWord_law
    (N : ℕ) (hN : 0 < N) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (q : ℝ) (r : List Bool → ℝ) (hr : ∀ a, 0 ≤ r a ∧ r a ≤ 1)
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (hfactor : ∀ (k : ℕ) (a : List Bool) (b : Bool), a.length = k →
      μ {x | sourceCouplingPrefix x (k + 1) = a ++ [b]} =
        μ {x | sourceCouplingPrefix x k = a} * adaptiveStepMass (r a) b) :
    pairedUniformLaw.map (correctedCouplingEmittedWord (Finset.range N) p q r) = μ := by
  let ν := pairedUniformLaw.map (correctedCouplingEmittedWord (Finset.range N) p q r)
  have hm := measurable_correctedCouplingEmittedWord (Finset.range N) p q r
  have hfν (k : ℕ) (a : List Bool) (b : Bool) (ha : a.length = k) :
      ν {x | sourceCouplingPrefix x (k + 1) = a ++ [b]} =
        ν {x | sourceCouplingPrefix x k = a} * adaptiveStepMass (r a) b := by
    dsimp only [ν]
    have hs : MeasurableSet {x : ℕ → Bool | sourceCouplingPrefix x (k + 1) = a ++ [b]} :=
      (measurable_sourceCouplingPrefix (k + 1)) (measurableSet_singleton _)
    have ht : MeasurableSet {x : ℕ → Bool | sourceCouplingPrefix x k = a} :=
      (measurable_sourceCouplingPrefix k) (measurableSet_singleton _)
    rw [Measure.map_apply hm hs, Measure.map_apply hm ht]
    simpa only [Set.preimage_ofPred_eq, ha] using
      correctedCouplingEmittedWord_cylinder_factor N hN hp hp1 q r hr a b
  exact (sourceCouplingProcess_law_of_cylinder_factors ν r hr hfν).trans
    (sourceCouplingProcess_law_of_cylinder_factors μ r hr hfactor).symm

theorem correctedCouplingEmittedWord_canonical_law
    (N : ℕ) (hN : 0 < N) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (q : ℝ) (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ] :
    pairedUniformLaw.map (correctedCouplingEmittedWord (Finset.range N) p q
      (sourceRecoveryRate μ)) = μ :=
  correctedCouplingEmittedWord_law N hN hp hp1 q (sourceRecoveryRate μ)
    (sourceRecoveryRate_mem_unit μ) μ (sourceRecoveryRate_factors μ)

end HeightPaper.CountCoupling
