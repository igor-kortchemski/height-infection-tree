module

public import HeightPaper.Probability.TreeUniformCoupling
public import HeightPaper.Model.EpidemicEventConditioning

/-! # Exact finite epidemic tree law on the two-uniform coupling space -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Classical

namespace HeightPaper.CountCoupling

open Model

/-- A countable-state transition driven by a fresh independent random draw. -/
theorem independent_pmf_update {Ω α β γ : Type*} [MeasurableSpace Ω]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure Ω) (X : Ω → α) (Z : Ω → β) (f : α → β → γ)
    (p : PMF α) (Q : α → PMF γ)
    (hX : Measurable X) (hZ : Measurable Z) (hf : ∀ a, Measurable (f a))
    (hnew : Measurable (fun ω ↦ f (X ω) (Z ω))) (hind : IndepFun X Z μ)
    (hLaw : μ.map X = p.toMeasure)
    (hQ : ∀ a, μ.map (fun ω ↦ f a (Z ω)) = (Q a).toMeasure) :
    μ.map (fun ω ↦ f (X ω) (Z ω)) = (p.bind Q).toMeasure := by
  ext t ht
  rw [Measure.map_apply hnew ht, PMF.toMeasure_bind_apply p Q t ht]
  have hsplit : (fun ω ↦ f (X ω) (Z ω)) ⁻¹' t =
      ⋃ a, X ⁻¹' {a} ∩ Z ⁻¹' ((f a) ⁻¹' t) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    constructor
    · intro h
      exact ⟨X ω, rfl, h⟩
    · rintro ⟨a, ha, h⟩
      simpa only [ha] using h
  rw [hsplit, measure_iUnion]
  · apply tsum_congr
    intro a
    rw [hind.measure_inter_preimage_eq_mul {a} ((f a) ⁻¹' t)
      (measurableSet_singleton a) ((hf a) ht)]
    have hp : μ (X ⁻¹' {a}) = p a := by
      rw [← Measure.map_apply hX (measurableSet_singleton a), hLaw,
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
    have hq : μ (Z ⁻¹' ((f a) ⁻¹' t)) = (Q a).toMeasure t := by
      change μ ((fun ω ↦ f a (Z ω)) ⁻¹' t) = _
      have hm : Measurable (fun ω ↦ f a (Z ω)) := (hf a).comp hZ
      rw [← Measure.map_apply hm ht, hQ a]
    rw [hp, hq]
  · intro a b hab
    exact Set.disjoint_left.mpr (fun ω ha hb ↦ hab (ha.1.symm.trans hb.1))
  · intro a
    exact (hX (measurableSet_singleton a)).inter (hZ ((hf a) ht))

noncomputable def pairedUniformLaw : Measure ((Fin 2 × ℕ) → ℝ) :=
  Measure.infinitePi (fun _ ↦ unitUniform)

instance : IsProbabilityMeasure pairedUniformLaw := by
  unfold pairedUniformLaw
  infer_instance

def splitUniforms (w : (Fin 2 × ℕ) → ℝ) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (fun k ↦ w (0, k), fun k ↦ w (1, k))

theorem measurable_splitUniforms : Measurable splitUniforms :=
  (measurable_pi_iff.mpr (fun k ↦ measurable_pi_apply (0, k))).prodMk
    (measurable_pi_iff.mpr (fun k ↦ measurable_pi_apply (1, k)))

theorem pairedUniformLaw_map_split : pairedUniformLaw.map splitUniforms = birthParentLaw := by
  have hc : pairedUniformLaw.map (MeasurableEquiv.curry (Fin 2) ℕ ℝ) =
      Measure.infinitePi (fun _ : Fin 2 ↦ uniformLaw) :=
    Measure.infinitePi_map_curry (fun (_ : Fin 2) (_ : ℕ) ↦ unitUniform)
  calc
    _ = (pairedUniformLaw.map (MeasurableEquiv.curry (Fin 2) ℕ ℝ)).map
        MeasurableEquiv.finTwoArrow := by
      rw [Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
      rfl
    _ = (Measure.pi (fun _ : Fin 2 ↦ uniformLaw)).map MeasurableEquiv.finTwoArrow := by
      rw [hc, Measure.infinitePi_eq_pi]
    _ = _ := (measurePreserving_finTwoArrow uniformLaw).map_eq

theorem pairedUniformLaw_independent :
    iIndepFun (fun i (w : (Fin 2 × ℕ) → ℝ) ↦ w i) pairedUniformLaw :=
  iIndepFun_infinitePi (X := fun _ x ↦ x) (fun _ ↦ measurable_id)

noncomputable def coupledTreeState (l : ℝ) (n : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ)) (k : ℕ) : State :=
  rankState (finiteBirth l n q.1) (initial n) q.2 k

noncomputable def coupledTreeHistory (l : ℝ) (n k : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ)) : FinitePath k :=
  rankHistory (finiteBirth l n q.1) (initial n) k q.2

theorem measurable_coupledTreeHistory (l : ℝ) (n k : ℕ) : Measurable (coupledTreeHistory l n k) :=
  (measurable_trajectoryPrefix k).comp (measurable_finite_rankTrajectory l n (initial n))

theorem counts_rankUpdate (birth : Bool) (s : State) (hs : s.active.Nonempty) (v : ℝ) :
    counts (rankUpdate birth s v) =
      if birth then (s.susceptible - 1, infectious s + 1) else (s.susceptible, infectious s - 1) := by
  rw [rankUpdate_of_nonempty birth s hs v]
  unfold counts
  rw [susceptible_prescribedUpdate, infectious_prescribedUpdate birth (activeAtRank_mem s _)]
  cases birth <;> rfl

/-- Exact count correspondence, also after extinction. The unabsorbed birth
word can continue, but the actual tree state and these counts are absorbed. -/
theorem counts_coupledTreeState (l : ℝ) (n : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ)) (k : ℕ) :
    counts (coupledTreeState l n q k) = absorbedCounts l n q.1 k := by
  induction k with
  | zero => simp [coupledTreeState, rankState, counts, absorbedCounts, initial, infectious]
  | succ k ih =>
      let s := coupledTreeState l n q k
      have hc : counts s = absorbedCounts l n q.1 k := ih
      by_cases hs : s.active.Nonempty
      · have hi : 0 < (absorbedCounts l n q.1 k).2 := by
          rw [← hc]
          exact hs.card_pos
        have hp : ∀ j < k, 0 < finiteWalk l n q.1 j := by
          intro j hj
          have hh := absorbedCounts_pos_past l n q.1 hj.le hi
          rw [← absorbedCounts_cast_eq_of_pos l n q.1 j hh]
          exact_mod_cast hh
        have hS : s.susceptible = finiteSusceptible l n q.1 k :=
          (congrArg Prod.fst hc).trans (absorbedCounts_eq_before_hit l n q.1 k hp).1
        change counts (rankUpdate (finiteBirth l n q.1 k) s (q.2 k)) = _
        rw [counts_rankUpdate _ _ hs, absorbedCounts, ← hc]
        simp only [uniformCountUpdate, counts, show infectious s ≠ 0 from ne_of_gt hs.card_pos,
          hS]
        rfl
      · have hi : infectious s = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hs)
        change counts (rankUpdate (finiteBirth l n q.1 k) s (q.2 k)) = _
        rw [absorbedCounts, ← hc]
        simp only [rankUpdate, dite_eq_right hs, uniformCountUpdate, counts, hi, ite_eq_left]

theorem coupledTreeState_succ (l : ℝ) (n : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ)) (k : ℕ) :
    coupledTreeState l n q (k + 1) = rankUpdate
      (budgetBirth l n (coupledTreeState l n q k).susceptible (q.1 k))
      (coupledTreeState l n q k) (q.2 k) := by
  let s := coupledTreeState l n q k
  by_cases hs : s.active.Nonempty
  · have hc := counts_coupledTreeState l n q k
    have hi : 0 < (absorbedCounts l n q.1 k).2 := by rw [← hc]; exact hs.card_pos
    have hp : ∀ j < k, 0 < finiteWalk l n q.1 j := by
      intro j hj
      have hh := absorbedCounts_pos_past l n q.1 hj.le hi
      rw [← absorbedCounts_cast_eq_of_pos l n q.1 j hh]
      exact_mod_cast hh
    have hS : s.susceptible = finiteSusceptible l n q.1 k :=
      (congrArg Prod.fst hc).trans (absorbedCounts_eq_before_hit l n q.1 k hp).1
    change rankUpdate (finiteBirth l n q.1 k) s (q.2 k) =
      rankUpdate (budgetBirth l n s.susceptible (q.1 k)) s (q.2 k)
    rw [hS]
    rfl
  · change rankUpdate _ s _ = rankUpdate _ s _
    simp only [rankUpdate, dite_eq_right hs]

theorem coupledTreeState_congr_prefix (l : ℝ) (n : ℕ) {q r : (ℕ → ℝ) × (ℕ → ℝ)}
    (k : ℕ) (hq : ∀ i < k, q.1 i = r.1 i ∧ q.2 i = r.2 i) :
    coupledTreeState l n q k = coupledTreeState l n r k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [coupledTreeState_succ, coupledTreeState_succ, ih (fun i hi ↦ hq i (by omega)),
        (hq k (by omega)).1, (hq k (by omega)).2]

noncomputable def uniformTreeUpdate (l : ℝ) (n : ℕ) (s : State) (v : ℝ × ℝ) : State :=
  rankUpdate (budgetBirth l n s.susceptible v.1) s v.2

theorem measurable_budgetBirth_scalar (l : ℝ) (n H : ℕ) : Measurable (budgetBirth l n H) := by
  exact (measurable_budgetBirth l n 0 (fun _ ↦ H) measurable_const).comp
    (measurable_pi_iff.mpr (fun _ ↦ measurable_id))

theorem measurable_uniformTreeUpdate (l : ℝ) (n : ℕ) (s : State) :
    Measurable (uniformTreeUpdate l n s) := by
  have hm : Measurable (fun p : Bool × ℝ ↦ rankUpdate p.1 s p.2) :=
    measurable_from_prod_countable_right (fun b ↦ measurable_rankUpdate b s)
  exact hm.comp (((measurable_budgetBirth_scalar l n s.susceptible).comp measurable_fst).prodMk
    measurable_snd)

/-- Both independent choices give exactly the original epidemic kernel. -/
theorem uniformTreeUpdate_law (l : ℝ≥0) (n k : ℕ) (s : State) :
    birthParentLaw.map (fun q ↦ uniformTreeUpdate l n s (q.1 k, q.2 k)) =
      (step (l / n) s).toMeasure := by
  let X : ((ℕ → ℝ) × (ℕ → ℝ)) → Bool := fun q ↦ budgetBirth l n s.susceptible (q.1 k)
  let Z : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun q ↦ q.2 k
  have hm : Measurable (fun u : ℕ → ℝ ↦ budgetBirth l n s.susceptible (u k)) :=
    measurable_budgetBirth l n k (fun _ ↦ s.susceptible) measurable_const
  have hX : Measurable X := hm.comp measurable_fst
  have hZ : Measurable Z := (measurable_pi_apply k).comp measurable_snd
  have hlaw : birthParentLaw.map X = (eventChoice (l / n) s.susceptible).toMeasure := by
    change birthParentLaw.map ((fun u ↦ budgetBirth l n s.susceptible (u k)) ∘ Prod.fst) = _
    rw [← Measure.map_map hm measurable_fst, birthParentLaw_map_fst, uniformLaw_map_budgetBirth]
  have hQ (b : Bool) : birthParentLaw.map (fun q ↦ rankUpdate b s (Z q)) =
      (prescribedStep b s).toMeasure := by
    have hm' : Measurable (fun u : ℕ → ℝ ↦ rankUpdate b s (u k)) :=
      (measurable_rankUpdate b s).comp (measurable_pi_apply k)
    change birthParentLaw.map ((fun u ↦ rankUpdate b s (u k)) ∘ Prod.snd) = _
    rw [← Measure.map_map hm' measurable_snd, birthParentLaw_map_snd, rankUpdate_law]
  rw [step_eq_eventChoice_bind_prescribed]
  exact independent_pmf_update birthParentLaw X Z (fun b v ↦ rankUpdate b s v)
    (eventChoice (l / n) s.susceptible) (fun b ↦ prescribedStep b s) hX hZ
    (fun b ↦ measurable_rankUpdate b s)
    ((measurable_uniformTreeUpdate l n s).comp
      (((measurable_pi_apply k).comp measurable_fst).prodMk hZ))
    (indepFun_prod hm (measurable_pi_apply k)) hlaw hQ

theorem pairedUniformTreeUpdate_law (l : ℝ≥0) (n k : ℕ) (s : State) :
    pairedUniformLaw.map (fun w ↦ uniformTreeUpdate l n s (w (0, k), w (1, k))) =
      (step (l / n) s).toMeasure := by
  have hm : Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦ uniformTreeUpdate l n s (q.1 k, q.2 k)) :=
    (measurable_uniformTreeUpdate l n s).comp
      (((measurable_pi_apply k).comp measurable_fst).prodMk ((measurable_pi_apply k).comp measurable_snd))
  change pairedUniformLaw.map ((fun q ↦ uniformTreeUpdate l n s (q.1 k, q.2 k)) ∘ splitUniforms) = _
  rw [← Measure.map_map hm measurable_splitUniforms, pairedUniformLaw_map_split, uniformTreeUpdate_law]

def extendPairPast (k : ℕ) (v : {i : Fin 2 × ℕ // i.2 < k} → ℝ) : (Fin 2 × ℕ) → ℝ :=
  fun i ↦ if hi : i.2 < k then v ⟨i, hi⟩ else 0

theorem measurable_extendPairPast (k : ℕ) : Measurable (extendPairPast k) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i.2 < k <;> simp [extendPairPast, hi]
  exact measurable_pi_apply (⟨i, hi⟩ : {i : Fin 2 × ℕ // i.2 < k})

/-- The entire two-uniform tree history is independent of the next pair. -/
theorem coupledTreeHistory_indep_next (l : ℝ) (n k : ℕ) :
    IndepFun (coupledTreeHistory l n k ∘ splitUniforms)
      (fun w : (Fin 2 × ℕ) → ℝ ↦ (w (0, k), w (1, k))) pairedUniformLaw := by
  have hind := pairedUniformLaw_independent.indepFun_set
    {i : Fin 2 × ℕ | i.2 < k} {i | i.2 = k}
    (by
      apply Set.disjoint_left.mpr
      intro i hi he
      simp only [mem_ofPred_eq] at hi he
      omega) (fun i ↦ measurable_pi_apply i)
  have hh := hind.comp
    (((measurable_coupledTreeHistory l n k).comp measurable_splitUniforms).comp (measurable_extendPairPast k))
    ((measurable_pi_apply (⟨(0, k), rfl⟩ : {i : Fin 2 × ℕ // i.2 = k})).prodMk
      (measurable_pi_apply (⟨(1, k), rfl⟩ : {i : Fin 2 × ℕ // i.2 = k})))
  have heq : ((coupledTreeHistory l n k ∘ splitUniforms) ∘ extendPairPast k) ∘
      (fun (w : (Fin 2 × ℕ) → ℝ) (i : {i : Fin 2 × ℕ // i.2 < k}) ↦ w i) =
        coupledTreeHistory l n k ∘ splitUniforms := by
    funext w
    apply FinitePath.ext
    intro i
    apply coupledTreeState_congr_prefix
    intro j hj
    have hjk : j < k := by have := i.isLt; omega
    simp [splitUniforms, extendPairPast, hjk]
  convert hh using 1
  · exact heq.symm
  · rfl

theorem coupledTreeHistory_succ (l : ℝ) (n k : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ)) :
    coupledTreeHistory l n (k + 1) q = (coupledTreeHistory l n k q).append
      (uniformTreeUpdate l n (coupledTreeHistory l n k q).last (q.1 k, q.2 k)) := by
  calc
    _ = (coupledTreeHistory l n k q).append (coupledTreeState l n q (k + 1)) :=
      trajectoryPrefix_succ k (rankState (finiteBirth l n q.1) (initial n) q.2)
    _ = _ := by rw [coupledTreeState_succ]; rfl

theorem paired_coupledTreeHistory_law (l : ℝ≥0) (n k : ℕ) :
    pairedUniformLaw.map (coupledTreeHistory l n k ∘ splitUniforms) =
      kernelPathMeasure (fun _ ↦ step (l / n)) (initial n) k := by
  induction k with
  | zero =>
      have he : coupledTreeHistory l n 0 ∘ splitUniforms =
          fun _ ↦ (⟨fun _ ↦ initial n⟩ : FinitePath 0) := by
        funext w
        apply FinitePath.ext
        intro i
        simp [coupledTreeHistory, rankHistory, trajectoryPrefix, rankState]
      rw [he, kernelPathMeasure, kernelPathLaw, PMF.toMeasure_pure]
      simp
  | succ k ih =>
      have he : coupledTreeHistory l n (k + 1) ∘ splitUniforms = fun w ↦
          (coupledTreeHistory l n k (splitUniforms w)).append
            (uniformTreeUpdate l n (coupledTreeHistory l n k (splitUniforms w)).last
              (w (0, k), w (1, k))) := by
        funext w
        exact coupledTreeHistory_succ l n k (splitUniforms w)
      rw [he, kernelPathMeasure, kernelPathLaw]
      refine independent_pmf_update pairedUniformLaw (coupledTreeHistory l n k ∘ splitUniforms)
        (fun w ↦ (w (0, k), w (1, k)))
        (fun (p : FinitePath k) v ↦ p.append (uniformTreeUpdate l n p.last v))
        (kernelPathLaw (fun _ ↦ step (l / n)) (initial n) k)
        (fun p ↦ (step (l / n) p.last).map p.append)
        ((measurable_coupledTreeHistory l n k).comp measurable_splitUniforms)
        ((measurable_pi_apply (0, k)).prodMk (measurable_pi_apply (1, k))) ?_ ?_
        (coupledTreeHistory_indep_next l n k) ih ?_
      · intro p
        exact (measurable_of_countable p.append).comp (measurable_uniformTreeUpdate l n p.last)
      · simp only [Function.comp_def]
        rw [← he]
        exact (measurable_coupledTreeHistory l n (k + 1)).comp measurable_splitUniforms
      · intro p
        have hm : Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦
            uniformTreeUpdate l n p.last (w (0, k), w (1, k))) :=
          (measurable_uniformTreeUpdate l n p.last).comp
            ((measurable_pi_apply (0, k)).prodMk (measurable_pi_apply (1, k)))
        change pairedUniformLaw.map (p.append ∘
          (fun w ↦ uniformTreeUpdate l n p.last (w (0, k), w (1, k)))) = _
        rw [← Measure.map_map (measurable_of_countable p.append) hm, pairedUniformTreeUpdate_law,
          PMF.toMeasure_map _ _ (measurable_of_countable p.append)]

/-- The complete finite infection-tree history under the source's two
independent uniform sequences is exactly the original epidemic law at `λ/n`,
including every absorbing self-loop after extinction. -/
theorem coupledTreeHistory_law (l : ℝ≥0) (n k : ℕ) :
    birthParentLaw.map (coupledTreeHistory l n k) = pathMeasure (l / n) n k := by
  calc
    _ = pairedUniformLaw.map (coupledTreeHistory l n k ∘ splitUniforms) := by
      rw [← Measure.map_map (measurable_coupledTreeHistory l n k) measurable_splitUniforms,
        pairedUniformLaw_map_split]
    _ = kernelPathMeasure (fun _ ↦ step (l / n)) (initial n) k := paired_coupledTreeHistory_law l n k
    _ = _ := by
      unfold kernelPathMeasure pathMeasure
      rw [pathLaw_eq_kernelPathLaw]

/-- Any finite-history observable transfers with its full joint distribution. -/
theorem coupledTreeHistory_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (l : ℝ≥0) (n k : ℕ) (f : FinitePath k → E) :
    (∫ q, f (coupledTreeHistory l n k q) ∂birthParentLaw) =
      ∫ p, f p ∂pathMeasure (l / n) n k := by
  rw [← coupledTreeHistory_law l n k]
  exact (integral_map (measurable_coupledTreeHistory l n k).aemeasurable
    (FinitePath.measurable f).aestronglyMeasurable).symm

end HeightPaper.CountCoupling
