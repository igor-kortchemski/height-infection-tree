module

public import HeightPaper.Probability.ProfileCouplingComparison
public import HeightPaper.Probability.LocalProfileStability
public import HeightPaper.Probability.FiniteTreeCouplingLaw
public import HeightPaper.Probability.SurvivalCoupling
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Finite prefixes of the early epidemic and the local limiting tree

For arbitrary asymptotic rate sequences, the first fixed number of epidemic
event choices agrees with the local infinite-population choices with
probability tending to one on their common uniform sampling space. This is
the finite-prefix input for the unscaled early-extinction law in `lem:limflu`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal symmDiff

namespace HeightPaper.CountCoupling

/-- Survival of the finite common-uniform walk has exactly the marginal
nonextinction probability of the epidemic event chain. -/
theorem finiteSurvival_probability_eq (a : ℝ≥0) (n H : ℕ) :
    uniformLaw.real (finiteSurvival a n H) =
      (Model.evolve (a / n) n H).toMeasure.real
        {s | 0 < Model.infectious s} := by
  let A : Set (Fin (H + 1) → ℕ × ℕ) :=
    {c | 0 < (c (Fin.last H)).2}
  have hA : MeasurableSet A := (Set.to_countable _).measurableSet
  have hmap := congrArg (fun μ : Measure (Fin (H + 1) → ℕ × ℕ) ↦ μ A)
    (uniformCountHistory_eq_epidemic a n H)
  rw [Measure.map_apply (measurable_uniformCountHistory a n H) hA,
    Measure.map_apply (Model.FinitePath.measurable _) hA] at hmap
  have hleft : finiteSurvival a n H =
      {u | 0 < (absorbedCounts a n u H).2} := by
    ext u
    constructor
    · intro hu
      exact ((finiteWalk_survival_iff a n u H).mp hu) H le_rfl
    · intro hu
      exact (finiteWalk_survival_iff a n u H).mpr
        (fun j hj ↦ absorbedCounts_pos_past a n u hj hu)
  have hreal := congrArg ENNReal.toReal hmap
  change uniformLaw.real {u | 0 < (absorbedCounts a n u H).2} =
    (Model.pathMeasure (a / n) n H).real
      {p | 0 < Model.infectious p.last} at hreal
  have hpath : uniformLaw.real (finiteSurvival a n H) =
      (Model.pathMeasure (a / n) n H).real
        {p | 0 < Model.infectious p.last} := by
    rw [hleft]
    exact hreal
  rw [hpath]
  simpa only [Model.FinitePath.eval_last, mem_ofPred_eq] using
    Model.pathMeasure_event_at (a / n) n H H le_rfl
      {s | 0 < Model.infectious s}

/-- At a fixed macroscopic preterminal time, survival of the finite walk has
the explicit supercritical limit. -/
theorem finiteSurvival_floor_probability_tendsto
    {l : ℝ} (hl : 1 < l) {T : ℝ}
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l)) :
    Tendsto (fun n ↦ uniformLaw.real
      (finiteSurvival l n ⌊T * n⌋₊)) atTop (𝓝 (1 - 1 / l)) := by
  let a : ℝ≥0 := ⟨l, (zero_lt_one.trans hl).le⟩
  have ha : (a : ℝ) = l := rfl
  let rates : ℕ → ℝ≥0 := fun n ↦ a / n
  have hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l) := by
    apply (tendsto_const_nhds (x := l)).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [rates, NNReal.coe_div, NNReal.coe_natCast, div_mul_cancel₀ _ hnR, ha]
  have hlim := Model.evolve_extinction_tendsto_reciprocal rates
    (fun n ↦ ⌊T * n⌋₊) hl hT hrates (tendsto_floor_fraction hT.1.le)
  have hcomp : Tendsto (fun n ↦ 1 -
      (Model.evolve (rates n) n ⌊T * n⌋₊).toMeasure.real
        {s | Model.infectious s = 0}) atTop (𝓝 (1 - 1 / l)) := by
    exact (tendsto_const_nhds.sub hlim)
  apply hcomp.congr'
  apply Eventually.of_forall
  intro n
  change 1 - (Model.evolve (a / n) n ⌊T * n⌋₊).toMeasure.real
    {s | Model.infectious s = 0} =
      uniformLaw.real (finiteSurvival a n ⌊T * n⌋₊)
  rw [finiteSurvival_probability_eq]
  have hset : {s : Model.State | 0 < Model.infectious s} =
      {s | Model.infectious s = 0}ᶜ := by
    ext s
    simp only [mem_ofPred_eq, mem_compl_iff]
    omega
  rw [hset, measureReal_compl (show MeasurableSet
    {s : Model.State | Model.infectious s = 0} from trivial)]
  simp

theorem measurableSet_localSurvival (l : ℝ) : MeasurableSet (localSurvival l) := by
  have hset : localSurvival l = ⋂ k : ℕ, {u | 0 < localWalk l u k} := by
    ext u
    simp [localSurvival]
  rw [hset]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_lt measurable_const (measurable_localWalk l k)

/-- Finite preterminal survival and infinite local survival disagree with
vanishing probability for each fixed supercritical intensity. -/
theorem finite_local_survival_disagreement_tendsto_zero
    {l : ℝ} (hl : 1 < l) {T : ℝ}
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l)) :
    Tendsto (fun n ↦ uniformLaw.real
      (finiteSurvival l n ⌊T * n⌋₊ ∆ localSurvival l)) atTop (𝓝 0) := by
  let a : ℝ≥0 := ⟨l, (zero_lt_one.trans hl).le⟩
  have ha : (a : ℝ) = l := rfl
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall (fun n ↦ hb.trans_le measureReal_nonneg)
  · intro b hb
    obtain ⟨N, hN⟩ := uniform_survival_disagreement
      (I := {a}) isCompact_singleton hT.1
      (by intro x hx; have hx' : x = a := by simpa using hx
          subst x; exact ⟨by simpa [ha] using hl, by simpa [ha] using hT.2⟩) hb
    filter_upwards [eventually_ge_atTop N] with n hn
    have hh := hN n hn a (by simp)
    have heq : {u : ℕ → ℝ |
        ¬ ((∀ j ≤ ⌊T * n⌋₊, 0 < finiteWalk a n u j) ↔
          ∀ k, 0 < localWalk a u k)} =
        finiteSurvival l n ⌊T * n⌋₊ ∆ localSurvival l := by
      ext u
      simp only [mem_ofPred_eq, mem_symmDiff, finiteSurvival, localSurvival, ha]
      tauto
    rw [heq] at hh
    exact hh

/-- The infinite local walk survives with the paper's Bernoulli weight. -/
theorem localSurvival_probability_eq {l : ℝ} (hl : 1 < l) :
    uniformLaw.real (localSurvival l) = 1 - 1 / l := by
  let T : ℝ := fluidExtinctionTime l / 2
  have hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    dsimp [T]
    have hp := fluidExtinctionTime_pos hl
    constructor <;> linarith
  have hfin := finiteSurvival_floor_probability_tendsto hl hT
  have hdis := finite_local_survival_disagreement_tendsto_zero hl hT
  have hdiff : Tendsto (fun n ↦
      |uniformLaw.real (finiteSurvival l n ⌊T * n⌋₊) -
        uniformLaw.real (localSurvival l)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hdis
    apply Eventually.of_forall
    intro n
    have hfinSet : MeasurableSet (finiteSurvival l n ⌊T * n⌋₊) := by
      have hset : finiteSurvival l n ⌊T * n⌋₊ =
          ⋂ j ∈ Finset.Iic ⌊T * n⌋₊, {u | 0 < finiteWalk l n u j} := by
        ext u
        simp [finiteSurvival]
      rw [hset]
      apply (Finset.Iic ⌊T * n⌋₊).measurableSet_biInter
      intro j _
      exact measurableSet_lt measurable_const (measurable_finiteWalk l n j)
    exact abs_measureReal_sub_le_measureReal_symmDiff hfinSet.nullMeasurableSet
      (measurableSet_localSurvival l).nullMeasurableSet
  have hdiff0 : Tendsto (fun n ↦
      uniformLaw.real (finiteSurvival l n ⌊T * n⌋₊) -
        uniformLaw.real (localSurvival l)) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr hdiff
  have hconst : 1 - 1 / l - uniformLaw.real (localSurvival l) = 0 :=
    tendsto_nhds_unique (hfin.sub_const _) hdiff0
  linarith

/-- The finite common-uniform survival event increases with infection
intensity. -/
theorem finiteSurvival_mono_parameter {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (n H : ℕ) : finiteSurvival a n H ⊆ finiteSurvival b n H := by
  intro u hu j hj
  exact (hu j hj).trans_le (finiteWalk_mono_parameter ha hab n u j)

/-- Comparable measurable events differ in probability by the absolute
difference of their masses. -/
theorem measureReal_symmDiff_eq_abs_sub_of_comparable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hcomp : A ⊆ B ∨ B ⊆ A) :
    μ.real (A ∆ B) = |μ.real A - μ.real B| := by
  rcases hcomp with hAB | hBA
  · have hset : A ∆ B = B \ A := by
      ext x
      have hx : x ∈ A → x ∈ B := fun h ↦ hAB h
      simp only [Set.mem_symmDiff, Set.mem_sdiff]
      tauto
    rw [hset, measureReal_sdiff hAB hA]
    have hle : μ.real A ≤ μ.real B := measureReal_mono hAB (measure_ne_top _ _)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
  · have hset : A ∆ B = A \ B := by
      ext x
      have hx : x ∈ B → x ∈ A := fun h ↦ hBA h
      simp only [Set.mem_symmDiff, Set.mem_sdiff]
      tauto
    rw [hset, measureReal_sdiff hBA hB]
    have hle : μ.real B ≤ μ.real A := measureReal_mono hBA (measure_ne_top _ _)
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]

/-- For finite survival events, disagreement probability is exactly the
difference of the two marginal probabilities. -/
theorem finiteSurvival_symmDiff_probability_eq_abs_sub
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n H : ℕ) :
    uniformLaw.real (finiteSurvival a n H ∆ finiteSurvival b n H) =
      |uniformLaw.real (finiteSurvival a n H) -
        uniformLaw.real (finiteSurvival b n H)| := by
  have hmeas (c : ℝ) : MeasurableSet (finiteSurvival c n H) := by
    have hset : finiteSurvival c n H =
        ⋂ j ∈ Finset.Iic H, {u | 0 < finiteWalk c n u j} := by
      ext u
      simp [finiteSurvival]
    rw [hset]
    apply (Finset.Iic H).measurableSet_biInter
    intro j _
    exact measurableSet_lt measurable_const (measurable_finiteWalk c n j)
  apply measureReal_symmDiff_eq_abs_sub_of_comparable uniformLaw
    (hmeas a) (hmeas b)
  rcases le_total a b with hab | hba
  · exact Or.inl (finiteSurvival_mono_parameter ha hab n H)
  · exact Or.inr (finiteSurvival_mono_parameter hb hba n H)

/-- Marginal finite survival for an arbitrary asymptotic rate sequence and
preterminal horizon, in the common-uniform normalization of the tree coupling. -/
theorem finiteSurvival_rateSequence_horizon_probability_tendsto
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    Tendsto (fun n ↦ uniformLaw.real
      (finiteSurvival ((rates n : ℝ) * n) n (horizon n)))
      atTop (𝓝 (1 - 1 / l)) := by
  have hlim := Model.evolve_extinction_tendsto_reciprocal rates
    horizon hl hT hrates hhorizon
  have hcomp : Tendsto (fun n ↦ 1 -
      (Model.evolve (rates n) n (horizon n)).toMeasure.real
        {s | Model.infectious s = 0}) atTop (𝓝 (1 - 1 / l)) :=
    tendsto_const_nhds.sub hlim
  apply hcomp.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  let a : ℝ≥0 := rates n * n
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hrate : a / n = rates n := by
    dsimp [a]
    field_simp [hn0]
  change 1 - (Model.evolve (rates n) n (horizon n)).toMeasure.real
    {s | Model.infectious s = 0} =
      uniformLaw.real (finiteSurvival (a : ℝ) n (horizon n))
  rw [finiteSurvival_probability_eq a, hrate]
  have hset : {s : Model.State | 0 < Model.infectious s} =
      {s | Model.infectious s = 0}ᶜ := by
    ext s
    simp only [mem_ofPred_eq, mem_compl_iff]
    omega
  rw [hset, measureReal_compl (show MeasurableSet
    {s : Model.State | Model.infectious s = 0} from trivial)]
  simp

theorem finiteSurvival_rateSequence_floor_probability_tendsto
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ uniformLaw.real
      (finiteSurvival ((rates n : ℝ) * n) n ⌊T * n⌋₊))
      atTop (𝓝 (1 - 1 / l)) :=
  finiteSurvival_rateSequence_horizon_probability_tendsto rates
    (fun n ↦ ⌊T * n⌋₊) hl hT hrates (tendsto_floor_fraction hT.1.le)

/-- The varying finite intensity has the same survival event as the fixed
limit intensity with probability tending to one. -/
theorem finiteSurvival_rateSequence_fixed_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ uniformLaw.real
      (finiteSurvival ((rates n : ℝ) * n) n ⌊T * n⌋₊ ∆
        finiteSurvival l n ⌊T * n⌋₊)) atTop (𝓝 0) := by
  have hvar := finiteSurvival_rateSequence_floor_probability_tendsto rates hl hT hrates
  have hfix := finiteSurvival_floor_probability_tendsto hl hT
  have hdiff := (hvar.sub hfix).abs
  simp only [sub_self, abs_zero] at hdiff
  apply hdiff.congr'
  apply Eventually.of_forall
  intro n
  exact (finiteSurvival_symmDiff_probability_eq_abs_sub
    (mul_nonneg (rates n).coe_nonneg (Nat.cast_nonneg n))
    (zero_lt_one.trans hl).le n ⌊T * n⌋₊).symm

/-- For every asymptotic rate sequence, finite survival through a fixed
preterminal fraction agrees with local infinite survival. -/
theorem finiteSurvival_rateSequence_local_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ uniformLaw.real
      (finiteSurvival ((rates n : ℝ) * n) n ⌊T * n⌋₊ ∆
        localSurvival l)) atTop (𝓝 0) := by
  have hvar := finiteSurvival_rateSequence_fixed_disagreement_tendsto_zero
    rates hl hT hrates
  have hfix := finite_local_survival_disagreement_tendsto_zero hl hT
  have hsum := hvar.add hfix
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  exact measureReal_symmDiff_le (μ := uniformLaw)
    (s := finiteSurvival ((rates n : ℝ) * n) n ⌊T * n⌋₊)
    (t := finiteSurvival l n ⌊T * n⌋₊)
    (localSurvival l) (by finiteness) (by finiteness)

/-- On the infinite-survival event this predicate holds at time zero; on an
extinct path it first holds exactly when the local walk reaches zero. -/
def localEarlyHit (l : ℝ) (u : ℕ → ℝ) (k : ℕ) : Prop :=
  localWalk l u k ≤ 0 ∨ (k = 0 ∧ u ∈ localSurvival l)

theorem localEarlyHit_exists (l : ℝ) (u : ℕ → ℝ) :
    ∃ k, localEarlyHit l u k := by
  by_cases hsurv : u ∈ localSurvival l
  · exact ⟨0, Or.inr ⟨rfl, hsurv⟩⟩
  · have hhit : ∃ k, localWalk l u k ≤ 0 := by
      simpa only [localSurvival, mem_ofPred_eq, not_forall, not_lt] using hsurv
    obtain ⟨k, hk⟩ := hhit
    exact ⟨k, Or.inl hk⟩

/-- The local unscaled early-extinction time. It is zero on the surviving
branch and is the first visit to zero on the extinct branch. -/
noncomputable def localEarlyExtinctionTime (l : ℝ) (u : ℕ → ℝ) : ℕ :=
  @Nat.find (localEarlyHit l u) (Classical.decPred _) (localEarlyHit_exists l u)

theorem measurable_localEarlyExtinctionTime (l : ℝ) :
    Measurable (localEarlyExtinctionTime l) := by
  classical
  have hsurv := measurableSet_localSurvival l
  have hm (k : ℕ) : MeasurableSet {u | localEarlyHit l u k} := by
    have hset : {u | localEarlyHit l u k} =
        {u | localWalk l u k ≤ 0} ∪ {u | k = 0 ∧ u ∈ localSurvival l} := by
      ext u
      simp [localEarlyHit]
    rw [hset]
    refine (measurableSet_le (measurable_localWalk l k) measurable_const).union ?_
    by_cases hk : k = 0
    · simpa [hk] using hsurv
    · simp [hk]
  exact measurable_find (fun u ↦ localEarlyHit_exists l u) hm

theorem localEarlyExtinctionTime_eq_zero_iff (l : ℝ) (u : ℕ → ℝ) :
    localEarlyExtinctionTime l u = 0 ↔ u ∈ localSurvival l := by
  classical
  unfold localEarlyExtinctionTime
  rw [Nat.find_eq_zero]
  simp [localEarlyHit, localWalk]

theorem localEarlyExtinctionTime_spec {l : ℝ} {u : ℕ → ℝ}
    (hnot : u ∉ localSurvival l) :
    0 < localEarlyExtinctionTime l u ∧
      localWalk l u (localEarlyExtinctionTime l u) = 0 ∧
      ∀ j < localEarlyExtinctionTime l u, 0 < localWalk l u j := by
  classical
  let T := localEarlyExtinctionTime l u
  have hT : 0 < T := by
    have hne : T ≠ 0 := fun h ↦ hnot ((localEarlyExtinctionTime_eq_zero_iff l u).mp h)
    omega
  have hhit : localWalk l u T ≤ 0 := by
    have hh := Nat.find_spec (localEarlyHit_exists l u)
    change localEarlyHit l u T at hh
    rcases hh with hh | ⟨hz, hs⟩
    · exact hh
    · exact (hnot hs).elim
  have hbefore (j : ℕ) (hj : j < T) : 0 < localWalk l u j := by
    have hmiss := Nat.find_min (localEarlyHit_exists l u) hj
    have hn : ¬(localWalk l u j ≤ 0) := fun h ↦ hmiss (Or.inl h)
    omega
  have hprev := hbefore (T - 1) (by omega)
  have hTsucc : T - 1 + 1 = T := by omega
  have hstep := localWalk_succ l u (T - 1)
  rw [hTsucc] at hstep
  have hzero : localWalk l u T = 0 := by
    split_ifs at hstep <;> omega
  exact ⟨hT, hzero, hbefore⟩

/-- The height of the local tree at its unscaled extinction time; it is zero
on the infinite-survival branch. -/
noncomputable def localEarlyHeight (l : ℝ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) : ℕ :=
  Model.height (Model.rankState (localBirth l q.1) (Model.initial 0) q.2
    (localEarlyExtinctionTime l q.1))

theorem measurable_localEarlyHeight (l : ℝ) : Measurable (localEarlyHeight l) := by
  have hevents : Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦ localBirth l q.1) :=
    (Measurable.of_eval (measurable_localBirth l)).comp measurable_fst
  have hstate (k : ℕ) : Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      Model.height (Model.rankState (localBirth l q.1) (Model.initial 0) q.2 k)) :=
    (measurable_of_countable Model.height).comp
      ((Model.measurable_rankState_joint (Model.initial 0) k).comp
        (hevents.prodMk measurable_snd))
  have hm : Measurable (fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × ℕ ↦
      Model.height (Model.rankState (localBirth l p.1.1) (Model.initial 0) p.1.2 p.2)) :=
    measurable_from_prod_countable_left hstate
  exact hm.comp (measurable_id.prodMk
    ((measurable_localEarlyExtinctionTime l).comp measurable_fst))

theorem localEarlyHeight_zero_of_survival {l : ℝ}
    {q : (ℕ → ℝ) × (ℕ → ℝ)} (hs : q.1 ∈ localSurvival l) :
    localEarlyHeight l q = 0 := by
  have hT := (localEarlyExtinctionTime_eq_zero_iff l q.1).mpr hs
  simp [localEarlyHeight, hT, Model.rankState, Model.height_initial]

theorem localEarlyHeight_le_time (l : ℝ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) :
    localEarlyHeight l q ≤ localEarlyExtinctionTime l q.1 := by
  let T := localEarlyExtinctionTime l q.1
  let s := Model.rankState (localBirth l q.1) (Model.initial 0) q.2 T
  have hv := Model.vertices_rankState_le (localBirth l q.1) (Model.initial 0) q.2 T
  have hh := Model.Tree.height_lt_size s.tree
  change Model.height s < s.vertices at hh
  change s.vertices ≤ 1 + T at hv
  change Model.height s ≤ T
  omega

/-- The local tree is absorbed at the explicit early-extinction time on the
extinct branch. -/
theorem localEarlyTree_absorbed {l : ℝ} {q : (ℕ → ℝ) × (ℕ → ℝ)}
    (hs : q.1 ∉ localSurvival l) :
    (Model.rankState (localBirth l q.1) (Model.initial 0) q.2
      (localEarlyExtinctionTime l q.1)).active = ∅ := by
  let T := localEarlyExtinctionTime l q.1
  obtain ⟨_, hzero, hbefore⟩ := localEarlyExtinctionTime_spec hs
  change localWalk l q.1 T = 0 at hzero
  have hcast (j : ℕ) (hj : j ≤ T) :
      (Model.prescribedWalk (localBirth l q.1) 1 j : ℤ) = localWalk l q.1 j :=
    prescribedWalk_cast_eq_of_positive _ _ (by simp [localWalk])
      (localWalk_succ l q.1) (fun i hi ↦ hbefore i (hi.trans_le hj))
  have hpositive (j : ℕ) (hj : j < T) :
      0 < Model.prescribedWalk (localBirth l q.1) 1 j := by
    have hh := hcast j hj.le
    have hp := hbefore j hj
    omega
  have hcount := Model.infectious_rankState (localBirth l q.1)
    (Model.initial 0) q.2 T hpositive
  simp only [Model.infectious_initial] at hcount
  have hzeroCount : Model.infectious
      (Model.rankState (localBirth l q.1) (Model.initial 0) q.2 T) = 0 := by
    have hh := hcast T le_rfl
    omega
  exact Finset.card_eq_zero.mp hzeroCount

/-- Local outbreaks that first die only after an increasing finite prefix have
vanishing probability. -/
theorem local_late_extinction_tendsto_zero {l : ℝ} (hl : 1 < l) :
    Tendsto (fun K ↦ uniformLaw.real (lateLocalExtinction l K))
      atTop (𝓝 0) := by
  have htail := (lateLowerFailure_tendsto hl).comp (tendsto_add_atTop_nat 1)
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ htail
  apply Eventually.of_forall
  intro K
  exact lateLocalExtinction_probability_le hl le_rfl K

/-- The explicitly constructed unscaled early-extinction time has a vanishing
tail under the local law. -/
theorem localEarlyExtinctionTime_tail_tendsto_zero {l : ℝ} (hl : 1 < l) :
    Tendsto (fun K ↦ uniformLaw.real
      {u | K < localEarlyExtinctionTime l u}) atTop (𝓝 0) := by
  have hlate := local_late_extinction_tendsto_zero hl
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hlate
  apply Eventually.of_forall
  intro K
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro u hu
  change K < localEarlyExtinctionTime l u at hu
  have hnot : u ∉ localSurvival l := by
    intro hs
    have hzero := (localEarlyExtinctionTime_eq_zero_iff l u).mpr hs
    omega
  have hzero := (localEarlyExtinctionTime_spec hnot).2.1
  exact ⟨localEarlyExtinctionTime l u, hu, by rw [hzero]⟩

theorem localEarlyHeight_tail_tendsto_zero {l : ℝ} (hl : 1 < l) :
    Tendsto (fun K ↦ birthParentLaw.real
      {q | K < localEarlyHeight l q}) atTop (𝓝 0) := by
  have hT := localEarlyExtinctionTime_tail_tendsto_zero hl
  have hTpath : Tendsto (fun K ↦ birthParentLaw.real
      {q | K < localEarlyExtinctionTime l q.1}) atTop (𝓝 0) := by
    apply hT.congr'
    apply Eventually.of_forall
    intro K
    have hB : MeasurableSet {u | K < localEarlyExtinctionTime l u} :=
      measurableSet_lt measurable_const (measurable_localEarlyExtinctionTime l)
    rw [← birthParentLaw_map_fst]
    simp only [Measure.real, Measure.map_apply measurable_fst hB]
    rfl
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hTpath
  apply Eventually.of_forall
  intro K
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro q hq
  exact hq.trans_le (localEarlyHeight_le_time l q)

/-- The common-space tree construction has exactly the original epidemic path
law for an arbitrary population-dependent rate, once its intensity is written
in the paper's `l/n` normalization. -/
theorem rateSequence_coupledTreeHistory_law (rates : ℕ → ℝ≥0)
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    birthParentLaw.map (coupledTreeHistory (rates n * n) n k) =
      Model.pathMeasure (rates n) n k := by
  have h := coupledTreeHistory_law (rates n * n) n k
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hrate : rates n * (n : ℝ≥0) / n = rates n := by
    field_simp [hn0]
  simpa only [hrate, NNReal.coe_mul, NNReal.coe_natCast] using h

/-- Fixed event prefixes couple to the local birth word for every asymptotic
rate sequence, using the actual common uniform law. -/
theorem finiteBirth_localBirth_prefix_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l : ℝ} (hl : 0 ≤ l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (K : ℕ) :
    Tendsto (fun n ↦ uniformLaw.real
      {u | ∃ i < K,
        finiteBirth ((rates n : ℝ) * n) n u i ≠ localBirth l u i})
      atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun n ↦ (rates n : ℝ) * n
  have ha (n : ℕ) : 0 ≤ a n := by dsimp [a]; positivity
  have hfinite : Tendsto (fun n ↦ a n * (K : ℝ) ^ 2 / n) atTop (𝓝 0) := by
    have hh := (hrates.mul_const ((K : ℝ) ^ 2)).mul
      (tendsto_one_div_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
    simpa only [mul_zero, div_eq_mul_inv, one_mul] using hh
  have hlocal : Tendsto (fun n ↦ (K : ℝ) * |a n - l|) atTop (𝓝 0) := by
    have hh := (hrates.sub_const l).abs.const_mul (K : ℝ)
    simpa only [sub_self, abs_zero, mul_zero] using hh
  have hsum := hfinite.add hlocal
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  filter_upwards [eventually_ge_atTop K, eventually_gt_atTop 0] with n hKn hn
  let A : Set (ℕ → ℝ) :=
    {u | ∃ k ≤ K, finiteWalk (a n) n u k ≠ localWalk (a n) u k}
  let B : Set (ℕ → ℝ) :=
    {u | ∃ i < K, localBirth (a n) u i ≠ localBirth l u i}
  have hsub : {u | ∃ i < K, finiteBirth (a n) n u i ≠ localBirth l u i} ⊆
      A ∪ B := by
    intro u hu
    obtain ⟨i, hi, hne⟩ := hu
    by_cases hpre : u ∈ A
    · exact Or.inl hpre
    · apply Or.inr
      have hwalk : ∀ k ≤ K, finiteWalk (a n) n u k = localWalk (a n) u k := by
        intro k hk
        by_contra hne'
        exact hpre ⟨k, hk, hne'⟩
      have hb := finiteBirth_eq_localBirth_of_walk_prefix hwalk i hi
      exact ⟨i, hi, fun heq ↦ hne (hb.trans heq)⟩
  calc
    uniformLaw.real {u | ∃ i < K,
      finiteBirth ((rates n : ℝ) * n) n u i ≠ localBirth l u i} ≤
        uniformLaw.real (A ∪ B) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ uniformLaw.real A + uniformLaw.real B := measureReal_union_le A B
    _ ≤ a n * (K : ℝ) ^ 2 / n + (K : ℝ) * |a n - l| := by
      apply add_le_add
      · exact prefix_disagreement_probability_le (ha n) hn hKn
      · exact localBirth_prefix_disagreement_probability_le (ha n) hl K

end HeightPaper.CountCoupling

namespace HeightPaper.Model

/-- A prescribed rank trajectory is exactly constant after its active set is
empty, independently of all later event and parent draws. -/
theorem rankState_absorbed_stable (events : ℕ → Bool) (s₀ : State)
    (u : ℕ → ℝ) {i j : ℕ} (hij : i ≤ j)
    (hi : (rankState events s₀ u i).active = ∅) :
    rankState events s₀ u j = rankState events s₀ u i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
      have hnone : ¬(rankState events s₀ u j).active.Nonempty := by
        rw [ih]
        exact Finset.not_nonempty_iff_eq_empty.mpr hi
      rw [rankState, rankUpdate, dite_eq_right hnone, ih]

/-- Matching event prefixes give the same finite tree shape, active set and
height as the local limiting construction. The susceptible coordinate is
removed because it is the sole population-size dependent coordinate. -/
theorem finite_local_rankState_clear_eq {a l : ℝ} {n K : ℕ}
    {u v : ℕ → ℝ}
    (he : ∀ i < K, CountCoupling.finiteBirth a n u i =
      CountCoupling.localBirth l u i) :
    clearSusceptible (rankState (CountCoupling.finiteBirth a n u)
      (initial n) v K) =
      rankState (CountCoupling.localBirth l u) (initial 0) v K := by
  rw [clearSusceptible_rankState]
  change rankState (CountCoupling.finiteBirth a n u) (initial 0) v K = _
  exact rankState_congr_events_prefix (initial 0) v K he

theorem finite_local_rankState_height_eq {a l : ℝ} {n K : ℕ}
    {u v : ℕ → ℝ}
    (he : ∀ i < K, CountCoupling.finiteBirth a n u i =
      CountCoupling.localBirth l u i) :
    height (rankState (CountCoupling.finiteBirth a n u) (initial n) v K) =
      height (rankState (CountCoupling.localBirth l u) (initial 0) v K) := by
  have hh := congrArg height (finite_local_rankState_clear_eq
    (a := a) (l := l) (n := n) (K := K) (u := u) (v := v) he)
  simpa [height, clearSusceptible] using hh

end HeightPaper.Model

namespace HeightPaper.CountCoupling

/-- At every fixed event time, the actual finite epidemic tree height equals
the local limiting tree height with probability tending to one under the
common birth and parent uniforms. -/
theorem finite_local_height_fixed_time_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l : ℝ} (hl : 0 ≤ l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (K : ℕ) :
    Tendsto (fun n ↦ birthParentLaw.real
      {q | Model.height (Model.rankState
          (finiteBirth ((rates n : ℝ) * n) n q.1) (Model.initial n) q.2 K) ≠
        Model.height (Model.rankState (localBirth l q.1)
          (Model.initial 0) q.2 K)}) atTop (𝓝 0) := by
  have hprefix := finiteBirth_localBirth_prefix_disagreement_tendsto_zero
    rates hl hrates K
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hprefix
  apply Eventually.of_forall
  intro n
  let B : Set (ℕ → ℝ) :=
    {u | ∃ i < K, finiteBirth ((rates n : ℝ) * n) n u i ≠ localBirth l u i}
  have hB : MeasurableSet B := by
    have hset : B = ⋃ i ∈ Finset.range K,
        {u | finiteBirth ((rates n : ℝ) * n) n u i ≠ localBirth l u i} := by
      ext u
      simp [B]
    rw [hset]
    apply (Finset.range K).measurableSet_biUnion
    intro i _
    have hm := (measurable_finiteBirth ((rates n : ℝ) * n) n i).prodMk
      (measurable_localBirth l i)
    exact hm ((Set.to_countable {p : Bool × Bool | p.1 ≠ p.2}).measurableSet)
  have hmap : birthParentLaw.real (Prod.fst ⁻¹' B) = uniformLaw.real B := by
    rw [← birthParentLaw_map_fst]
    simp only [Measure.real, Measure.map_apply measurable_fst hB]
  rw [← hmap]
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro q hbad
  by_contra hnot
  have he : ∀ i < K,
      finiteBirth ((rates n : ℝ) * n) n q.1 i = localBirth l q.1 i := by
    intro i hi
    by_contra hne
    exact hnot ⟨i, hi, hne⟩
  exact hbad (Model.finite_local_rankState_height_eq
    (a := (rates n : ℝ) * n) (l := l) (n := n) (K := K)
    (u := q.1) (v := q.2) he)

/-- The entire fixed early tree prefix couples simultaneously, after removing
the unused susceptible coordinate from the finite-population state. -/
theorem finite_local_tree_prefix_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l : ℝ} (hl : 0 ≤ l)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (K : ℕ) :
    Tendsto (fun n ↦ birthParentLaw.real
      {q | ∃ k ≤ K,
        Model.clearSusceptible (Model.rankState
          (finiteBirth ((rates n : ℝ) * n) n q.1) (Model.initial n) q.2 k) ≠
          Model.rankState (localBirth l q.1) (Model.initial 0) q.2 k})
      atTop (𝓝 0) := by
  have hprefix := finiteBirth_localBirth_prefix_disagreement_tendsto_zero
    rates hl hrates K
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hprefix
  apply Eventually.of_forall
  intro n
  let B : Set (ℕ → ℝ) :=
    {u | ∃ i < K, finiteBirth ((rates n : ℝ) * n) n u i ≠ localBirth l u i}
  have hB : MeasurableSet B := by
    have hset : B = ⋃ i ∈ Finset.range K,
        {u | finiteBirth ((rates n : ℝ) * n) n u i ≠ localBirth l u i} := by
      ext u
      simp [B]
    rw [hset]
    apply (Finset.range K).measurableSet_biUnion
    intro i _
    have hm := (measurable_finiteBirth ((rates n : ℝ) * n) n i).prodMk
      (measurable_localBirth l i)
    exact hm ((Set.to_countable {p : Bool × Bool | p.1 ≠ p.2}).measurableSet)
  have hmap : birthParentLaw.real (Prod.fst ⁻¹' B) = uniformLaw.real B := by
    rw [← birthParentLaw_map_fst]
    simp only [Measure.real, Measure.map_apply measurable_fst hB]
  rw [← hmap]
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro q hbad
  obtain ⟨k, hk, hne⟩ := hbad
  by_contra hnot
  have he : ∀ i < k,
      finiteBirth ((rates n : ℝ) * n) n q.1 i = localBirth l q.1 i := by
    intro i hi
    by_contra hne'
    exact hnot ⟨i, by omega, hne'⟩
  exact hne (Model.finite_local_rankState_clear_eq
    (a := (rates n : ℝ) * n) (l := l) (n := n) (K := k)
    (u := q.1) (v := q.2) he)

end HeightPaper.CountCoupling
