module

public import HeightPaper.Probability.EarlyLocalHeightPotential
public import HeightPaper.Probability.FiniteTreeCouplingLaw
public import HeightPaper.Model.HeightPotentialKernel

/-!
# The constant-rate local tree kernel

The early limiting tree uses the same uniform active-parent rule as the
finite epidemic, but its birth probability does not depend on the remaining
susceptibles. The kernel below records that local transition law and the
exact expectation identity for the height potential.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace HeightPaper.Model

/-- One birth/recovery event at fixed intensity `l`, with a uniform active
parent. An empty active set is absorbing through `prescribedStep`. -/
def localTreeStep (l : ℝ≥0) (s : State) : PMF State :=
  (eventChoice l 1).bind fun b ↦ prescribedStep b s

theorem finite_support_localTreeStep (l : ℝ≥0) (s : State) :
    (localTreeStep l s).support.Finite := by
  unfold localTreeStep
  exact FinitePMF.finite_support_bind _ _ (Set.toFinite _) fun b _ ↦
    finite_support_prescribedStep b s

theorem prescribedStep_integral_real (birth : Bool) (s : State)
    (f : State → ℝ) :
    (∫ t, f t ∂(prescribedStep birth s).toMeasure) =
      if _ha : s.active.Nonempty then
        (∑ v ∈ s.active, f (prescribedUpdate birth s v)) / (infectious s : ℝ)
      else f s := by
  by_cases ha : s.active.Nonempty
  · rw [prescribedStep, dite_eq_left ha,
      ← PMF.toMeasure_map _ _ (measurable_of_countable _),
      integral_map_of_stronglyMeasurable (measurable_of_countable _)
        (measurable_state f).stronglyMeasurable,
      uniformActive_integral_real]
    simp [ha]
  · rw [prescribedStep, dite_eq_right ha, PMF.toMeasure_pure, integral_dirac]
    simp [ha]

theorem localTreeStep_integral_real (l : ℝ≥0) (s : State) (f : State → ℝ) :
    (∫ t, f t ∂(localTreeStep l s).toMeasure) =
      (infectionProbability l 1 : ℝ) *
          (∫ t, f t ∂(prescribedStep true s).toMeasure) +
        (1 - (infectionProbability l 1 : ℝ)) *
          (∫ t, f t ∂(prescribedStep false s).toMeasure) := by
  rw [localTreeStep, FinitePMF.integral_bind_of_finite_support
    (eventChoice l 1) (fun b ↦ prescribedStep b s)
    (measurable_of_countable _) (Set.toFinite _)
    (fun b _ ↦ finite_support_prescribedStep b s)]
  exact eventChoice_integral_real l 1 _

theorem localTreeStep_heightPotential_harmonic (l : ℝ≥0) (h : ℕ)
    (s : State) :
    (∫ t, freshHeightPotential
        (Branching.successParameter l l.property) 1 (by omega) {0} h t
          ∂(localTreeStep l s).toMeasure) =
      freshHeightPotential
        (Branching.successParameter l l.property) 1 (by omega) {0} h s := by
  by_cases ha : s.active.Nonempty
  · rw [localTreeStep_integral_real,
      prescribedStep_integral_real true s _,
      prescribedStep_integral_real false s _]
    simp only [dite_eq_left ha]
    have hprob : (infectionProbability l 1 : ℝ) =
        CountCoupling.birthThreshold l := by
      simp [infectionProbability, CountCoupling.birthThreshold]
    rw [hprob]
    have hc : 0 < (infectious s : ℝ) := by exact_mod_cast ha.card_pos
    simp only [prescribedUpdate, Bool.false_eq_true, ↓reduceIte]
    calc
      _ = (∑ v ∈ s.active,
          (CountCoupling.birthThreshold l *
              freshHeightPotential (Branching.successParameter l l.property) 1
                (by omega) {0} h (infect s v) +
            (1 - CountCoupling.birthThreshold l) *
              freshHeightPotential (Branching.successParameter l l.property) 1
                (by omega) {0} h (recover s v))) / (infectious s : ℝ) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            ring
      _ = (∑ _v ∈ s.active,
          freshHeightPotential (Branching.successParameter l l.property) 1
            (by omega) {0} h s) / (infectious s : ℝ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro v hv
          exact CountCoupling.localHeightPotential_one_step l.property h s v hv
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_div_cancel_left₀ _ hc.ne'
  · have hs : s.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have hstep (b : Bool) : prescribedStep b s = PMF.pure s := by
      simp [prescribedStep, ha]
    rw [localTreeStep_integral_real, hstep, hstep]
    simp [PMF.toMeasure_pure]
    ring

/-- The finite-time state law of the constant-rate local tree. -/
def localTreeLaw (l : ℝ≥0) (k : ℕ) : PMF State :=
  FinitePMF.kernelEvolve (PMF.pure (initial 0)) (fun _ ↦ localTreeStep l) k

theorem localTreeLaw_support_finite (l : ℝ≥0) (k : ℕ) :
    (localTreeLaw l k).support.Finite :=
  FinitePMF.kernelEvolve_support_finite _ _ (by simp)
    (fun _ s ↦ finite_support_localTreeStep l s) k

/-- The geometric height-CDF potential has exactly constant expectation at
every finite time under the local tree kernel. -/
theorem localTreeLaw_heightPotential_expectation (l : ℝ≥0) (h k : ℕ) :
    (∫ s, freshHeightPotential
        (Branching.successParameter l l.property) 1 (by omega) {0} h s
          ∂(localTreeLaw l k).toMeasure) =
      Branching.extinctionProbability (Branching.successParameter l l.property) h := by
  induction k with
  | zero =>
      simp only [localTreeLaw, FinitePMF.kernelEvolve, PMF.toMeasure_pure, integral_dirac]
      exact freshHeightPotential_initial_one _ h
  | succ k ih =>
      rw [localTreeLaw, FinitePMF.kernelEvolve_integral_succ _ _ (by simp)
        (fun _ s ↦ finite_support_localTreeStep l s) (fun _ ↦ measurable_state _) k]
      simp_rw [localTreeStep_heightPotential_harmonic l h]
      exact ih

end HeightPaper.Model

namespace HeightPaper.CountCoupling

open HeightPaper.Model

theorem budgetBirth_one_one_eq_localBirth (l v : ℝ) :
    budgetBirth l 1 1 v = decide (v ≤ birthThreshold l) := by
  simp [budgetBirth, finiteThreshold]

/-- A pair of fresh uniform draws implements one constant-rate local-tree
transition. -/
def localTreeUpdate (l : ℝ) (s : State) (v : ℝ × ℝ) : State :=
  rankUpdate (budgetBirth l 1 1 v.1) s v.2

theorem measurable_localTreeUpdate (l : ℝ) (s : State) :
    Measurable (localTreeUpdate l s) := by
  have hm : Measurable (fun p : Bool × ℝ ↦ rankUpdate p.1 s p.2) :=
    measurable_from_prod_countable_right (fun b ↦ measurable_rankUpdate b s)
  exact hm.comp
    (((measurable_budgetBirth_scalar l 1 1).comp measurable_fst).prodMk measurable_snd)

theorem localTreeUpdate_law (l : ℝ≥0) (k : ℕ) (s : State) :
    birthParentLaw.map (fun q ↦ localTreeUpdate l s (q.1 k, q.2 k)) =
      (localTreeStep l s).toMeasure := by
  let X : ((ℕ → ℝ) × (ℕ → ℝ)) → Bool :=
    fun q ↦ budgetBirth l 1 1 (q.1 k)
  let Z : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun q ↦ q.2 k
  have hm : Measurable (fun u : ℕ → ℝ ↦ budgetBirth l 1 1 (u k)) :=
    measurable_budgetBirth l 1 k (fun _ ↦ 1) measurable_const
  have hX : Measurable X := hm.comp measurable_fst
  have hZ : Measurable Z := (measurable_pi_apply k).comp measurable_snd
  have hlaw : birthParentLaw.map X = (eventChoice l 1).toMeasure := by
    change birthParentLaw.map
      ((fun u ↦ budgetBirth l 1 1 (u k)) ∘ Prod.fst) = _
    rw [← Measure.map_map hm measurable_fst, birthParentLaw_map_fst,
      uniformLaw_map_budgetBirth]
    simp
  have hQ (b : Bool) : birthParentLaw.map (fun q ↦ rankUpdate b s (Z q)) =
      (prescribedStep b s).toMeasure := by
    have hm' : Measurable (fun u : ℕ → ℝ ↦ rankUpdate b s (u k)) :=
      (measurable_rankUpdate b s).comp (measurable_pi_apply k)
    change birthParentLaw.map ((fun u ↦ rankUpdate b s (u k)) ∘ Prod.snd) = _
    rw [← Measure.map_map hm' measurable_snd, birthParentLaw_map_snd, rankUpdate_law]
  exact independent_pmf_update birthParentLaw X Z (fun b v ↦ rankUpdate b s v)
    (eventChoice l 1) (fun b ↦ prescribedStep b s) hX hZ
    (fun b ↦ measurable_rankUpdate b s)
    ((measurable_localTreeUpdate l s).comp
      (((measurable_pi_apply k).comp measurable_fst).prodMk hZ))
    (indepFun_prod hm (measurable_pi_apply k)) hlaw hQ

def localTreeState (l : ℝ) (q : (ℕ → ℝ) × (ℕ → ℝ)) (k : ℕ) : State :=
  rankState (localBirth l q.1) (initial 0) q.2 k

theorem measurable_localTreeState (l : ℝ) (k : ℕ) :
    Measurable (fun q ↦ localTreeState l q k) :=
  (measurable_pi_apply k).comp (measurable_local_rankTrajectory l (initial 0))

theorem localTreeState_congr_prefix (l : ℝ)
    {q r : (ℕ → ℝ) × (ℕ → ℝ)} (k : ℕ)
    (hqr : ∀ i < k, q.1 i = r.1 i ∧ q.2 i = r.2 i) :
    localTreeState l q k = localTreeState l r k := by
  have hevents : ∀ i < k, localBirth l q.1 i = localBirth l r.1 i := by
    intro i hi
    simp [localBirth, (hqr i hi).1]
  calc
    _ = rankState (localBirth l r.1) (initial 0) q.2 k :=
      rankState_congr_events_prefix (initial 0) q.2 k hevents
    _ = _ := rankState_congr_prefix _ _ k (fun i hi ↦ (hqr i hi).2)

theorem localTreeState_succ (l : ℝ) (q : (ℕ → ℝ) × (ℕ → ℝ)) (k : ℕ) :
    localTreeState l q (k + 1) =
      localTreeUpdate l (localTreeState l q k) (q.1 k, q.2 k) := by
  change rankUpdate (localBirth l q.1 k) (localTreeState l q k) (q.2 k) =
    rankUpdate (budgetBirth l 1 1 (q.1 k)) (localTreeState l q k) (q.2 k)
  rw [budgetBirth_one_one_eq_localBirth]
  rfl

theorem paired_localTreeUpdate_law (l : ℝ≥0) (k : ℕ) (s : State) :
    pairedUniformLaw.map (fun w ↦ localTreeUpdate l s (w (0, k), w (1, k))) =
      (localTreeStep l s).toMeasure := by
  have hm : Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      localTreeUpdate l s (q.1 k, q.2 k)) :=
    (measurable_localTreeUpdate l s).comp
      (((measurable_pi_apply k).comp measurable_fst).prodMk
        ((measurable_pi_apply k).comp measurable_snd))
  change pairedUniformLaw.map ((fun q ↦ localTreeUpdate l s (q.1 k, q.2 k)) ∘
    splitUniforms) = _
  rw [← Measure.map_map hm measurable_splitUniforms, pairedUniformLaw_map_split,
    localTreeUpdate_law]

theorem paired_localTreeState_indep_next (l : ℝ) (k : ℕ) :
    IndepFun ((fun q ↦ localTreeState l q k) ∘ splitUniforms)
      (fun w : (Fin 2 × ℕ) → ℝ ↦ (w (0, k), w (1, k))) pairedUniformLaw := by
  have hind := pairedUniformLaw_independent.indepFun_set
    {i : Fin 2 × ℕ | i.2 < k} {i | i.2 = k}
    (by
      apply Set.disjoint_left.mpr
      intro i hi he
      simp only [Set.mem_ofPred_eq] at hi he
      omega) (fun i ↦ measurable_pi_apply i)
  have hh := hind.comp
    (((measurable_localTreeState l k).comp measurable_splitUniforms).comp
      (measurable_extendPairPast k))
    ((measurable_pi_apply (⟨(0, k), rfl⟩ : {i : Fin 2 × ℕ // i.2 = k})).prodMk
      (measurable_pi_apply (⟨(1, k), rfl⟩ : {i : Fin 2 × ℕ // i.2 = k})))
  have heq : ((fun q ↦ localTreeState l q k) ∘ splitUniforms ∘ extendPairPast k) ∘
      (fun (w : (Fin 2 × ℕ) → ℝ) (i : {i : Fin 2 × ℕ // i.2 < k}) ↦ w i) =
        (fun q ↦ localTreeState l q k) ∘ splitUniforms := by
    funext w
    apply localTreeState_congr_prefix
    intro j hj
    simp [splitUniforms, extendPairPast, hj]
  convert hh using 1
  · exact heq.symm
  · rfl

theorem paired_localTreeState_law (l : ℝ≥0) (k : ℕ) :
    pairedUniformLaw.map (fun w ↦ localTreeState l (splitUniforms w) k) =
      (localTreeLaw l k).toMeasure := by
  induction k with
  | zero =>
      change pairedUniformLaw.map (fun _ ↦ initial 0) = (PMF.pure (initial 0)).toMeasure
      simp [PMF.toMeasure_pure]
  | succ k ih =>
      have hs : (fun w ↦ localTreeState l (splitUniforms w) (k + 1)) =
          fun w ↦ localTreeUpdate l (localTreeState l (splitUniforms w) k)
            (w (0, k), w (1, k)) := by
        funext w
        exact localTreeState_succ l (splitUniforms w) k
      rw [hs]
      change pairedUniformLaw.map _ = ((localTreeLaw l k).bind (localTreeStep l)).toMeasure
      have hnew : Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦
          localTreeUpdate l (localTreeState l (splitUniforms w) k)
            (w (0, k), w (1, k))) := by
        have hm := (measurable_localTreeState l (k + 1)).comp measurable_splitUniforms
        change Measurable (fun w ↦ localTreeState l (splitUniforms w) (k + 1)) at hm
        rw [hs] at hm
        exact hm
      exact independent_pmf_update pairedUniformLaw
        (fun w ↦ localTreeState l (splitUniforms w) k)
        (fun w ↦ (w (0, k), w (1, k)))
        (fun s v ↦ localTreeUpdate l s v)
        (localTreeLaw l k) (localTreeStep l)
        ((measurable_localTreeState l k).comp measurable_splitUniforms)
        ((measurable_pi_apply (0, k)).prodMk (measurable_pi_apply (1, k)))
        (fun s ↦ measurable_localTreeUpdate l s)
        hnew
        (paired_localTreeState_indep_next l k) ih
        (paired_localTreeUpdate_law l k)

/-- At each finite time the existing common-uniform local tree has exactly
the Markov law with constant birth intensity. -/
theorem localTreeState_law (l : ℝ≥0) (k : ℕ) :
    birthParentLaw.map (fun q ↦ localTreeState l q k) =
      (localTreeLaw l k).toMeasure := by
  rw [← pairedUniformLaw_map_split]
  rw [Measure.map_map (measurable_localTreeState l k) measurable_splitUniforms]
  exact paired_localTreeState_law l k

/-- The geometric potential has constant expectation on the very same
two-uniform probability space used for the paper's local early height. -/
theorem localTreeState_heightPotential_expectation (l : ℝ≥0) (h k : ℕ) :
    (∫ q, freshHeightPotential
        (Branching.successParameter l l.property) 1 (by omega) {0} h
          (localTreeState l q k) ∂birthParentLaw) =
      Branching.extinctionProbability (Branching.successParameter l l.property) h := by
  rw [← localTreeLaw_heightPotential_expectation l h k,
    ← localTreeState_law l k]
  exact (integral_map (measurable_localTreeState l k).aemeasurable
    (measurable_state _).aestronglyMeasurable).symm

theorem localTreeState_infectious_eq_localWalk {l : ℝ}
    (q : (ℕ → ℝ) × (ℕ → ℝ))
    (hs : q.1 ∈ localSurvival l) (k : ℕ) :
    ((localTreeState l q k).active.card : ℤ) = localWalk l q.1 k := by
  have hcast (j : ℕ) :
      (prescribedWalk (localBirth l q.1) 1 j : ℤ) = localWalk l q.1 j := by
    exact prescribedWalk_cast_eq_of_positive _ _ (by simp [localWalk])
      (localWalk_succ l q.1) (fun i _ ↦ hs i)
  have hpos (j : ℕ) : 0 < prescribedWalk (localBirth l q.1) 1 j := by
    have hj := hs j
    have he := hcast j
    omega
  have he := infectious_rankState (localBirth l q.1) (initial 0) q.2 k
    (fun j _ ↦ hpos j)
  change (localTreeState l q k).active.card = _ at he
  exact (congrArg (fun x : ℕ ↦ (x : ℤ)) he).trans (hcast k)

/-- On an infinite-survival path with the strong-law linear count bound, the
height potential vanishes. This also covers paths that never reach height
`h`, because every active vertex then contributes a factor strictly below one. -/
theorem localTreeState_heightPotential_tendsto_zero_on_survival
    {l : ℝ} (hl : 1 < l) (q : (ℕ → ℝ) × (ℕ → ℝ))
    (hs : q.1 ∈ localSurvival l)
    (hlinear : ∃ N : ℕ, ∀ k ≥ N,
      localDrift l / 2 * k ≤ (localWalk l q.1 k : ℝ)) (h : ℕ) :
    Filter.Tendsto (fun k ↦ Model.freshHeightPotential
        (Branching.successParameter l (by linarith)) 1 (by omega) {0} h
          (localTreeState l q k)) Filter.atTop (nhds 0) := by
  let p := Branching.successParameter l (by linarith)
  let a := Branching.extinctionProbability p h
  have hp : 0 < (p : ℝ) := Branching.successParameter_pos l (by linarith)
  have ha0 : 0 ≤ a := Branching.extinctionProbability_nonneg p h
  have ha1 : a < 1 := Branching.extinctionProbability_lt_one_of_mean_gt_one hp
    (by simpa [p] using hl) h
  obtain ⟨N, hN⟩ := hlinear
  have hc : 0 < localDrift l / 2 := half_pos (localDrift_pos hl)
  have hcountR : Filter.Tendsto
      (fun k : ℕ ↦ ((localTreeState l q k).active.card : ℝ))
      Filter.atTop Filter.atTop := by
    apply tendsto_atTop_mono' Filter.atTop ?_
      (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hw := hN k hk
    have he := localTreeState_infectious_eq_localWalk q hs k
    have heR : ((localTreeState l q k).active.card : ℝ) =
        (localWalk l q.1 k : ℝ) := by exact_mod_cast he
    rw [heR]
    exact hw
  have hcount : Filter.Tendsto (fun k : ℕ ↦ (localTreeState l q k).active.card)
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_iff.mp hcountR
  have hpow : Filter.Tendsto (fun k : ℕ ↦ a ^ (localTreeState l q k).active.card)
      Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).comp hcount
  apply squeeze_zero
    (fun k ↦ (Model.freshHeightPotential_bounds p 1 (by omega) {0} h
      (localTreeState l q k)).1)
    (fun k ↦ Model.freshHeightPotential_one_le_pow_active p hp h
      (localTreeState l q k))
    hpow

theorem localTreeState_heightPotential_eventually_of_extinction
    (l : ℝ) (p : unitInterval) (h : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ))
    (hs : q.1 ∉ localSurvival l) :
    ∀ᶠ k : ℕ in Filter.atTop,
      Model.freshHeightPotential p 1 (by omega) {0} h (localTreeState l q k) =
        if localEarlyHeight l q < h then 1 else 0 := by
  filter_upwards [eventually_ge_atTop (localEarlyExtinctionTime l q.1)] with k hk
  have hstable := rankState_absorbed_stable (localBirth l q.1) (initial 0) q.2
    hk (localEarlyTree_absorbed hs)
  change localTreeState l q k = _ at hstable
  rw [hstable]
  exact localEarlyHeight_potential_terminal_of_extinction l p h q hs

def localLinearGood (l : ℝ) : Set (ℕ → ℝ) :=
  {u | ∃ N : ℕ, ∀ k ≥ N,
    localDrift l / 2 * k ≤ (localWalk l u k : ℝ)}

theorem measurableSet_localLinearGood (l : ℝ) :
    MeasurableSet (localLinearGood l) := by
  have hset : localLinearGood l =
      ⋃ N : ℕ, ⋂ k : ℕ,
        {u | N ≤ k → localDrift l / 2 * k ≤ (localWalk l u k : ℝ)} := by
    ext u
    simp [localLinearGood]
  rw [hset]
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro k
  by_cases hk : N ≤ k
  · simpa only [hk, true_implies] using
      (measurableSet_le measurable_const (measurable_localWalk_real l k))
  · simp [hk]

theorem birthParentLaw_ae_localLinearGood {l : ℝ} (hl : 1 < l) :
    ∀ᵐ q ∂birthParentLaw, q.1 ∈ localLinearGood l := by
  have hbase : ∀ᵐ u ∂uniformLaw, u ∈ localLinearGood l := by
    filter_upwards [localWalk_ae_eventually_uniform_lower hl] with u hu
    obtain ⟨N, hN⟩ := hu
    exact ⟨N, fun k hk ↦ hN k hk l le_rfl⟩
  rw [← birthParentLaw_map_fst] at hbase
  exact (ae_map_iff measurable_fst.aemeasurable
    (measurableSet_localLinearGood l)).mp hbase

/-- Exact local early-tree height CDF on the finite-extinction branch. The
normalization by its total mass `1 / l` gives the subcritical reciprocal-mean
geometric branching height law. -/
theorem localEarlyHeight_extinction_cdf_eq {l : ℝ} (hl : 1 < l) (h : ℕ) :
    birthParentLaw.real
      {q | q.1 ∉ localSurvival l ∧ localEarlyHeight l q < h} =
      Branching.extinctionProbability
        (Branching.successParameter l (by linarith)) h := by
  let p := Branching.successParameter l (by linarith)
  let E : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | q.1 ∉ localSurvival l ∧ localEarlyHeight l q < h}
  let F : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ :=
    fun k q ↦ Model.freshHeightPotential p 1 (by omega) {0} h (localTreeState l q k)
  have hFmeas (k : ℕ) : AEStronglyMeasurable (F k) birthParentLaw := by
    change AEStronglyMeasurable
      ((fun s : State ↦ Model.freshHeightPotential p 1 (by omega) {0} h s) ∘
        (fun q ↦ localTreeState l q k)) birthParentLaw
    exact ((Model.measurable_state _).comp
      (measurable_localTreeState l k)).aestronglyMeasurable
  have hbound (k : ℕ) : ∀ᵐ q ∂birthParentLaw, ‖F k q‖ ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro q
    have hb := Model.freshHeightPotential_bounds p 1 (by omega) {0} h
      (localTreeState l q k)
    change ‖Model.freshHeightPotential p 1 (by omega) {0} h (localTreeState l q k)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  have hlim : ∀ᵐ q ∂birthParentLaw,
      Filter.Tendsto (fun k ↦ F k q) Filter.atTop
        (𝓝 (E.indicator (fun _ ↦ (1 : ℝ)) q)) := by
    filter_upwards [birthParentLaw_ae_localLinearGood hl] with q hgood
    by_cases hs : q.1 ∈ localSurvival l
    · have ht := localTreeState_heightPotential_tendsto_zero_on_survival hl q hs hgood h
      simpa [F, E, Set.indicator, hs] using ht
    · have hev := localTreeState_heightPotential_eventually_of_extinction l p h q hs
      have ht : Filter.Tendsto (fun k ↦ F k q) Filter.atTop
          (𝓝 (if localEarlyHeight l q < h then 1 else 0)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [hev] with k hk
        exact hk.symm
      simpa [F, E, Set.indicator, hs] using ht
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := birthParentLaw) (fun _ ↦ (1 : ℝ)) hFmeas (integrable_const 1) hbound hlim
  have hconstant : Filter.Tendsto
      (fun k : ℕ ↦ Branching.extinctionProbability p h)
      Filter.atTop (𝓝 (Branching.extinctionProbability p h)) := tendsto_const_nhds
  have hsame : (fun k : ℕ ↦ ∫ q, F k q ∂birthParentLaw) =
      fun _ ↦ Branching.extinctionProbability p h := by
    funext k
    exact localTreeState_heightPotential_expectation ⟨l, by linarith⟩ h k
  rw [hsame] at hDCT
  have hident : (∫ q, E.indicator (fun _ ↦ (1 : ℝ)) q ∂birthParentLaw) =
      Branching.extinctionProbability p h :=
    tendsto_nhds_unique hDCT hconstant
  have hE : MeasurableSet E := by
    exact ((measurableSet_localSurvival l).preimage measurable_fst).compl.inter
      (measurableSet_lt (measurable_localEarlyHeight l) measurable_const)
  change (∫ q, E.indicator (1 : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ) q ∂birthParentLaw) =
    Branching.extinctionProbability p h at hident
  rw [integral_indicator_one hE] at hident
  exact hident

theorem birthParentLaw_localExtinction_probability_eq {l : ℝ} (hl : 1 < l) :
    birthParentLaw.real {q | q.1 ∉ localSurvival l} = 1 / l := by
  let A : Set ((ℕ → ℝ) × (ℕ → ℝ)) := {q | q.1 ∈ localSurvival l}
  have hA : MeasurableSet A :=
    (measurableSet_localSurvival l).preimage measurable_fst
  have hsurv : birthParentLaw.real A = 1 - 1 / l := by
    have hh := localSurvival_probability_eq hl
    rw [← birthParentLaw_map_fst] at hh
    rw [Measure.real, Measure.map_apply measurable_fst
      (measurableSet_localSurvival l)] at hh
    change birthParentLaw.real A = 1 - 1 / l at hh
    exact hh
  have hcomp : {q : (ℕ → ℝ) × (ℕ → ℝ) | q.1 ∉ localSurvival l} = Aᶜ := by
    ext q
    simp [A]
  rw [hcomp, measureReal_compl hA, hsurv, probReal_univ]
  ring

/-- On extinction, the actual local tree has the same height CDF as a
subcritical geometric Bienaymé tree with mean `1 / l`. -/
theorem localEarlyHeight_conditional_cdf_eq_subcritical {l : ℝ}
    (hl : 1 < l) (h : ℕ) :
    birthParentLaw.real
        {q | q.1 ∉ localSurvival l ∧ localEarlyHeight l q < h} /
      birthParentLaw.real {q | q.1 ∉ localSurvival l} =
        Branching.extinctionProbability
          (Branching.successParameter (1 / l) (by positivity)) h := by
  rw [birthParentLaw_localExtinction_probability_eq hl,
    localEarlyHeight_extinction_cdf_eq hl]
  exact Branching.extinctionProbability_supercritical_conditioned_eq_subcritical hl h

end HeightPaper.CountCoupling
