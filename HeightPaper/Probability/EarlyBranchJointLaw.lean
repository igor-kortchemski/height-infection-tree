module

public import HeightPaper.Probability.EarlyBranchLocalLaw

/-!
# The early-extinction time and height on the coupled finite and local trees

The finite variables below are zero on survival through a prescribed horizon.
Otherwise they record the first zero of the coupled walk and the height at
that event. They are the unscaled coordinates needed for `lem:limflu`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal symmDiff Classical

namespace HeightPaper.CountCoupling

theorem measurableSet_finiteSurvival (a : ℝ) (n H : ℕ) :
    MeasurableSet (finiteSurvival a n H) := by
  have hset : finiteSurvival a n H =
      ⋂ j ∈ Finset.Iic H, {u | 0 < finiteWalk a n u j} := by
    ext u
    simp [finiteSurvival]
  rw [hset]
  apply (Finset.Iic H).measurableSet_biInter
  intro j _
  exact measurableSet_lt measurable_const (measurable_finiteWalk a n j)

def finiteEarlyHit (a : ℝ) (n H : ℕ) (u : ℕ → ℝ) (k : ℕ) : Prop :=
  (finiteWalk a n u k ≤ 0 ∧ k ≤ H) ∨
    (k = 0 ∧ u ∈ finiteSurvival a n H)

theorem finiteEarlyHit_exists (a : ℝ) (n H : ℕ) (u : ℕ → ℝ) :
    ∃ k, finiteEarlyHit a n H u k := by
  by_cases hs : u ∈ finiteSurvival a n H
  · exact ⟨0, Or.inr ⟨rfl, hs⟩⟩
  · have hhit : ∃ k, ∃ _ : k ≤ H, finiteWalk a n u k ≤ 0 := by
      simpa only [finiteSurvival, mem_ofPred_eq, not_forall, not_imp, not_lt]
        using hs
    obtain ⟨k, hk, hz⟩ := hhit
    exact ⟨k, Or.inl ⟨hz, hk⟩⟩

/-- The first extinction event of the finite walk, clipped to zero on
survival through the prescribed horizon. -/
noncomputable def finiteEarlyExtinctionTime (a : ℝ) (n H : ℕ)
    (u : ℕ → ℝ) : ℕ :=
  @Nat.find (finiteEarlyHit a n H u) (Classical.decPred _)
    (finiteEarlyHit_exists a n H u)

theorem measurable_finiteEarlyExtinctionTime (a : ℝ) (n H : ℕ) :
    Measurable (finiteEarlyExtinctionTime a n H) := by
  classical
  have hs := measurableSet_finiteSurvival a n H
  have hm (k : ℕ) : MeasurableSet {u | finiteEarlyHit a n H u k} := by
    have hset : {u | finiteEarlyHit a n H u k} =
        ({u | finiteWalk a n u k ≤ 0} ∩ {u | k ≤ H}) ∪
          {u | k = 0 ∧ u ∈ finiteSurvival a n H} := by
      ext u
      simp [finiteEarlyHit]
    rw [hset]
    have hfirst : MeasurableSet
        ({u | finiteWalk a n u k ≤ 0} ∩ {u | k ≤ H}) := by
      refine (measurableSet_le (measurable_finiteWalk a n k) measurable_const).inter ?_
      by_cases hk : k ≤ H <;> simp [hk]
    have hsecond : MeasurableSet {u | k = 0 ∧ u ∈ finiteSurvival a n H} := by
      by_cases hk : k = 0
      · simpa [hk] using hs
      · simp [hk]
    exact hfirst.union hsecond
  exact measurable_find (fun u ↦ finiteEarlyHit_exists a n H u) hm

theorem finiteEarlyExtinctionTime_eq_zero_iff (a : ℝ) (n H : ℕ)
    (u : ℕ → ℝ) :
    finiteEarlyExtinctionTime a n H u = 0 ↔
      u ∈ finiteSurvival a n H := by
  classical
  unfold finiteEarlyExtinctionTime
  rw [Nat.find_eq_zero]
  simp [finiteEarlyHit, finiteWalk_zero]

theorem finiteEarlyExtinctionTime_spec {a : ℝ} {n H : ℕ}
    {u : ℕ → ℝ} (hs : u ∉ finiteSurvival a n H) :
    0 < finiteEarlyExtinctionTime a n H u ∧
      finiteEarlyExtinctionTime a n H u ≤ H ∧
      finiteWalk a n u (finiteEarlyExtinctionTime a n H u) = 0 ∧
      ∀ j < finiteEarlyExtinctionTime a n H u,
        0 < finiteWalk a n u j := by
  classical
  let T := finiteEarlyExtinctionTime a n H u
  have hT : 0 < T := by
    have hne : T ≠ 0 := fun h ↦ hs
      ((finiteEarlyExtinctionTime_eq_zero_iff a n H u).mp h)
    omega
  have hhit : finiteWalk a n u T ≤ 0 ∧ T ≤ H := by
    have hh := Nat.find_spec (finiteEarlyHit_exists a n H u)
    change finiteEarlyHit a n H u T at hh
    rcases hh with hh | ⟨_, hsurv⟩
    · exact hh
    · exact (hs hsurv).elim
  have hbefore (j : ℕ) (hj : j < T) : 0 < finiteWalk a n u j := by
    have hmiss := Nat.find_min (finiteEarlyHit_exists a n H u) hj
    have hjH : j ≤ H := by omega
    have hn : ¬(finiteWalk a n u j ≤ 0) :=
      fun hz ↦ hmiss (Or.inl ⟨hz, hjH⟩)
    omega
  have hprev := hbefore (T - 1) (by omega)
  have hTsucc : T - 1 + 1 = T := by omega
  have hstep := finiteWalk_succ a n u (T - 1)
  rw [hTsucc] at hstep
  have hzero : finiteWalk a n u T = 0 := by
    split_ifs at hstep <;> omega
  exact ⟨hT, hhit.2, hzero, hbefore⟩

/-- Height of the finite early tree at its first extinction event, zero on
survival through the horizon. -/
noncomputable def finiteEarlyHeight (a : ℝ) (n H : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) : ℕ :=
  Model.height (Model.rankState (finiteBirth a n q.1) (Model.initial n) q.2
    (finiteEarlyExtinctionTime a n H q.1))

theorem measurable_finiteTreeHeight_at (a : ℝ) (n k : ℕ) :
    Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      Model.height (Model.rankState (finiteBirth a n q.1) (Model.initial n) q.2 k)) := by
  have hh := (Model.FinitePath.measurable
    (fun p : Model.FinitePath k ↦ Model.height p.last)).comp
      (measurable_coupledTreeHistory a n k)
  have heq : (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      Model.height (coupledTreeHistory a n k q).last) =
      (fun q ↦ Model.height (Model.rankState (finiteBirth a n q.1)
        (Model.initial n) q.2 k)) := by
    funext q
    simp only [coupledTreeHistory, Model.rankHistory, Model.trajectoryPrefix_last]
  rw [← heq]
  exact hh

theorem finiteEarlyHeight_zero_of_survival {a : ℝ} {n H : ℕ}
    {q : (ℕ → ℝ) × (ℕ → ℝ)}
    (hs : q.1 ∈ finiteSurvival a n H) :
    finiteEarlyHeight a n H q = 0 := by
  have hT := (finiteEarlyExtinctionTime_eq_zero_iff a n H q.1).mpr hs
  simp [finiteEarlyHeight, hT, Model.rankState, Model.height_initial]

theorem finiteEarlyTree_absorbed {a : ℝ} {n H : ℕ}
    {q : (ℕ → ℝ) × (ℕ → ℝ)}
    (hs : q.1 ∉ finiteSurvival a n H) :
    (Model.rankState (finiteBirth a n q.1) (Model.initial n) q.2
      (finiteEarlyExtinctionTime a n H q.1)).active = ∅ := by
  let T := finiteEarlyExtinctionTime a n H q.1
  obtain ⟨_, _, hzero, hbefore⟩ := finiteEarlyExtinctionTime_spec hs
  change finiteWalk a n q.1 T = 0 at hzero
  have hcast (j : ℕ) (hj : j ≤ T) :
      (Model.prescribedWalk (finiteBirth a n q.1) 1 j : ℤ) =
        finiteWalk a n q.1 j :=
    prescribedWalk_cast_eq_of_positive _ _ (finiteWalk_zero a n q.1)
      (finiteWalk_succ a n q.1)
      (fun i hi ↦ hbefore i (hi.trans_le hj))
  have hpositive (j : ℕ) (hj : j < T) :
      0 < Model.prescribedWalk (finiteBirth a n q.1) 1 j := by
    have hh := hcast j hj.le
    have hp := hbefore j hj
    omega
  have hcount := Model.infectious_rankState (finiteBirth a n q.1)
    (Model.initial n) q.2 T hpositive
  simp only [Model.infectious_initial] at hcount
  have hzeroCount : Model.infectious
      (Model.rankState (finiteBirth a n q.1) (Model.initial n) q.2 T) = 0 := by
    have hh := hcast T le_rfl
    omega
  exact Finset.card_eq_zero.mp hzeroCount

/-- On an extinct finite outbreak, the early height is the actual height at
the prescribed horizon, since the tree is absorbed after first extinction. -/
theorem finiteEarlyHeight_eq_horizon_of_extinct {a : ℝ} {n H : ℕ}
    {q : (ℕ → ℝ) × (ℕ → ℝ)}
    (hs : q.1 ∉ finiteSurvival a n H) :
    finiteEarlyHeight a n H q =
      Model.height (Model.rankState (finiteBirth a n q.1)
        (Model.initial n) q.2 H) := by
  have hTH := (finiteEarlyExtinctionTime_spec hs).2.1
  have hstable := Model.rankState_absorbed_stable
    (finiteBirth a n q.1) (Model.initial n) q.2 hTH
    (finiteEarlyTree_absorbed hs)
  unfold finiteEarlyHeight
  exact congrArg Model.height hstable.symm

/-- The stopped height is a measurable choice between zero and the ordinary
finite-horizon tree height. -/
theorem finiteEarlyHeight_eq_ite (a : ℝ) (n H : ℕ) :
    finiteEarlyHeight a n H = fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      if q.1 ∈ finiteSurvival a n H then 0 else
        Model.height (Model.rankState (finiteBirth a n q.1)
          (Model.initial n) q.2 H) := by
  classical
  funext q
  by_cases hs : q.1 ∈ finiteSurvival a n H
  · rw [ite_eq_left hs]
    exact finiteEarlyHeight_zero_of_survival hs
  · rw [ite_eq_right hs]
    exact finiteEarlyHeight_eq_horizon_of_extinct hs

theorem measurable_finiteEarlyHeight (a : ℝ) (n H : ℕ) :
    Measurable (finiteEarlyHeight a n H) := by
  classical
  rw [finiteEarlyHeight_eq_ite]
  have hs : MeasurableSet {q : (ℕ → ℝ) × (ℕ → ℝ) |
      q.1 ∈ finiteSurvival a n H} :=
    (measurableSet_finiteSurvival a n H).preimage measurable_fst
  exact Measurable.ite hs measurable_const (measurable_finiteTreeHeight_at a n H)

/-- Matching birth words give the same unabsorbed signed walk on the whole
matched prefix. -/
theorem finiteWalk_eq_localWalk_of_birth_prefix
    {a l : ℝ} {n K : ℕ} {u : ℕ → ℝ}
    (he : ∀ i < K, finiteBirth a n u i = localBirth l u i) :
    ∀ k ≤ K, finiteWalk a n u k = localWalk l u k := by
  intro k hk
  unfold finiteWalk localWalk
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [he i ((Finset.mem_range.mp hi).trans_le hk)]

/-- If the finite and local survival indicators agree, then a matched prefix
containing the local extinction time identifies their first zero exactly. -/
theorem finiteEarlyExtinctionTime_eq_local_of_prefix
    {a l : ℝ} {n H K : ℕ} {u : ℕ → ℝ}
    (hsurv : u ∈ finiteSurvival a n H ↔ u ∈ localSurvival l)
    (hKH : K ≤ H)
    (hTK : localEarlyExtinctionTime l u ≤ K)
    (he : ∀ i < K, finiteBirth a n u i = localBirth l u i) :
    finiteEarlyExtinctionTime a n H u = localEarlyExtinctionTime l u := by
  classical
  by_cases hs : u ∈ localSurvival l
  · rw [(finiteEarlyExtinctionTime_eq_zero_iff a n H u).mpr (hsurv.mpr hs),
      (localEarlyExtinctionTime_eq_zero_iff l u).mpr hs]
  · have hwalk := finiteWalk_eq_localWalk_of_birth_prefix he
    obtain ⟨hTpos, hzero, hbefore⟩ := localEarlyExtinctionTime_spec hs
    have hfin : u ∉ finiteSurvival a n H := fun h ↦ hs (hsurv.mp h)
    unfold finiteEarlyExtinctionTime
    apply (Nat.find_eq_iff (finiteEarlyHit_exists a n H u)).mpr
    constructor
    · exact Or.inl ⟨by rw [hwalk _ hTK]; exact le_of_eq hzero, hTK.trans hKH⟩
    · intro j hj hhit
      rcases hhit with ⟨hz, _⟩ | ⟨_, hsurv'⟩
      · have heq := hwalk j (hj.le.trans hTK)
        have hp := hbefore j hj
        omega
      · exact hfin hsurv'

/-- The same early-prefix coupling identifies the unscaled extinction
height, simultaneously with extinction time. -/
theorem finiteEarlyHeight_eq_local_of_prefix
    {a l : ℝ} {n H K : ℕ} {q : (ℕ → ℝ) × (ℕ → ℝ)}
    (hsurv : q.1 ∈ finiteSurvival a n H ↔ q.1 ∈ localSurvival l)
    (hKH : K ≤ H)
    (hTK : localEarlyExtinctionTime l q.1 ≤ K)
    (he : ∀ i < K, finiteBirth a n q.1 i = localBirth l q.1 i) :
    finiteEarlyHeight a n H q = localEarlyHeight l q := by
  unfold finiteEarlyHeight localEarlyHeight
  rw [finiteEarlyExtinctionTime_eq_local_of_prefix hsurv hKH hTK he]
  apply Model.finite_local_rankState_height_eq
  intro i hi
  exact he i (hi.trans_le hTK)

/-- The joint time-height disagreement is bounded by survival disagreement,
the local extinction-time tail, and a finite birth-word mismatch. -/
theorem finiteEarly_joint_disagreement_probability_le
    {a l : ℝ} {n H K : ℕ} (hKH : K ≤ H) :
    birthParentLaw.real {q | finiteEarlyExtinctionTime a n H q.1 ≠
          localEarlyExtinctionTime l q.1 ∨
        finiteEarlyHeight a n H q ≠ localEarlyHeight l q} ≤
      uniformLaw.real (finiteSurvival a n H ∆ localSurvival l) +
        uniformLaw.real {u | K < localEarlyExtinctionTime l u} +
          uniformLaw.real {u | ∃ i < K, finiteBirth a n u i ≠ localBirth l u i} := by
  let S : Set (ℕ → ℝ) := finiteSurvival a n H ∆ localSurvival l
  let L : Set (ℕ → ℝ) := {u | K < localEarlyExtinctionTime l u}
  let P : Set (ℕ → ℝ) :=
    {u | ∃ i < K, finiteBirth a n u i ≠ localBirth l u i}
  have hP : MeasurableSet P := by
    have hset : P = ⋃ i ∈ Finset.range K,
        {u | finiteBirth a n u i ≠ localBirth l u i} := by
      ext u
      simp [P]
    rw [hset]
    apply (Finset.range K).measurableSet_biUnion
    intro i _
    have hm := (measurable_finiteBirth a n i).prodMk (measurable_localBirth l i)
    exact hm ((Set.to_countable {p : Bool × Bool | p.1 ≠ p.2}).measurableSet)
  have hS : MeasurableSet S :=
    (measurableSet_finiteSurvival a n H).symmDiff (measurableSet_localSurvival l)
  have hL : MeasurableSet L :=
    measurableSet_lt measurable_const (measurable_localEarlyExtinctionTime l)
  have hU : MeasurableSet (S ∪ (L ∪ P)) := hS.union (hL.union hP)
  have hsub : {q : (ℕ → ℝ) × (ℕ → ℝ) |
      finiteEarlyExtinctionTime a n H q.1 ≠ localEarlyExtinctionTime l q.1 ∨
        finiteEarlyHeight a n H q ≠ localEarlyHeight l q} ⊆
      Prod.fst ⁻¹' (S ∪ (L ∪ P)) := by
    intro q hbad
    by_cases hs : q.1 ∈ finiteSurvival a n H ↔ q.1 ∈ localSurvival l
    · by_cases hT : localEarlyExtinctionTime l q.1 ≤ K
      · by_cases hp : ∀ i < K, finiteBirth a n q.1 i = localBirth l q.1 i
        · have ht := finiteEarlyExtinctionTime_eq_local_of_prefix hs hKH hT hp
          have hh := finiteEarlyHeight_eq_local_of_prefix hs hKH hT hp
          exact (hbad.elim (fun h ↦ (h ht).elim) (fun h ↦ (h hh).elim))
        · apply Or.inr; apply Or.inr
          push Not at hp
          exact hp
      · apply Or.inr; apply Or.inl
        exact lt_of_not_ge hT
    · apply Or.inl
      simp only [S, mem_symmDiff]
      tauto
  calc
    birthParentLaw.real {q | finiteEarlyExtinctionTime a n H q.1 ≠
          localEarlyExtinctionTime l q.1 ∨
        finiteEarlyHeight a n H q ≠ localEarlyHeight l q} ≤
      birthParentLaw.real (Prod.fst ⁻¹' (S ∪ (L ∪ P))) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = uniformLaw.real (S ∪ (L ∪ P)) := by
      rw [← birthParentLaw_map_fst]
      simp only [Measure.real, Measure.map_apply measurable_fst hU]
    _ ≤ uniformLaw.real S + uniformLaw.real L + uniformLaw.real P := by
      calc
        uniformLaw.real (S ∪ (L ∪ P)) ≤
            uniformLaw.real S + uniformLaw.real (L ∪ P) :=
          measureReal_union_le S (L ∪ P)
        _ ≤ uniformLaw.real S + (uniformLaw.real L + uniformLaw.real P) :=
          add_le_add le_rfl (measureReal_union_le L P)
        _ = _ := by ring

/-- Under every rate sequence allowed by the paper, the two unscaled early
coordinates converge jointly in probability on the common birth-parent space.
This is a coupling statement, stronger than convergence in distribution for
these coordinates. -/
theorem finiteEarly_joint_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ birthParentLaw.real {q |
      finiteEarlyExtinctionTime ((rates n : ℝ) * n) n ⌊T * n⌋₊ q.1 ≠
        localEarlyExtinctionTime l q.1 ∨
      finiteEarlyHeight ((rates n : ℝ) * n) n ⌊T * n⌋₊ q ≠
        localEarlyHeight l q}) atTop (𝓝 0) := by
  have hs := finiteSurvival_rateSequence_local_disagreement_tendsto_zero
    rates hl hT hrates
  have ht := localEarlyExtinctionTime_tail_tendsto_zero hl
  have hH : Tendsto (fun n : ℕ ↦ ⌊T * n⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hT.1)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n ↦ ha.trans_le measureReal_nonneg)
  · intro b hb
    have hb3 : 0 < b / 3 := by positivity
    obtain ⟨K, hK⟩ := (ht.eventually (Iio_mem_nhds hb3)).exists
    have hp := finiteBirth_localBirth_prefix_disagreement_tendsto_zero
      rates (zero_lt_one.trans hl).le hrates K
    have hH_K : ∀ᶠ n : ℕ in atTop, K ≤ ⌊T * n⌋₊ :=
      hH.eventually (eventually_ge_atTop K)
    filter_upwards [hs.eventually (Iio_mem_nhds hb3),
      hp.eventually (Iio_mem_nhds hb3), hH_K] with n hsn hpn hKn
    have hbound := finiteEarly_joint_disagreement_probability_le
      (a := (rates n : ℝ) * n) (l := l) (n := n)
      (H := ⌊T * n⌋₊) (K := K) hKn
    change uniformLaw.real
      {u | K < localEarlyExtinctionTime l u} < b / 3 at hK
    linarith

/-- Extinction exactly at a growing preterminal horizon has vanishing
probability. This is the boundary estimate needed when converting between
the paper's real-time threshold and the floored event horizon. -/
theorem finiteEarly_horizon_extinction_probability_tendsto_zero
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ birthParentLaw.real {q |
      finiteEarlyExtinctionTime ((rates n : ℝ) * n) n ⌊T * n⌋₊ q.1 =
        ⌊T * n⌋₊}) atTop (𝓝 0) := by
  have hearly := finiteEarly_joint_disagreement_tendsto_zero rates hl hT hrates
  have htail := localEarlyExtinctionTime_tail_tendsto_zero hl
  have hH : Tendsto (fun n : ℕ ↦ ⌊T * n⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hT.1)
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall (fun n ↦ hb.trans_le measureReal_nonneg)
  · intro b hb
    have hb2 : 0 < b / 2 := by positivity
    obtain ⟨K, hK⟩ := (htail.eventually (Iio_mem_nhds hb2)).exists
    have hHK : ∀ᶠ n : ℕ in atTop, K < ⌊T * n⌋₊ :=
      hH.eventually (eventually_gt_atTop K)
    filter_upwards [hearly.eventually (Iio_mem_nhds hb2), hHK] with n he hn
    let H := ⌊T * n⌋₊
    let E : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
      {q | finiteEarlyExtinctionTime ((rates n : ℝ) * n) n H q.1 ≠
          localEarlyExtinctionTime l q.1 ∨
        finiteEarlyHeight ((rates n : ℝ) * n) n H q ≠
          localEarlyHeight l q}
    let L : Set (ℕ → ℝ) := {u | K < localEarlyExtinctionTime l u}
    have hsub : {q | finiteEarlyExtinctionTime ((rates n : ℝ) * n) n H q.1 = H} ⊆
        E ∪ (Prod.fst ⁻¹' L) := by
      intro q hq
      by_cases hne : finiteEarlyExtinctionTime ((rates n : ℝ) * n) n H q.1 ≠
          localEarlyExtinctionTime l q.1
      · exact Or.inl (Or.inl hne)
      · right
        have hlocal : localEarlyExtinctionTime l q.1 = H := by
          exact (not_ne_iff.mp hne).symm.trans hq
        change K < localEarlyExtinctionTime l q.1
        rw [hlocal]
        exact hn
    have hL : MeasurableSet L :=
      measurableSet_lt measurable_const (measurable_localEarlyExtinctionTime l)
    have hmass : birthParentLaw.real (Prod.fst ⁻¹' L) =
        uniformLaw.real L := by
      rw [← birthParentLaw_map_fst]
      simp only [Measure.real, Measure.map_apply measurable_fst hL]
    have hbound : birthParentLaw.real
        {q | finiteEarlyExtinctionTime ((rates n : ℝ) * n) n H q.1 = H} ≤
        birthParentLaw.real E + birthParentLaw.real (Prod.fst ⁻¹' L) :=
      (measureReal_mono hsub (measure_ne_top _ _)).trans
        (measureReal_union_le E (Prod.fst ⁻¹' L))
    change birthParentLaw.real E < b / 2 at he
    change uniformLaw.real L < b / 2 at hK
    simp only [H] at hbound ⊢
    rw [hmass] at hbound
    linarith

end HeightPaper.CountCoupling

namespace HeightPaper.Model

/-- Every prescribed active rank update is one genuine epidemic event. -/
theorem eventCount_rankUpdate_of_nonempty (birth : Bool) (s : State)
    (hs : s.active.Nonempty) (v : ℝ) :
    eventCount (rankUpdate birth s v) = eventCount s + 1 := by
  rw [rankUpdate_of_nonempty birth s hs v]
  cases birth with
  | false =>
      change eventCount (recover s (activeAtRank s
        (uniformRank s.active.card hs.card_pos v))) = eventCount s + 1
      exact eventCount_recover (activeAtRank_mem s _)
  | true =>
      change eventCount (infect s (activeAtRank s
        (uniformRank s.active.card hs.card_pos v))) = eventCount s + 1
      exact eventCount_infect s _

/-- An active prescribed prefix has performed exactly one event per step. -/
theorem eventCount_rankState_of_active_prefix (events : ℕ → Bool)
    (s₀ : State) (u : ℕ → ℝ) (k : ℕ)
    (hactive : ∀ j < k, (rankState events s₀ u j).active.Nonempty) :
    eventCount (rankState events s₀ u k) = eventCount s₀ + k := by
  induction k with
  | zero => simp [rankState]
  | succ k ih =>
      have hk := hactive k (by omega)
      have hpre : ∀ j < k, (rankState events s₀ u j).active.Nonempty :=
        fun j hj ↦ hactive j (by omega)
      rw [rankState, eventCount_rankUpdate_of_nonempty _ _ hk _, ih hpre]
      omega

end HeightPaper.Model

namespace HeightPaper.CountCoupling

/-- On an outbreak extinct by the horizon, the explicitly stopped walk time
is exactly the genuine event count of the terminal coupled tree. -/
theorem finiteEarlyExtinctionTime_eq_eventCount_horizon_of_extinct
    {a : ℝ} {n H : ℕ} {q : (ℕ → ℝ) × (ℕ → ℝ)}
    (hs : q.1 ∉ finiteSurvival a n H) :
    finiteEarlyExtinctionTime a n H q.1 =
      Model.eventCount (Model.rankState (finiteBirth a n q.1)
        (Model.initial n) q.2 H) := by
  let T := finiteEarlyExtinctionTime a n H q.1
  obtain ⟨_, hTH, _, hbefore⟩ := finiteEarlyExtinctionTime_spec hs
  have hactive (j : ℕ) (hj : j < T) :
      (Model.rankState (finiteBirth a n q.1) (Model.initial n) q.2 j).active.Nonempty := by
    have hsurvJ : ∀ i ≤ j, 0 < finiteWalk a n q.1 i :=
      fun i hi ↦ hbefore i (hi.trans_lt hj)
    have hcast (i : ℕ) (hi : i ≤ j) :
        (Model.prescribedWalk (finiteBirth a n q.1) 1 i : ℤ) =
          finiteWalk a n q.1 i :=
      prescribedWalk_finite_cast hsurvJ hi
    have hpositive (i : ℕ) (hi : i < j) :
        0 < Model.prescribedWalk (finiteBirth a n q.1) 1 i := by
      have hc := hcast i hi.le
      have hp := hsurvJ i hi.le
      omega
    have hcount := Model.infectious_rankState (finiteBirth a n q.1)
      (Model.initial n) q.2 j hpositive
    simp only [Model.infectious_initial] at hcount
    have hwalk := hcast j le_rfl
    have hp := hsurvJ j le_rfl
    have hpos : 0 < Model.infectious
        (Model.rankState (finiteBirth a n q.1) (Model.initial n) q.2 j) := by
      omega
    exact Finset.card_pos.mp hpos
  have hcount := Model.eventCount_rankState_of_active_prefix
    (finiteBirth a n q.1) (Model.initial n) q.2 T hactive
  simp only [Model.eventCount_initial, zero_add] at hcount
  have hstable := Model.rankState_absorbed_stable
    (finiteBirth a n q.1) (Model.initial n) q.2 hTH
    (finiteEarlyTree_absorbed hs)
  change T = Model.eventCount (Model.rankState (finiteBirth a n q.1)
    (Model.initial n) q.2 H)
  rw [hstable]
  exact hcount.symm

theorem coupledTreeHistory_last_eq_state (a : ℝ) (n H : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) :
    (coupledTreeHistory a n H q).last = coupledTreeState a n q H := by
  simp only [coupledTreeHistory, coupledTreeState, Model.rankHistory,
    Model.trajectoryPrefix_last]

theorem finiteSurvival_iff_coupledTreeHistory_active (a : ℝ) (n H : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) :
    q.1 ∈ finiteSurvival a n H ↔
      0 < Model.infectious (coupledTreeHistory a n H q).last := by
  have hwalk : q.1 ∈ finiteSurvival a n H ↔
      0 < (absorbedCounts a n q.1 H).2 := by
    constructor
    · intro hs
      exact ((finiteWalk_survival_iff a n q.1 H).mp hs) H le_rfl
    · intro hs
      exact (finiteWalk_survival_iff a n q.1 H).mpr
        (fun j hj ↦ absorbedCounts_pos_past a n q.1 hj hs)
  have hc := counts_coupledTreeState a n q H
  have hI : Model.infectious (coupledTreeState a n q H) =
      (absorbedCounts a n q.1 H).2 := by
    simpa only [Model.counts] using congrArg Prod.snd hc
  rw [coupledTreeHistory_last_eq_state, hI]
  exact hwalk

/-- Both finite early coordinates are explicit functions of the terminal
finite path. This is the exact bridge from the coupled construction to the
paper's event-count and height observables at the floored cutoff. -/
theorem finiteEarly_pair_eq_terminalPath (a : ℝ) (n H : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) :
    (finiteEarlyExtinctionTime a n H q.1, finiteEarlyHeight a n H q) =
      (let p := coupledTreeHistory a n H q
       if 0 < Model.infectious p.last then (0, 0)
       else (Model.eventCount p.last, Model.height p.last)) := by
  classical
  let p := coupledTreeHistory a n H q
  have hp := finiteSurvival_iff_coupledTreeHistory_active a n H q
  by_cases hs : q.1 ∈ finiteSurvival a n H
  · have hT := (finiteEarlyExtinctionTime_eq_zero_iff a n H q.1).mpr hs
    have hR := finiteEarlyHeight_zero_of_survival (q := q) hs
    simp [hT, hR, hp.mp hs]
  · have hT := finiteEarlyExtinctionTime_eq_eventCount_horizon_of_extinct hs
    have hR := finiteEarlyHeight_eq_horizon_of_extinct hs
    have hdead : ¬(0 < Model.infectious p.last) :=
      fun h ↦ hs (hp.mpr (by simpa only [p] using h))
    simp only [p, ite_eq_right hdead]
    rw [coupledTreeHistory_last_eq_state]
    exact Prod.ext hT hR

/-- The source-side stopped event count and tree height at a fixed finite
horizon, recorded as a single terminal-path observable. -/
noncomputable def earlyTerminalPair {H : ℕ} (p : Model.FinitePath H) : ℕ × ℕ :=
  if 0 < Model.infectious p.last then (0, 0)
  else (Model.eventCount p.last, Model.height p.last)

/-- Exact joint law of the early pair under the common uniforms and the
original epidemic finite-path law. -/
theorem finiteEarly_pair_law (a : ℝ≥0) (n H : ℕ) :
    birthParentLaw.map (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      (finiteEarlyExtinctionTime a n H q.1, finiteEarlyHeight a n H q)) =
      (Model.pathMeasure (a / n) n H).map (earlyTerminalPair (H := H)) := by
  have heq : (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      (finiteEarlyExtinctionTime a n H q.1, finiteEarlyHeight a n H q)) =
      earlyTerminalPair ∘ coupledTreeHistory a n H := by
    funext q
    exact finiteEarly_pair_eq_terminalPath (a : ℝ) n H q
  rw [heq, ← Measure.map_map (Model.FinitePath.measurable earlyTerminalPair)
    (measurable_coupledTreeHistory a n H), coupledTreeHistory_law]

/-- The paper's early terminal event-count and height pair converges in law at
every floored preterminal horizon. The conclusion is setwise convergence on
the countable pair space, obtained from a stronger common-space coupling. -/
theorem earlyTerminalPair_event_probability_tendsto
    (rates : ℕ → ℝ≥0) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (B : Set (ℕ × ℕ)) :
    Tendsto (fun n ↦
      (Model.pathMeasure (rates n) n ⌊T * n⌋₊).real
        (earlyTerminalPair ⁻¹' B)) atTop
      (𝓝 (birthParentLaw.real {q |
        (localEarlyExtinctionTime l q.1, localEarlyHeight l q) ∈ B})) := by
  let F : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ × ℕ := fun n q ↦
    (finiteEarlyExtinctionTime ((rates n : ℝ) * n) n ⌊T * n⌋₊ q.1,
      finiteEarlyHeight ((rates n : ℝ) * n) n ⌊T * n⌋₊ q)
  let G : ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ × ℕ := fun q ↦
    (localEarlyExtinctionTime l q.1, localEarlyHeight l q)
  have hG : Measurable G :=
    ((measurable_localEarlyExtinctionTime l).comp measurable_fst).prodMk
      (measurable_localEarlyHeight l)
  have hF (n : ℕ) : Measurable (F n) :=
    ((measurable_finiteEarlyExtinctionTime ((rates n : ℝ) * n) n ⌊T * n⌋₊).comp
      measurable_fst).prodMk
      (measurable_finiteEarlyHeight ((rates n : ℝ) * n) n ⌊T * n⌋₊)
  have hB : MeasurableSet B := (Set.to_countable B).measurableSet
  have hcoupled := finiteEarly_joint_disagreement_tendsto_zero rates hl hT hrates
  have hdiff : Tendsto (fun n ↦
      |birthParentLaw.real (F n ⁻¹' B) - birthParentLaw.real (G ⁻¹' B)|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hcoupled
    apply Eventually.of_forall
    intro n
    have hsub : (F n ⁻¹' B) ∆ (G ⁻¹' B) ⊆
        {q | finiteEarlyExtinctionTime ((rates n : ℝ) * n) n ⌊T * n⌋₊ q.1 ≠
            localEarlyExtinctionTime l q.1 ∨
          finiteEarlyHeight ((rates n : ℝ) * n) n ⌊T * n⌋₊ q ≠
            localEarlyHeight l q} := by
      intro q hq
      have hpair : F n q ≠ G q := by
        intro he
        simp only [mem_symmDiff, mem_preimage] at hq
        rw [he] at hq
        tauto
      simpa only [mem_ofPred_eq, F, G, ne_eq, Prod.mk.injEq, not_and_or] using hpair
    have hfirst := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := birthParentLaw)
      ((hF n) hB).nullMeasurableSet (hG hB).nullMeasurableSet
    exact hfirst.trans (measureReal_mono hsub (measure_ne_top _ _))
  have hzero : Tendsto (fun n ↦
      birthParentLaw.real (F n ⁻¹' B) - birthParentLaw.real (G ⁻¹' B))
      atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr hdiff
  have hmass : Tendsto (fun n ↦ birthParentLaw.real (F n ⁻¹' B))
      atTop (𝓝 (birthParentLaw.real (G ⁻¹' B))) := by
    have hh := hzero.add_const (birthParentLaw.real (G ⁻¹' B))
    simpa only [zero_add, sub_add_cancel] using hh
  apply hmass.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  let a : ℝ≥0 := rates n * n
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hrate : a / n = rates n := by
    dsimp [a]
    field_simp [hn0]
  have hLaw := congrArg (fun μ : Measure (ℕ × ℕ) ↦ μ.real B)
    (finiteEarly_pair_law a n ⌊T * n⌋₊)
  rw [hrate] at hLaw
  simp only [a, NNReal.coe_mul, NNReal.coe_natCast] at hLaw
  change (birthParentLaw.map (F n)).real B =
    ((Model.pathMeasure (rates n) n ⌊T * n⌋₊).map earlyTerminalPair).real B at hLaw
  change ENNReal.toReal ((birthParentLaw.map (F n)) B) =
    ENNReal.toReal (((Model.pathMeasure (rates n) n ⌊T * n⌋₊).map
      earlyTerminalPair) B) at hLaw
  rw [Measure.map_apply (hF n) hB,
    Measure.map_apply (Model.FinitePath.measurable earlyTerminalPair) hB] at hLaw
  simpa only [Measure.real, Set.preimage, F, G] using hLaw

/-- Survival immediately before the source's floored cutoff agrees with the
infinite local survival indicator. The one-event shift is proved through the
finite marginal limit and nesting of the two survival events. -/
theorem sourceCutoff_minus_one_survival_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ uniformLaw.real
      (finiteSurvival ((rates n : ℝ) * n) n
        (Model.sourceCutoff l δ n - 1) ∆ localSurvival l)) atTop (𝓝 0) := by
  let T : ℝ := (1 - δ) * fluidExtinctionTime l
  have hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l) := by
    dsimp [T]
    have ht := fluidExtinctionTime_pos hl
    constructor
    · exact mul_pos (sub_pos.mpr hδ.2) ht
    · nlinarith [mul_pos hδ.1 ht]
  have hfloor : Tendsto (fun n : ℕ ↦
      (Model.sourceCutoff l δ n : ℝ) / n) atTop (𝓝 T) := by
    simpa only [Model.sourceCutoff, T] using tendsto_floor_fraction hT.1.le
  have hminus : Tendsto (fun n : ℕ ↦
      ((Model.sourceCutoff l δ n - 1 : ℕ) : ℝ) / n) atTop (𝓝 T) := by
    have hh := hfloor.sub (tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [Model.sourceCutoff_pos_eventually hl hδ] with n hn
    rw [Nat.cast_sub (by omega : 1 ≤ Model.sourceCutoff l δ n),
      Nat.cast_one, sub_div]
  have hprobMinus := finiteSurvival_rateSequence_horizon_probability_tendsto
    rates (fun n ↦ Model.sourceCutoff l δ n - 1) hl hT hrates hminus
  have hprobFloor : Tendsto (fun n ↦ uniformLaw.real
      (finiteSurvival ((rates n : ℝ) * n) n (Model.sourceCutoff l δ n)))
      atTop (𝓝 (1 - 1 / l)) := by
    simpa only [Model.sourceCutoff, T] using
      finiteSurvival_rateSequence_floor_probability_tendsto rates hl hT hrates
  have hdiff := (hprobMinus.sub hprobFloor).abs
  simp only [sub_self, abs_zero] at hdiff
  have hshift : Tendsto (fun n ↦ uniformLaw.real
      (finiteSurvival ((rates n : ℝ) * n) n (Model.sourceCutoff l δ n - 1) ∆
        finiteSurvival ((rates n : ℝ) * n) n (Model.sourceCutoff l δ n)))
      atTop (𝓝 0) := by
    apply hdiff.congr'
    apply Eventually.of_forall
    intro n
    have hsub : finiteSurvival ((rates n : ℝ) * n) n (Model.sourceCutoff l δ n) ⊆
        finiteSurvival ((rates n : ℝ) * n) n (Model.sourceCutoff l δ n - 1) := by
      intro u hu j hj
      exact hu j (hj.trans (Nat.sub_le _ _))
    exact (measureReal_symmDiff_eq_abs_sub_of_comparable uniformLaw
      (measurableSet_finiteSurvival _ _ _)
      (measurableSet_finiteSurvival _ _ _) (Or.inr hsub)).symm
  have hlocal : Tendsto (fun n ↦ uniformLaw.real
      (finiteSurvival ((rates n : ℝ) * n) n (Model.sourceCutoff l δ n) ∆
        localSurvival l)) atTop (𝓝 0) := by
    simpa only [Model.sourceCutoff, T] using
      finiteSurvival_rateSequence_local_disagreement_tendsto_zero
        rates hl hT hrates
  have hsum := hshift.add hlocal
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro n
  exact measureReal_symmDiff_le (μ := uniformLaw)
    (s := finiteSurvival ((rates n : ℝ) * n) n (Model.sourceCutoff l δ n - 1))
    (t := finiteSurvival ((rates n : ℝ) * n) n (Model.sourceCutoff l δ n))
    (localSurvival l) (by finiteness) (by finiteness)

/-- The source's terminal-state survival event is almost surely the same as
the common-uniform finite walk surviving through the event just before its
integer cutoff. -/
theorem sourceSurvivalEvent_iff_finiteSurvival_ae
    (a : ℝ≥0) (n : ℕ) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hcut : 0 < Model.sourceCutoff l δ n) :
    ∀ᵐ q ∂birthParentLaw,
      ((coupledTreeHistory a n (2 * n + 1) q).last ∈
          Model.sourceSurvivalEvent l δ n ↔
        q.1 ∈ finiteSurvival a n (Model.sourceCutoff l δ n - 1)) := by
  let N := 2 * n + 1
  let H := Model.sourceCutoff l δ n - 1
  have hHN : H ≤ N := by
    dsimp [H, N]
    have hh := Model.sourceCutoff_le_steps hl hδ n
    omega
  have hpath : ∀ᵐ p ∂birthParentLaw.map (coupledTreeHistory a n N),
      Model.SupportedPath (a / n) n N p.eval := by
    rw [coupledTreeHistory_law]
    exact Model.ae_supportedPath (a / n) n N
  have hcommon := ae_of_ae_map (measurable_coupledTreeHistory a n N).aemeasurable hpath
  filter_upwards [hcommon] with q hp
  let p := coupledTreeHistory a n N q
  have hsource := Model.sourceSurvivalEvent_iff_active hl hδ hp hcut
  have heval : p.eval H = (coupledTreeHistory a n H q).last := by
    dsimp [p]
    simp only [coupledTreeHistory, Model.rankHistory,
      Model.trajectoryPrefix_eval N _ H hHN, Model.trajectoryPrefix_last]
  have hactive : (p.eval H).active.Nonempty ↔
      0 < Model.infectious (coupledTreeHistory a n H q).last := by
    rw [heval]
    change (coupledTreeHistory a n H q).last.active.Nonempty ↔
      0 < (coupledTreeHistory a n H q).last.active.card
    exact Finset.card_pos.symm
  have hfinite := finiteSurvival_iff_coupledTreeHistory_active a n H q
  simpa only [p, N, H, Model.FinitePath.eval_last] using
    hsource.trans (hactive.trans hfinite.symm)

/-- Under the exact common-uniform coupling, the source's terminal survival
event becomes the infinite local survival event with probability tending to
one. -/
theorem sourceSurvivalEvent_localSurvival_disagreement_tendsto_zero
    (rates : ℕ → ℝ≥0) {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l)) :
    Tendsto (fun n ↦ birthParentLaw.real {q |
      ¬ ((coupledTreeHistory (rates n * n) n (2 * n + 1) q).last ∈
          Model.sourceSurvivalEvent l δ n ↔ q.1 ∈ localSurvival l)})
      atTop (𝓝 0) := by
  have hfinite := sourceCutoff_minus_one_survival_disagreement_tendsto_zero
    rates hl hδ hrates
  apply hfinite.congr'
  filter_upwards [Model.sourceCutoff_pos_eventually hl hδ] with n hcut
  let a : ℝ≥0 := rates n * n
  let H := Model.sourceCutoff l δ n - 1
  let S : Set (ℕ → ℝ) := finiteSurvival a n H ∆ localSurvival l
  have hS : MeasurableSet S :=
    (measurableSet_finiteSurvival a n H).symmDiff (measurableSet_localSurvival l)
  have hAE := sourceSurvivalEvent_iff_finiteSurvival_ae a n hl hδ hcut
  symm
  calc
    birthParentLaw.real {q |
      ¬ ((coupledTreeHistory (rates n * n) n (2 * n + 1) q).last ∈
          Model.sourceSurvivalEvent l δ n ↔ q.1 ∈ localSurvival l)} =
      birthParentLaw.real {q |
        ¬ (q.1 ∈ finiteSurvival a n H ↔ q.1 ∈ localSurvival l)} := by
        apply measureReal_congr
        filter_upwards [hAE] with q hq
        simp only [a, H, NNReal.coe_mul, NNReal.coe_natCast] at hq ⊢
        rw [hq]
    _ = birthParentLaw.real (Prod.fst ⁻¹' S) := by
      congr 1
      ext q
      simp only [S, mem_ofPred_eq, mem_preimage, mem_symmDiff]
      tauto
    _ = uniformLaw.real S := by
      rw [← birthParentLaw_map_fst]
      simp only [Measure.real, Measure.map_apply measurable_fst hS]
    _ = uniformLaw.real
        (finiteSurvival ((rates n : ℝ) * n) n
          (Model.sourceCutoff l δ n - 1) ∆ localSurvival l) := by
      simp only [S, H, a, NNReal.coe_mul, NNReal.coe_natCast]

end HeightPaper.CountCoupling
