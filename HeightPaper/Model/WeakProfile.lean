module

public import HeightPaper.Probability.ProfileInProbability
public import HeightPaper.Model.Profile
public import HeightPaper.Model.StateMeasure
public import HeightPaper.Analysis.Parameters

/-!
# The actual active profile and its real-Laplace proof boundary

Finite bin counts and tail counts are tied to the infection-tree state.
The transfer theorem below supplies the weak profile estimate from explicit
real Laplace asymptotics on the active event. Those asymptotics are proved
separately in `Probability/EpidemicLaplace.lean` and supplied in the main proof.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology NNReal BigOperators

namespace HeightPaper.Model

noncomputable def activeBinCount (s : State) (a b : ℝ) : ℕ := by
  classical
  exact (s.active.filter fun v ↦ a ≤ (s.tree.depth v : ℝ) ∧ (s.tree.depth v : ℝ) ≤ b).card

noncomputable def activeTailCount (s : State) (a : ℝ) : ℕ := by
  classical
  exact (s.active.filter fun v ↦ a ≤ (s.tree.depth v : ℝ)).card

theorem binMass_active_eq (s : State) (a b : ℝ) :
    Profile.binMass s.active (fun _ ↦ (1 : ℝ)) (fun v ↦ (s.tree.depth v : ℝ)) a b =
      (activeBinCount s a b : ℝ) := by
  classical
  unfold Profile.binMass activeBinCount
  rw [← Finset.sum_filter]
  simp

theorem tailMass_active_eq (s : State) (a : ℝ) :
    Profile.tailMass s.active (fun _ ↦ (1 : ℝ)) (fun v ↦ (s.tree.depth v : ℝ)) a =
      (activeTailCount s a : ℝ) := by
  classical
  unfold Profile.tailMass activeTailCount
  rw [← Finset.sum_filter]
  simp

theorem laplaceSum_active_eq (s : State) (x : ℝ) :
    Profile.laplaceSum s.active (fun _ ↦ (1 : ℝ)) (fun v ↦ (s.tree.depth v : ℝ)) x =
      activeWeight (Real.exp x) s := by
  unfold Profile.laplaceSum activeWeight
  apply Finset.sum_congr rfl
  intro v _
  simp only [one_mul, mul_comm x, Real.exp_nat_mul]

theorem activeWeight_exp_pos (s : State) (h : s.active.Nonempty) (x : ℝ) :
    0 < activeWeight (Real.exp x) s := by
  exact Finset.sum_pos (fun v _ ↦ pow_pos (Real.exp_pos x) _) h

/-- The actual state law restricted to nonextinction. Its mass is the survival
probability, so no division by a possibly small survival probability is used. -/
noncomputable def activeStateMeasure (rate : ℝ≥0) (n k : ℕ) : Measure State :=
  (evolve rate n k).toMeasure.restrict {s | s.active.Nonempty}

instance (rate : ℝ≥0) (n k : ℕ) : IsFiniteMeasure (activeStateMeasure rate n k) := by
  unfold activeStateMeasure
  infer_instance

theorem activeStateMeasure_real_apply (rate : ℝ≥0) (n k : ℕ) (A : Set State) :
    (activeStateMeasure rate n k).real A =
      (evolve rate n k).toMeasure.real {s | s.active.Nonempty ∧ s ∈ A} := by
  rw [measureReal_def, activeStateMeasure, Measure.restrict_apply (show MeasurableSet A from trivial)]
  congr 2
  ext s
  simp only [mem_inter_iff, mem_ofPred_eq, and_comm]

/-- The finite-upper-endpoint weak profile estimate for the actual SIR state
follows from its real Laplace estimate on the active event. -/
theorem activeBinCount_log_convergence_of_laplace
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l x y : ℝ} (hl : 1 < l)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (hxy : x < y)
    (hLap : ∀ t ∈ Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp t) s) / Real.log n -
          (1 + growthFactor l * (Real.exp t - 1))|}) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s |
      s.active.Nonempty ∧ ε ≤ |Real.log (activeBinCount s
        (growthFactor l * Real.exp x * Real.log n) (growthFactor l * Real.exp y * Real.log n)) /
        Real.log n - profileExponent l x|}) atTop (𝓝 0) := by
  let μ : ℕ → Measure State := fun n ↦ activeStateMeasure (rates n) n (horizon n)
  let S : (i : Σ _ : ℕ, State) → Finset (Fin i.2.vertices) := fun i ↦ i.2.active
  let w : (i : Σ _ : ℕ, State) → Fin i.2.vertices → ℝ := fun _ _ ↦ 1
  let d : (i : Σ _ : ℕ, State) → Fin i.2.vertices → ℝ := fun i v ↦ i.2.tree.depth v
  have hZ : ∀ t ∈ Ioo (0 : ℝ) (profileRoot l), Tendsto (fun n ↦ (μ n).real
      {s | Profile.laplaceSum (S ⟨n, s⟩) (w ⟨n, s⟩) (d ⟨n, s⟩) t ≤ 0}) atTop (𝓝 0) := by
    intro t _
    have hz (n : ℕ) : (μ n).real
        {s | Profile.laplaceSum (S ⟨n, s⟩) (w ⟨n, s⟩) (d ⟨n, s⟩) t ≤ 0} = 0 := by
      rw [show μ n = activeStateMeasure (rates n) n (horizon n) from rfl,
        activeStateMeasure_real_apply]
      have heq : {s : State | s.active.Nonempty ∧
          Profile.laplaceSum (S ⟨n, s⟩) (w ⟨n, s⟩) (d ⟨n, s⟩) t ≤ 0} = ∅ := by
        ext s
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hs
        change ¬Profile.laplaceSum s.active (fun _ ↦ 1) (fun v ↦ (s.tree.depth v : ℝ)) t ≤ 0
        rw [laplaceSum_active_eq]
        exact not_le_of_gt (activeWeight_exp_pos s hs t)
      simp only [Set.mem_ofPred_eq]
      rw [heq, measureReal_empty]
    simpa only [hz] using (tendsto_const_nhds (x := (0 : ℝ)) (f := (atTop : Filter ℕ)))
  have hconv : ∀ t ∈ Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (μ n).real {s | ε ≤
        |Real.log (Profile.laplaceSum (S ⟨n, s⟩) (w ⟨n, s⟩) (d ⟨n, s⟩) t) / Real.log n -
          (1 + growthFactor l * (Real.exp t - 1))|}) atTop (𝓝 0) := by
    intro t ht ε hε
    simpa only [μ, activeStateMeasure_real_apply, S, w, d, laplaceSum_active_eq,
      Set.mem_ofPred_eq] using hLap t ht ε hε
  have hh := Profile.log_binMass_convergence_in_probability μ S w d
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) (fun _ _ _ ↦ zero_le_one)
    (growthFactor_pos hl) hx.1.le
    (mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hxy) (growthFactor_pos hl))
    isOpen_Ioo hx hZ hconv
  intro ε hε
  simpa only [μ, activeStateMeasure_real_apply, S, w, d, binMass_active_eq, profileExponent,
    Set.mem_ofPred_eq, Function.comp_apply]
    using hh.2 ε hε

/-- The infinite-upper-endpoint weak profile estimate has the same exponent
and follows from the same real Laplace input. -/
theorem activeTailCount_log_convergence_of_laplace
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l x : ℝ} (hl : 1 < l)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l))
    (hLap : ∀ t ∈ Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp t) s) / Real.log n -
          (1 + growthFactor l * (Real.exp t - 1))|}) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s |
      s.active.Nonempty ∧ ε ≤ |Real.log (activeTailCount s (growthFactor l * Real.exp x * Real.log n)) /
        Real.log n - profileExponent l x|}) atTop (𝓝 0) := by
  let μ : ℕ → Measure State := fun n ↦ activeStateMeasure (rates n) n (horizon n)
  let S : (i : Σ _ : ℕ, State) → Finset (Fin i.2.vertices) := fun i ↦ i.2.active
  let w : (i : Σ _ : ℕ, State) → Fin i.2.vertices → ℝ := fun _ _ ↦ 1
  let d : (i : Σ _ : ℕ, State) → Fin i.2.vertices → ℝ := fun i v ↦ i.2.tree.depth v
  have hZ : ∀ t ∈ Ioo (0 : ℝ) (profileRoot l), Tendsto (fun n ↦ (μ n).real
      {s | Profile.laplaceSum (S ⟨n, s⟩) (w ⟨n, s⟩) (d ⟨n, s⟩) t ≤ 0}) atTop (𝓝 0) := by
    intro t _
    have hz (n : ℕ) : (μ n).real
        {s | Profile.laplaceSum (S ⟨n, s⟩) (w ⟨n, s⟩) (d ⟨n, s⟩) t ≤ 0} = 0 := by
      rw [show μ n = activeStateMeasure (rates n) n (horizon n) from rfl,
        activeStateMeasure_real_apply]
      have heq : {s : State | s.active.Nonempty ∧
          Profile.laplaceSum (S ⟨n, s⟩) (w ⟨n, s⟩) (d ⟨n, s⟩) t ≤ 0} = ∅ := by
        ext s
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hs
        change ¬Profile.laplaceSum s.active (fun _ ↦ 1) (fun v ↦ (s.tree.depth v : ℝ)) t ≤ 0
        rw [laplaceSum_active_eq]
        exact not_le_of_gt (activeWeight_exp_pos s hs t)
      simp only [Set.mem_ofPred_eq]
      rw [heq, measureReal_empty]
    simpa only [hz] using (tendsto_const_nhds (x := (0 : ℝ)) (f := (atTop : Filter ℕ)))
  have hconv : ∀ t ∈ Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (μ n).real {s | ε ≤
        |Real.log (Profile.laplaceSum (S ⟨n, s⟩) (w ⟨n, s⟩) (d ⟨n, s⟩) t) / Real.log n -
          (1 + growthFactor l * (Real.exp t - 1))|}) atTop (𝓝 0) := by
    intro t ht ε hε
    simpa only [μ, activeStateMeasure_real_apply, S, w, d, laplaceSum_active_eq,
      Set.mem_ofPred_eq] using hLap t ht ε hε
  have hh := Profile.log_tailMass_convergence_in_probability μ S w d
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) (fun _ _ _ ↦ zero_le_one)
    (growthFactor_pos hl) hx.1.le
    isOpen_Ioo hx hZ hconv
  intro ε hε
  simpa only [μ, activeStateMeasure_real_apply, S, w, d, tailMass_active_eq, profileExponent,
    Set.mem_ofPred_eq, Function.comp_apply]
    using hh.2 ε hε


end HeightPaper.Model
