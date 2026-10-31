module

public import HeightPaper.Model.UniformParent
public import HeightPaper.Model.KernelTrajectoryPrefix
public import HeightPaper.Model.InfiniteProfile
public import HeightPaper.Probability.CountCouplingLaw
public import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Exact tree-history law of the independent uniform parent construction

For each deterministic event word, fresh independent uniforms select the
increasing ranks of the active labels.  Both complete finite histories and the
infinite trajectory have the prescribed uniform-parent kernel law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HeightPaper.Model

open HeightPaper.CountCoupling

theorem uniformRank_probability (m : ℕ) (hm : 0 < m) (k : ℕ) (r : Fin m) :
    uniformLaw {u | uniformRank m hm (u k) = r} = (m : ℝ≥0∞)⁻¹ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    _ = uniformLaw {u | (r.val : ℝ) / m < u k ∧ u k ≤ (r.val + 1 : ℝ) / m} := by
      apply measure_congr
      filter_upwards [uniformLaw_ae_pos, uniformLaw_ae_le_one] with u hu hu1
      exact propext (uniformRank_eq_iff hm (hu k) (hu1 k) r)
    _ = ENNReal.ofReal ((r.val + 1 : ℝ) / m - r.val / m) :=
      uniformLaw_interval k (div_nonneg (Nat.cast_nonneg _) hmR.le)
        ((div_le_one hmR).mpr (by exact_mod_cast (Nat.succ_le_iff.mpr r.isLt)))
    _ = (m : ℝ≥0∞)⁻¹ := by
      rw [← sub_div, add_sub_cancel_left, one_div, ENNReal.ofReal_inv_of_pos hmR]
      simp

/-- The ordered-rank selection has exactly the existing uniform-active law. -/
theorem activeAtRank_uniform_law (s : State) (hs : s.active.Nonempty) (k : ℕ) :
    uniformLaw.map (fun u ↦ activeAtRank s (uniformRank _ hs.card_pos (u k))) =
      (uniformActive s hs).toMeasure := by
  classical
  have hm : Measurable (fun u : ℕ → ℝ ↦ activeAtRank s (uniformRank _ hs.card_pos (u k))) :=
    (measurable_of_countable (activeAtRank s)).comp
      ((measurable_uniformRank _ _).comp (measurable_pi_apply k))
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply hm (measurableSet_singleton v),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton v), uniformActive_apply]
  by_cases hv : v ∈ s.active
  · obtain ⟨r, rfl⟩ := (show v ∈ Set.range (activeAtRank s) by rw [activeAtRank_range]; exact hv)
    simp only [ite_eq_left (activeAtRank_mem s r)]
    have he : {u : ℕ → ℝ | activeAtRank s (uniformRank _ hs.card_pos (u k)) = activeAtRank s r} =
        {u | uniformRank _ hs.card_pos (u k) = r} := by
      ext u
      exact (activeAtRank_injective s).eq_iff
    change uniformLaw {u | activeAtRank s (uniformRank _ hs.card_pos (u k)) = activeAtRank s r} = _
    rw [he]
    exact uniformRank_probability _ hs.card_pos k r
  · rw [ite_eq_right hv]
    have he : (fun u : ℕ → ℝ ↦ activeAtRank s (uniformRank _ hs.card_pos (u k))) ⁻¹' {v} = ∅ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hu
      exact hv (hu ▸ activeAtRank_mem s _)
    rw [he, measure_empty]

theorem rankUpdate_law (birth : Bool) (s : State) (k : ℕ) :
    uniformLaw.map (fun u ↦ rankUpdate birth s (u k)) = (prescribedStep birth s).toMeasure := by
  classical
  by_cases hs : s.active.Nonempty
  · simp only [rankUpdate, prescribedStep, dite_eq_left hs]
    have hm : Measurable (fun u : ℕ → ℝ ↦ activeAtRank s (uniformRank _ hs.card_pos (u k))) :=
      (measurable_of_countable (activeAtRank s)).comp
        ((measurable_uniformRank _ _).comp (measurable_pi_apply k))
    rw [show (fun u : ℕ → ℝ ↦ prescribedUpdate birth s
        (activeAtRank s (uniformRank _ hs.card_pos (u k)))) =
        prescribedUpdate birth s ∘ (fun u ↦ activeAtRank s (uniformRank _ hs.card_pos (u k))) from rfl,
      ← Measure.map_map (measurable_of_countable (prescribedUpdate birth s)) hm,
      activeAtRank_uniform_law, PMF.toMeasure_map _ _ (measurable_of_countable _)]
  · simp [rankUpdate, prescribedStep, hs, PMF.toMeasure_pure]

theorem measurable_rankState (events : ℕ → Bool) (s₀ : State) (k : ℕ) :
    Measurable (fun u ↦ rankState events s₀ u k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      have hm : Measurable (fun p : State × ℝ ↦ rankUpdate (events k) p.1 p.2) :=
        measurable_from_prod_countable_right (fun s ↦ measurable_rankUpdate (events k) s)
      exact hm.comp (ih.prodMk (measurable_pi_apply k))

theorem measurable_rankTrajectory (events : ℕ → Bool) (s₀ : State) :
    Measurable (rankState events s₀) :=
  measurable_pi_iff.mpr (measurable_rankState events s₀)

noncomputable def rankHistory (events : ℕ → Bool) (s₀ : State) (k : ℕ) (u : ℕ → ℝ) :
    FinitePath k := trajectoryPrefix k (rankState events s₀ u)

theorem measurable_rankHistory (events : ℕ → Bool) (s₀ : State) (k : ℕ) :
    Measurable (rankHistory events s₀ k) :=
  (measurable_trajectoryPrefix k).comp (measurable_rankTrajectory events s₀)

theorem rankHistory_indep_next (events : ℕ → Bool) (s₀ : State) (k : ℕ) :
    IndepFun (rankHistory events s₀ k) (fun u ↦ u k) uniformLaw := by
  have hind := uniformLaw_independent.indepFun_set (Set.Iio k) {k}
    (by
      apply Set.disjoint_left.mpr
      intro a ha hb
      simp only [Set.mem_Iio, Set.mem_singleton_iff] at ha hb
      omega) (fun i ↦ measurable_pi_apply i)
  have hh := hind.comp
    ((measurable_rankHistory events s₀ k).comp (measurable_extendPast k))
    (measurable_pi_apply (⟨k, by simp⟩ : ({k} : Set ℕ)))
  have heq : (rankHistory events s₀ k ∘ extendPast k) ∘
      (fun (u : ℕ → ℝ) (i : Set.Iio k) ↦ u i) = rankHistory events s₀ k := by
    funext u
    apply FinitePath.ext
    intro i
    apply rankState_congr_prefix
    intro j hj
    have hjk : j < k := by have := i.isLt; omega
    simp [extendPast, hjk]
  rw [heq] at hh
  exact hh

theorem rankHistory_succ (events : ℕ → Bool) (s₀ : State) (k : ℕ) (u : ℕ → ℝ) :
    rankHistory events s₀ (k + 1) u =
      (rankHistory events s₀ k u).append
        (rankUpdate (events k) (rankHistory events s₀ k u).last (u k)) :=
  trajectoryPrefix_succ k (rankState events s₀ u)

/-- Equality of complete finite-history laws, with the absorbing convention
valid even for prescribed words that reach zero. -/
theorem rankHistory_law (events : ℕ → Bool) (s₀ : State) (k : ℕ) :
    uniformLaw.map (rankHistory events s₀ k) =
      kernelPathMeasure (fun j ↦ prescribedStep (events j)) s₀ k := by
  induction k with
  | zero =>
      have he : rankHistory events s₀ 0 = fun _ ↦ (⟨fun _ ↦ s₀⟩ : FinitePath 0) := by
        funext u
        apply FinitePath.ext
        intro i
        simp [rankHistory, trajectoryPrefix, rankState]
      rw [he, kernelPathMeasure, kernelPathLaw, PMF.toMeasure_pure]
      simp
  | succ k ih =>
      have he : rankHistory events s₀ (k + 1) = fun u ↦
          (rankHistory events s₀ k u).append
            (rankUpdate (events k) (rankHistory events s₀ k u).last (u k)) :=
        funext (rankHistory_succ events s₀ k)
      rw [he, kernelPathMeasure, kernelPathLaw]
      refine uniform_independent_update (rankHistory events s₀ k) k
        (fun (p : FinitePath k) v ↦ p.append (rankUpdate (events k) p.last v))
        (kernelPathLaw (fun j ↦ prescribedStep (events j)) s₀ k)
        (fun p ↦ (prescribedStep (events k) p.last).map p.append)
        (measurable_rankHistory events s₀ k) ?_ ?_ (rankHistory_indep_next events s₀ k) ih ?_
      · intro p
        exact (measurable_of_countable p.append).comp (measurable_rankUpdate _ _)
      · rw [← he]
        exact measurable_rankHistory events s₀ (k + 1)
      · intro p
        have hm : Measurable (fun u : ℕ → ℝ ↦ rankUpdate (events k) p.last (u k)) :=
          (measurable_rankUpdate _ _).comp (measurable_pi_apply k)
        rw [show (fun u : ℕ → ℝ ↦ p.append (rankUpdate (events k) p.last (u k))) =
            p.append ∘ (fun u ↦ rankUpdate (events k) p.last (u k)) from rfl,
          ← Measure.map_map (measurable_of_countable p.append) hm, rankUpdate_law,
          PMF.toMeasure_map _ _ (measurable_of_countable p.append)]

/-- Full infinite-path distribution, not merely separate one-time marginals. -/
theorem rankTrajectory_law (events : ℕ → Bool) (s₀ : State) :
    uniformLaw.map (rankState events s₀) = prescribedTrajectoryMeasure events s₀ := by
  classical
  let μ := prescribedTrajectoryMeasure events s₀
  apply IsProjectiveLimit.unique (P := fun I : Finset ℕ ↦ μ.map I.restrict) ?_ (fun _ ↦ rfl)
  intro I
  change (uniformLaw.map (rankState events s₀)).map I.restrict = μ.map I.restrict
  let N := I.sup id
  let f : FinitePath N → (I → State) := fun p i ↦ p.eval i.val
  have hf : Measurable f := measurable_of_countable _
  have he : I.restrict = f ∘ trajectoryPrefix N := by
    funext ω i
    exact (trajectoryPrefix_eval N ω i.val (Finset.le_sup (f := id) i.property)).symm
  have hprefix : (uniformLaw.map (rankState events s₀)).map (trajectoryPrefix N) =
      μ.map (trajectoryPrefix N) := by
    rw [Measure.map_map (measurable_trajectoryPrefix N) (measurable_rankTrajectory events s₀)]
    change uniformLaw.map (rankHistory events s₀ N) = μ.map (trajectoryPrefix N)
    rw [rankHistory_law]
    exact (kernelTrajectoryMeasure_map_prefix (fun j ↦ prescribedStep (events j)) s₀ N).symm
  rw [he, ← Measure.map_map hf (measurable_trajectoryPrefix N),
    ← Measure.map_map hf (measurable_trajectoryPrefix N), hprefix]

/-- Before any tree is sampled, prescribed positive counts fix the cardinality
of each uniform rank.  Independence follows from coordinatewise dependence. -/
theorem measurable_prescribedRanks (events : ℕ → Bool) (i₀ k : ℕ) :
    Measurable (fun u ↦ prescribedRanks events i₀ u k) := by
  exact (measurable_of_countable (fun a : ℕ ↦ min (a - 1)
    (prescribedWalk events i₀ k - 1))).comp
      (Nat.measurable_ceil.comp ((measurable_pi_apply k).const_mul _))

theorem prescribedRanks_independent (events : ℕ → Bool) (i₀ : ℕ) :
    iIndepFun (fun k u ↦ prescribedRanks events i₀ u k) uniformLaw := by
  apply uniformLaw_independent.comp
    (fun k v ↦ min (Nat.ceil ((prescribedWalk events i₀ k : ℝ) * v) - 1)
      (prescribedWalk events i₀ k - 1))
  intro k
  exact (measurable_of_countable (fun a : ℕ ↦ min (a - 1)
    (prescribedWalk events i₀ k - 1))).comp
      (Nat.measurable_ceil.comp (measurable_id.const_mul _))

end HeightPaper.Model
