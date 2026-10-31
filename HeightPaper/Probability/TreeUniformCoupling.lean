module

public import HeightPaper.Probability.UniformParentLaw

/-!
# Separate count and parent uniforms

The two independent uniform sequences in the source live on their product
space.  The tree construction is jointly measurable in its entire event word
and parent sequence, and equal event prefixes produce identical tree histories.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.Model

theorem rankState_congr_events_prefix {events events' : ℕ → Bool} (s₀ : State)
    (u : ℕ → ℝ) (k : ℕ) (he : ∀ i < k, events i = events' i) :
    rankState events s₀ u k = rankState events' s₀ u k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [rankState, rankState, he k (by omega), ih (fun i hi ↦ he i (by omega))]

theorem rankHistory_congr_events_prefix {events events' : ℕ → Bool} (s₀ : State)
    (u : ℕ → ℝ) (k : ℕ) (he : ∀ i < k, events i = events' i) :
    rankHistory events s₀ k u = rankHistory events' s₀ k u := by
  apply FinitePath.ext
  intro i
  exact rankState_congr_events_prefix s₀ u i.val
    (fun j hj ↦ he j (by have := i.isLt; omega))

theorem measurable_rankState_joint (s₀ : State) (k : ℕ) :
    Measurable (fun q : (ℕ → Bool) × (ℕ → ℝ) ↦ rankState q.1 s₀ q.2 k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      have hm : Measurable (fun p : (Bool × State) × ℝ ↦ rankUpdate p.1.1 p.1.2 p.2) :=
        measurable_from_prod_countable_right (fun p ↦ measurable_rankUpdate p.1 p.2)
      exact hm.comp ((((measurable_pi_apply k).comp measurable_fst).prodMk ih).prodMk
        ((measurable_pi_apply k).comp measurable_snd))

theorem measurable_rankTrajectory_joint (s₀ : State) :
    Measurable (fun q : (ℕ → Bool) × (ℕ → ℝ) ↦ rankState q.1 s₀ q.2) :=
  measurable_pi_iff.mpr (measurable_rankState_joint s₀)

theorem measurable_rankHistory_joint (s₀ : State) (k : ℕ) :
    Measurable (fun q : (ℕ → Bool) × (ℕ → ℝ) ↦ rankHistory q.1 s₀ k q.2) :=
  (measurable_trajectoryPrefix k).comp (measurable_rankTrajectory_joint s₀)

end HeightPaper.Model

namespace HeightPaper.CountCoupling

/-- First coordinate: infection/recovery uniforms. Second coordinate: the
independent active-parent uniforms. -/
noncomputable def birthParentLaw : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
  uniformLaw.prod uniformLaw

instance : IsProbabilityMeasure birthParentLaw := by
  unfold birthParentLaw
  infer_instance

theorem birthParentLaw_map_fst : birthParentLaw.map Prod.fst = uniformLaw := by
  simp [birthParentLaw]

theorem birthParentLaw_map_snd : birthParentLaw.map Prod.snd = uniformLaw := by
  simp [birthParentLaw]

theorem birthParentLaw_independent : IndepFun Prod.fst Prod.snd birthParentLaw :=
  indepFun_prod measurable_id measurable_id

theorem birthParentLaw_map_rankTrajectory (events : ℕ → Bool) (s₀ : Model.State) :
    birthParentLaw.map (fun q ↦ Model.rankState events s₀ q.2) =
      Model.prescribedTrajectoryMeasure events s₀ := by
  rw [show (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦ Model.rankState events s₀ q.2) =
      Model.rankState events s₀ ∘ Prod.snd from rfl,
    ← Measure.map_map (Model.measurable_rankTrajectory events s₀) measurable_snd,
    birthParentLaw_map_snd, Model.rankTrajectory_law]

theorem measurable_finite_rankTrajectory (l : ℝ) (n : ℕ) (s₀ : Model.State) :
    Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      Model.rankState (finiteBirth l n q.1) s₀ q.2) :=
  (Model.measurable_rankTrajectory_joint s₀).comp
    (((measurable_pi_iff.mpr (measurable_finiteBirth l n)).comp measurable_fst).prodMk measurable_snd)

theorem measurable_local_rankTrajectory (l : ℝ) (s₀ : Model.State) :
    Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) ↦
      Model.rankState (localBirth l q.1) s₀ q.2) :=
  (Model.measurable_rankTrajectory_joint s₀).comp
    (((measurable_pi_iff.mpr (measurable_localBirth l)).comp measurable_fst).prodMk measurable_snd)

end HeightPaper.CountCoupling
