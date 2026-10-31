module

public import HeightPaper.Model.AnalyticProfileSummability
public import HeightPaper.Probability.LocalAnalyticProfile
public import HeightPaper.Probability.TreeUniformCoupling

/-! # A measurable analytic-convergence witness on the birth/parent product space -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace HeightPaper

theorem measurableSet_summable_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (b : ℕ → Ω → ℝ) (hb : ∀ m, Measurable (b m)) (hn : ∀ m q, 0 ≤ b m q) :
    MeasurableSet {q | Summable (fun m => b m q)} := by
  have he : {q | Summable (fun m => b m q)} =
      {q | (∑' m, ENNReal.ofReal (b m q)) ≠ ∞} := by
    ext q
    constructor
    · exact fun h => h.tsum_ofReal_ne_top
    · intro h
      exact (ENNReal.summable_toReal h).congr (fun m => ENNReal.toReal_ofReal (hn m q))
  rw [he]
  exact (measurableSet_eq_fun (Measurable.tsum (fun m => (hb m).ennreal_ofReal)) measurable_const).compl

namespace CountCoupling

noncomputable def localDyadicCircleIncrement (l : ℝ) (n : ℕ) (c : ℂ) (R : ℝ) (m : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) : ℝ :=
  Model.prescribedDyadicCircleIncrement (localBirth l q.1) (Model.initial n)
    (localSafeCutoff l q.1) c R m
      (Model.rankState (localBirth l q.1) (Model.initial n) q.2)

theorem measurable_localDyadicCircleIncrement (l : ℝ) (n : ℕ) (c : ℂ) (R : ℝ) (m : ℕ) :
    Measurable (localDyadicCircleIncrement l n c R m) := by
  unfold localDyadicCircleIncrement
  have he : Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) => localBirth l q.1) :=
    Measurable.of_eval (fun i => (measurable_localBirth l i).comp measurable_fst)
  have hm : Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) =>
      ((localBirth l q.1, Model.rankState (localBirth l q.1) (Model.initial n) q.2),
        localSafeCutoff l q.1)) :=
    (he.prodMk (measurable_local_rankTrajectory l (Model.initial n))).prodMk
      ((measurable_localSafeCutoff l).comp measurable_fst)
  simpa only [Function.comp_def] using
    (Model.measurable_prescribedDyadicCircleIncrement_joint_cutoff (Model.initial n) c R m).comp hm

theorem localDyadicCircleIncrement_nonneg (l : ℝ) (n : ℕ) (c : ℂ) (R : ℝ) (m : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) : 0 ≤ localDyadicCircleIncrement l n c R m q := by
  unfold localDyadicCircleIncrement Model.prescribedDyadicCircleIncrement
  exact circleL1_nonneg c R _

theorem measurableSet_localDyadicCircle_summable (l : ℝ) (n : ℕ) (c : ℂ) (R : ℝ) :
    MeasurableSet {q : (ℕ → ℝ) × (ℕ → ℝ) |
      Summable (fun m => localDyadicCircleIncrement l n c R m q)} :=
  measurableSet_summable_nonneg (localDyadicCircleIncrement l n c R)
    (measurable_localDyadicCircleIncrement l n c R)
    (localDyadicCircleIncrement_nonneg l n c R)

end CountCoupling
end HeightPaper
