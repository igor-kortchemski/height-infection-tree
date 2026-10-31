module

public import HeightPaper.Probability.FiniteTreeCouplingLaw
public import HeightPaper.Probability.GhostBudgetCoupling

/-!
# Exact tree-kernel law from an arbitrary initial active state

The two-uniform realization of the epidemic transition is independent of the
initial state. The general path law below permits the active-padded budget
state to inherit the existing stopped-count concentration estimates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Classical

namespace HeightPaper.CountCoupling

open Model

noncomputable def uniformTreeStateFrom (l : ℝ) (n : ℕ) (s₀ : State)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) : ℕ → State
  | 0 => s₀
  | k + 1 => uniformTreeUpdate l n (uniformTreeStateFrom l n s₀ q k) (q.1 k, q.2 k)

noncomputable def uniformTreeHistoryFrom (l : ℝ) (n : ℕ) (s₀ : State)
    (k : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ)) : FinitePath k :=
  trajectoryPrefix k (uniformTreeStateFrom l n s₀ q)

theorem measurable_uniformTreeStateFrom (l : ℝ) (n : ℕ) (s₀ : State)
    (k : ℕ) : Measurable (fun q ↦ uniformTreeStateFrom l n s₀ q k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hm : Measurable (fun r : State × (ℝ × ℝ) ↦
        uniformTreeUpdate l n r.1 r.2) :=
      measurable_from_prod_countable_right (fun s ↦ measurable_uniformTreeUpdate l n s)
    exact hm.comp (ih.prodMk
      (((measurable_pi_apply k).comp measurable_fst).prodMk
        ((measurable_pi_apply k).comp measurable_snd)))

theorem measurable_uniformTreeHistoryFrom (l : ℝ) (n : ℕ) (s₀ : State)
    (k : ℕ) : Measurable (uniformTreeHistoryFrom l n s₀ k) := by
  exact (measurable_trajectoryPrefix k).comp
    (measurable_pi_iff.mpr (measurable_uniformTreeStateFrom l n s₀))

theorem uniformTreeStateFrom_congr_prefix (l : ℝ) (n : ℕ) (s₀ : State)
    {q r : (ℕ → ℝ) × (ℕ → ℝ)} (k : ℕ)
    (hqr : ∀ i < k, q.1 i = r.1 i ∧ q.2 i = r.2 i) :
    uniformTreeStateFrom l n s₀ q k = uniformTreeStateFrom l n s₀ r k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [uniformTreeStateFrom, uniformTreeStateFrom,
      ih (fun i hi ↦ hqr i (by omega)),
      (hqr k (by omega)).1, (hqr k (by omega)).2]

theorem uniformTreeHistoryFrom_indep_next (l : ℝ) (n : ℕ) (s₀ : State)
    (k : ℕ) :
    IndepFun (uniformTreeHistoryFrom l n s₀ k ∘ splitUniforms)
      (fun w : (Fin 2 × ℕ) → ℝ ↦ (w (0, k), w (1, k))) pairedUniformLaw := by
  have hind := pairedUniformLaw_independent.indepFun_set
    {i : Fin 2 × ℕ | i.2 < k} {i | i.2 = k}
    (by
      apply Set.disjoint_left.mpr
      intro i hi he
      simp only [Set.mem_ofPred_eq] at hi he
      omega) (fun i ↦ measurable_pi_apply i)
  have hh := hind.comp
    (((measurable_uniformTreeHistoryFrom l n s₀ k).comp measurable_splitUniforms).comp
      (measurable_extendPairPast k))
    ((measurable_pi_apply (⟨(0, k), rfl⟩ : {i : Fin 2 × ℕ // i.2 = k})).prodMk
      (measurable_pi_apply (⟨(1, k), rfl⟩ : {i : Fin 2 × ℕ // i.2 = k})))
  have heq : ((uniformTreeHistoryFrom l n s₀ k ∘ splitUniforms) ∘ extendPairPast k) ∘
      (fun (w : (Fin 2 × ℕ) → ℝ) (i : {i : Fin 2 × ℕ // i.2 < k}) ↦ w i) =
        uniformTreeHistoryFrom l n s₀ k ∘ splitUniforms := by
    funext w
    apply FinitePath.ext
    intro i
    apply uniformTreeStateFrom_congr_prefix
    intro j hj
    have hjk : j < k := by have := i.isLt; omega
    simp [splitUniforms, extendPairPast, hjk]
  convert hh using 1
  · exact heq.symm
  · rfl

theorem uniformTreeHistoryFrom_succ (l : ℝ) (n : ℕ) (s₀ : State)
    (k : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ)) :
    uniformTreeHistoryFrom l n s₀ (k + 1) q =
      (uniformTreeHistoryFrom l n s₀ k q).append
        (uniformTreeUpdate l n (uniformTreeHistoryFrom l n s₀ k q).last
          (q.1 k, q.2 k)) := by
  exact trajectoryPrefix_succ k (uniformTreeStateFrom l n s₀ q)

theorem paired_uniformTreeHistoryFrom_law (l : ℝ≥0) (n : ℕ) (s₀ : State)
    (k : ℕ) :
    pairedUniformLaw.map (uniformTreeHistoryFrom l n s₀ k ∘ splitUniforms) =
      kernelPathMeasure (fun _ ↦ step (l / n)) s₀ k := by
  induction k with
  | zero =>
    have he : uniformTreeHistoryFrom (l : ℝ) n s₀ 0 ∘ splitUniforms =
        fun _ ↦ (⟨fun _ ↦ s₀⟩ : FinitePath 0) := by
      funext w
      apply FinitePath.ext
      intro i
      simp [uniformTreeHistoryFrom, trajectoryPrefix, uniformTreeStateFrom]
    rw [he, kernelPathMeasure, kernelPathLaw, PMF.toMeasure_pure]
    simp
  | succ k ih =>
    have he : uniformTreeHistoryFrom (l : ℝ) n s₀ (k + 1) ∘ splitUniforms =
        fun w ↦ (uniformTreeHistoryFrom l n s₀ k (splitUniforms w)).append
          (uniformTreeUpdate l n
            (uniformTreeHistoryFrom l n s₀ k (splitUniforms w)).last
            (w (0, k), w (1, k))) := by
      funext w
      exact uniformTreeHistoryFrom_succ l n s₀ k (splitUniforms w)
    rw [he, kernelPathMeasure, kernelPathLaw]
    refine independent_pmf_update pairedUniformLaw
      (uniformTreeHistoryFrom l n s₀ k ∘ splitUniforms)
      (fun w ↦ (w (0, k), w (1, k)))
      (fun (p : FinitePath k) v ↦ p.append (uniformTreeUpdate l n p.last v))
      (kernelPathLaw (fun _ ↦ step (l / n)) s₀ k)
      (fun p ↦ (step (l / n) p.last).map p.append)
      ((measurable_uniformTreeHistoryFrom l n s₀ k).comp measurable_splitUniforms)
      ((measurable_pi_apply (0, k)).prodMk (measurable_pi_apply (1, k))) ?_ ?_
      (uniformTreeHistoryFrom_indep_next l n s₀ k) ih ?_
    · intro p
      exact (measurable_of_countable p.append).comp (measurable_uniformTreeUpdate l n p.last)
    · simp only [Function.comp_def]
      rw [← he]
      exact (measurable_uniformTreeHistoryFrom l n s₀ (k + 1)).comp measurable_splitUniforms
    · intro p
      have hm : Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦
          uniformTreeUpdate l n p.last (w (0, k), w (1, k))) :=
        (measurable_uniformTreeUpdate l n p.last).comp
          ((measurable_pi_apply (0, k)).prodMk (measurable_pi_apply (1, k)))
      change pairedUniformLaw.map (p.append ∘
        (fun w ↦ uniformTreeUpdate l n p.last (w (0, k), w (1, k)))) = _
      rw [← Measure.map_map (measurable_of_countable p.append) hm,
        pairedUniformTreeUpdate_law, PMF.toMeasure_map _ _ (measurable_of_countable p.append)]

theorem uniformTreeHistoryFrom_law (l : ℝ≥0) (n : ℕ) (s₀ : State)
    (k : ℕ) :
    birthParentLaw.map (uniformTreeHistoryFrom l n s₀ k) =
      kernelPathMeasure (fun _ ↦ step (l / n)) s₀ k := by
  calc
    _ = pairedUniformLaw.map (uniformTreeHistoryFrom l n s₀ k ∘ splitUniforms) := by
      rw [← Measure.map_map (measurable_uniformTreeHistoryFrom l n s₀ k)
        measurable_splitUniforms, pairedUniformLaw_map_split]
    _ = _ := paired_uniformTreeHistoryFrom_law l n s₀ k

end HeightPaper.CountCoupling
