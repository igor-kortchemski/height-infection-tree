module

public import HeightPaper.Probability.FiniteProfileIncrements
public import HeightPaper.Model.AnalyticProfileProbability
public import HeightPaper.Probability.UniformParentLaw
public import HeightPaper.Probability.TreeUniformCoupling

/-! # Uniform disk deviations of the actual finite prescribed profile -/

@[expose] public section

open MeasureTheory Complex Metric Set

namespace HeightPaper.Model

/-- Outer probability suffices for simultaneous events with arbitrary tilt
sets, so no uncountable measurability assertion is hidden in this transfer. -/
theorem rankTrajectory_measureReal_preimage_le (events : ℕ → Bool) (s₀ : State)
    (E : Set (ℕ → State)) :
    CountCoupling.uniformLaw.real {v | rankState events s₀ v ∈ E} ≤
      (prescribedTrajectoryMeasure events s₀).real E := by
  have hh := Measure.le_map_apply (μ := CountCoupling.uniformLaw)
    (measurable_rankTrajectory events s₀).aemeasurable E
  rw [rankTrajectory_law] at hh
  exact ENNReal.toReal_mono (measure_ne_top _ _) hh

end HeightPaper.Model

namespace HeightPaper.CountCoupling

open Model

/-- A finite event prefix together with two tree states is a countable code.
Every event determined by this code is measurable, even when its tilt set is
uncountable. -/
theorem measurableSet_of_finiteBirth_rankStates (l : ℝ) (n H j k : ℕ)
    {E : Set ((ℕ → ℝ) × (ℕ → ℝ))}
    (hE : ∀ q q', (∀ i < H, finiteBirth l n q.1 i = finiteBirth l n q'.1 i) →
      rankState (finiteBirth l n q.1) (initial n) q.2 j =
        rankState (finiteBirth l n q'.1) (initial n) q'.2 j →
      rankState (finiteBirth l n q.1) (initial n) q.2 k =
        rankState (finiteBirth l n q'.1) (initial n) q'.2 k → (q ∈ E ↔ q' ∈ E)) :
    MeasurableSet E := by
  let f : ((ℕ → ℝ) × (ℕ → ℝ)) → (Fin H → Bool) × (State × State) := fun q =>
    (fun i => finiteBirth l n q.1 i,
      rankState (finiteBirth l n q.1) (initial n) q.2 j,
      rankState (finiteBirth l n q.1) (initial n) q.2 k)
  have hf : Measurable f := by
    exact (Measurable.of_eval (fun i : Fin H => (measurable_finiteBirth l n i).comp measurable_fst)).prodMk
      (((measurable_pi_apply j).comp (measurable_finite_rankTrajectory l n (initial n))).prodMk
        ((measurable_pi_apply k).comp (measurable_finite_rankTrajectory l n (initial n))))
  have heq : f ⁻¹' (f '' E) = E := by
    ext q
    constructor
    · rintro ⟨q', hq', hcode⟩
      have hb := congrArg Prod.fst hcode
      have hj := congrArg (fun a => a.2.1) hcode
      have hk := congrArg (fun a => a.2.2) hcode
      exact (hE q' q (fun i hi => congrFun hb ⟨i, hi⟩) hj hk).mp hq'
    · intro hq
      exact ⟨q, hq, rfl⟩
  rw [← heq]
  exact hf (Set.to_countable _).measurableSet

theorem measurableSet_finite_rankProfile_difference (l : ℝ) (n H j k : ℕ)
    (hj : j ≤ H) (hk : k ≤ H) (K : Set ℂ) (ε : ℝ) :
    MeasurableSet {q : (ℕ → ℝ) × (ℕ → ℝ) | ∃ z ∈ K,
      ε < ‖prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n q.1) (initial n)
          (finiteSafeCutoff l n H q.1) k (rankState (finiteBirth l n q.1) (initial n) q.2 k) -
        prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n q.1) (initial n)
          (finiteSafeCutoff l n H q.1) j (rankState (finiteBirth l n q.1) (initial n) q.2 j)‖} := by
  apply measurableSet_of_finiteBirth_rankStates l n H j k
  intro q q' he hsj hsk
  have hJ := finiteSafeCutoff_congr_birth_prefix he
  have hC (i : ℕ) (hi : i ≤ H) (z : ℂ) :=
    prescribedNormalizerFrom_congr_prefix (Complex.exp z) 1 (finiteSafeCutoff l n H q'.1) he hi
  simp only [mem_ofPred_eq, prescribedNormalizedProfile, infectious_initial, hsj, hsk, hJ,
    hC j hj, hC k hk]

theorem finiteProfileDifferenceMoment_eq_trajectory (l : ℝ) (n H : ℕ) (u : ℕ → ℝ)
    {j k : ℕ} (hjk : j ≤ k) (z : ℂ) (p : ℝ) :
    finiteProfileDifferenceMoment l n H u j k z p =
      ∫ ω, ‖prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n u) (initial n)
          (finiteSafeCutoff l n H u) k (ω k) -
        prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n u) (initial n)
          (finiteSafeCutoff l n H u) j (ω j)‖ ^ p
        ∂prescribedTrajectoryMeasure (finiteBirth l n u) (initial n) := by
  have hh := kernelTrajectory_integral_prefix (fun i => prescribedStep (finiteBirth l n u i))
    (initial n) k (fun q => ‖normalizedActiveWeight (Complex.exp z) q.last /
      finiteComplexNormalizer l n H u k z - normalizedActiveWeight (Complex.exp z) (q.eval j) /
        finiteComplexNormalizer l n H u j z‖ ^ p)
  simpa only [finiteProfileDifferenceMoment, prescribedNormalizedProfile,
    infectious_initial, trajectoryPrefix_last, trajectoryPrefix_eval k _ j hjk,
    finiteComplexNormalizer, prescribedTrajectoryMeasure] using hh.symm

/-- A conditional moment bound on the outer circle controls the simultaneous
profile difference on the smaller disk under the actual uniform parent draws. -/
theorem finiteProfile_uniform_difference_probability_le
    {l : ℝ} {n H : ℕ} {u : ℕ → ℝ} (hs : ∀ i ≤ H, 0 < finiteWalk l n u i)
    {j k : ℕ} (hJj : finiteSafeCutoff l n H u ≤ j) (hjk : j ≤ k) (hk : k ≤ H)
    (z₀ : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hwindow : ∀ z ∈ closedBall z₀ R, z.re ≤ 2 * profileRoot l)
    {p B ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε)
    (hbound : ∀ z ∈ sphere z₀ R, finiteProfileDifferenceMoment l n H u j k z p ≤ B) :
    uniformLaw.real {v | ∃ z ∈ closedBall z₀ r,
      ε < ‖prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n u) (initial n)
          (finiteSafeCutoff l n H u) k (rankState (finiteBirth l n u) (initial n) v k) -
        prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n u) (initial n)
          (finiteSafeCutoff l n H u) j (rankState (finiteBirth l n u) (initial n) v j)‖} ≤
      (R / (2 * Real.pi * (R - r)) * (2 * Real.pi) * B ^ p⁻¹) / ε := by
  apply (rankTrajectory_measureReal_preimage_le (finiteBirth l n u) (initial n)
    {ω | ∃ z ∈ closedBall z₀ r,
      ε < ‖prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n u) (initial n)
          (finiteSafeCutoff l n H u) k (ω k) -
        prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n u) (initial n)
          (finiteSafeCutoff l n H u) j (ω j)‖}).trans
  apply prescribedTrajectory_uniform_difference_probability_le_of_two_normalizers
    (finiteBirth l n u) (initial n) (finiteSafeCutoff l n H u) z₀ hr hrR hJj hjk
    (fun z hz => finiteComplexNormalizer_ne_zero hs (hjk.trans hk) (hwindow z hz))
    (fun z hz => finiteComplexNormalizer_ne_zero hs hk (hwindow z hz)) hp hε
  intro z hz
  rw [← finiteProfileDifferenceMoment_eq_trajectory l n H u hjk z p]
  exact hbound z hz

end HeightPaper.CountCoupling
