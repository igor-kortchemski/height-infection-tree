module

public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A common uniform sequence and the unabsorbed local walk

The same independent uniform coordinates are used for every parameter.  The
walk takes values in the integers and continues through zero, as in the
coupled construction of the paper.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace HeightPaper.CountCoupling

noncomputable def birthThreshold (l : ℝ) : ℝ := l / (1 + l)

noncomputable def localBirth (l : ℝ) (u : ℕ → ℝ) (k : ℕ) : Bool :=
  decide (u k ≤ birthThreshold l)

noncomputable def localWalk (l : ℝ) (u : ℕ → ℝ) (k : ℕ) : ℤ :=
  1 + ∑ i ∈ Finset.range k, if localBirth l u i then 1 else -1

/-- Lebesgue probability measure on the closed unit interval. -/
noncomputable def unitUniform : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitUniform := by
  constructor
  simp [unitUniform, Real.volume_Icc]

/-- One probability space for all parameters and all event times. -/
noncomputable def uniformLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ ↦ unitUniform)

instance : IsProbabilityMeasure uniformLaw := by
  unfold uniformLaw
  infer_instance

theorem uniformLaw_map_eval (k : ℕ) :
    uniformLaw.map (fun u ↦ u k) = unitUniform :=
  Measure.infinitePi_map_eval _ _

theorem uniformLaw_independent :
    iIndepFun (fun k (u : ℕ → ℝ) ↦ u k) uniformLaw :=
  iIndepFun_infinitePi (X := fun _ x ↦ x) (fun _ ↦ measurable_id)

theorem birthThreshold_nonneg {l : ℝ} (hl : 0 ≤ l) : 0 ≤ birthThreshold l := by
  exact div_nonneg hl (by linarith)

theorem birthThreshold_le_one {l : ℝ} (hl : 0 ≤ l) : birthThreshold l ≤ 1 := by
  unfold birthThreshold
  apply (div_le_one (by linarith : (0 : ℝ) < 1 + l)).mpr
  linarith

theorem birthThreshold_mono {l₀ l : ℝ} (h₀ : 0 ≤ l₀) (h : l₀ ≤ l) :
    birthThreshold l₀ ≤ birthThreshold l := by
  unfold birthThreshold
  rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 1 + l₀)
    (by linarith : (0 : ℝ) < 1 + l)]
  nlinarith

theorem measurable_localBirth (l : ℝ) (k : ℕ) : Measurable (fun u ↦ localBirth l u k) := by
  have h : MeasurableSet {u : ℕ → ℝ | u k ≤ birthThreshold l} :=
    measurableSet_le (measurable_pi_apply k) measurable_const
  simpa [localBirth] using
    (measurable_const.ite h measurable_const :
      Measurable (fun u : ℕ → ℝ ↦ if u k ≤ birthThreshold l then true else false))

theorem localBirth_independent (l : ℝ) :
    iIndepFun (fun k u ↦ localBirth l u k) uniformLaw := by
  unfold localBirth uniformLaw
  apply iIndepFun_infinitePi (X := fun _ x ↦ decide (x ≤ birthThreshold l))
  intro k
  have h : MeasurableSet {x : ℝ | x ≤ birthThreshold l} := measurableSet_Iic
  simpa [localBirth] using
    (measurable_const.ite h measurable_const :
      Measurable (fun x : ℝ ↦ if x ≤ birthThreshold l then true else false))

theorem uniformLaw_le (k : ℕ) {p : ℝ} (_hp : 0 ≤ p) (hp' : p ≤ 1) :
    uniformLaw {u | u k ≤ p} = ENNReal.ofReal p := by
  have heq : Iic p ∩ Icc (0 : ℝ) 1 = Icc 0 p := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hxp, hx0, _⟩
      exact ⟨hx0, hxp⟩
    · rintro ⟨hx0, hxp⟩
      exact ⟨hxp, hx0, hxp.trans hp'⟩
  rw [show {u : ℕ → ℝ | u k ≤ p} = (fun u ↦ u k) ⁻¹' Iic p from rfl,
    ← Measure.map_apply (measurable_pi_apply k) measurableSet_Iic,
    uniformLaw_map_eval, unitUniform, Measure.restrict_apply measurableSet_Iic, heq,
    Real.volume_Icc, sub_zero]

theorem uniformLaw_interval (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    uniformLaw {u | a < u k ∧ u k ≤ b} = ENNReal.ofReal (b - a) := by
  have hsub : Ioc a b ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨ha.trans hx.1.le, hx.2.trans hb⟩
  rw [show {u : ℕ → ℝ | a < u k ∧ u k ≤ b} =
      (fun u ↦ u k) ⁻¹' Ioc a b from rfl,
    ← Measure.map_apply (measurable_pi_apply k) measurableSet_Ioc,
    uniformLaw_map_eval, unitUniform, Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.mpr hsub, Real.volume_Ioc]

theorem uniformLaw_interval_real (k : ℕ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) :
    uniformLaw.real {u | a < u k ∧ u k ≤ b} = b - a := by
  rw [Measure.real, uniformLaw_interval k ha hb, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

theorem uniformLaw_ae_pos : ∀ᵐ u ∂uniformLaw, ∀ k, 0 < u k := by
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  simpa only [not_lt, ENNReal.ofReal_zero] using
    (uniformLaw_le k (p := 0) le_rfl zero_le_one)

theorem uniformLaw_ae_le_one : ∀ᵐ u ∂uniformLaw, ∀ k, u k ≤ 1 := by
  rw [ae_all_iff]
  intro k
  apply (ae_iff_measure_eq
    (measurableSet_le (measurable_pi_apply k) measurable_const).nullMeasurableSet).mpr
  simpa using uniformLaw_le k (p := 1) zero_le_one le_rfl

/-- Exact Bernoulli success probability of each thresholded draw. -/
theorem localBirth_probability {l : ℝ} (hl : 0 ≤ l) (k : ℕ) :
    uniformLaw {u | localBirth l u k = true} = ENNReal.ofReal (birthThreshold l) := by
  simpa [localBirth] using uniformLaw_le k (birthThreshold_nonneg hl) (birthThreshold_le_one hl)

/-- The real-valued increment, used for expectations and concentration. -/
noncomputable def localStep (l : ℝ) (k : ℕ) (u : ℕ → ℝ) : ℝ :=
  if localBirth l u k then 1 else -1

theorem measurable_localStep (l : ℝ) (k : ℕ) : Measurable (localStep l k) := by
  exact (measurable_of_countable (fun b : Bool ↦ if b then (1 : ℝ) else -1)).comp
    (measurable_localBirth l k)

theorem localStep_mem_Icc (l : ℝ) (k : ℕ) (u : ℕ → ℝ) :
    localStep l k u ∈ Icc (-1 : ℝ) 1 := by
  unfold localStep
  split <;> norm_num

theorem integrable_localStep (l : ℝ) (k : ℕ) : Integrable (localStep l k) uniformLaw :=
  Integrable.of_mem_Icc (-1) 1 (measurable_localStep l k).aemeasurable
    (Filter.Eventually.of_forall (localStep_mem_Icc l k))

/-- The drift of the local walk. -/
noncomputable def localDrift (l : ℝ) : ℝ := (l - 1) / (1 + l)

theorem integral_localStep {l : ℝ} (hl : 0 ≤ l) (k : ℕ) :
    (∫ u, localStep l k u ∂uniformLaw) = localDrift l := by
  let A : Set (ℕ → ℝ) := {u | localBirth l u k = true}
  have hA : MeasurableSet A := (measurable_localBirth l k) (measurableSet_singleton true)
  have heq : localStep l k = fun u ↦ 2 * A.indicator (fun _ ↦ (1 : ℝ)) u - 1 := by
    funext u
    simp only [localStep, A, Set.indicator, mem_ofPred_eq]
    cases localBirth l u k <;> norm_num
  rw [heq, integral_sub ((integrable_const (1 : ℝ)).indicator hA |>.const_mul 2)
    (integrable_const 1), integral_const_mul, integral_indicator_const _ hA]
  simp only [smul_eq_mul, mul_one, integral_const, probReal_univ]
  rw [Measure.real, localBirth_probability hl k, ENNReal.toReal_ofReal (birthThreshold_nonneg hl)]
  unfold birthThreshold localDrift
  field_simp
  ring

theorem localWalk_cast (l : ℝ) (u : ℕ → ℝ) (k : ℕ) :
    (localWalk l u k : ℝ) = 1 + ∑ i ∈ Finset.range k, localStep l i u := by
  simp [localWalk, localStep, Int.cast_sum, Int.cast_ite]

end HeightPaper.CountCoupling
