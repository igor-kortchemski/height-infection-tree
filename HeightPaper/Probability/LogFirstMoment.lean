module

public import HeightPaper.Analysis.ProfileFirstMomentScale
public import Mathlib.MeasureTheory.Measure.Real

/-! # Logarithmic upper tails from a random normalizer and conditional first moments -/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace HeightPaper

theorem log_upper_tail_of_normalizer
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (A : ∀ n, Set (Ω n)) (C F : ∀ n, Ω n → ℝ) {b : ℝ}
    (hCpos : ∀ n ω, ω ∈ A n → 0 < C n ω)
    (hFpos : ∀ n ω, ω ∈ A n → 0 < F n ω)
    (hC : ∀ η > (0 : ℝ), Tendsto (fun n ↦ (μ n).real
      {ω | ω ∈ A n ∧ η ≤ |Real.log (C n ω) / Real.log n - b|}) atTop (𝓝 0))
    (hfirst : ∀ n B D, 0 < B → 0 < D → (μ n).real
      {ω | ω ∈ A n ∧ C n ω ≤ B ∧ D ≤ F n ω} ≤ B / D) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (μ n).real
      {ω | ω ∈ A n ∧ ε ≤ Real.log (F n ω) / Real.log n - b}) atTop (𝓝 0) := by
  intro ε hε
  have hη : 0 < ε / 2 := half_pos hε
  have ht := (hC (ε / 2) hη).add
    (tendsto_nat_rpow_ratio_zero (show b + ε / 2 < b + ε by linarith))
  rw [zero_add] at ht
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ ht
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hnR
  have hlog : 0 < Real.log n := Real.log_pos hnR
  have hsubset : {ω | ω ∈ A n ∧ ε ≤ Real.log (F n ω) / Real.log n - b} ⊆
      {ω | ω ∈ A n ∧ ε / 2 ≤ |Real.log (C n ω) / Real.log n - b|} ∪
      {ω | ω ∈ A n ∧ C n ω ≤ (n : ℝ) ^ (b + ε / 2) ∧
        (n : ℝ) ^ (b + ε) ≤ F n ω} := by
    intro ω hω
    by_cases he : ε / 2 ≤ |Real.log (C n ω) / Real.log n - b|
    · exact Or.inl ⟨hω.1, he⟩
    · right
      have hc : Real.log (C n ω) / Real.log n < b + ε / 2 := by
        have := (abs_lt.mp (lt_of_not_ge he)).2
        linarith
      have hc' := (div_lt_iff₀ hlog).mp hc
      have hf : (b + ε) * Real.log n ≤ Real.log (F n ω) :=
        (le_div_iff₀ hlog).mp (by linarith only [hω.2])
      refine ⟨hω.1, ?_, ?_⟩
      · rw [Real.rpow_def_of_pos hn0]
        have hh := Real.exp_lt_exp.mpr hc'
        rw [Real.exp_log (hCpos n ω hω.1)] at hh
        simpa only [mul_comm] using hh.le
      · rw [Real.rpow_def_of_pos hn0]
        have hh := Real.exp_le_exp.mpr hf
        rw [Real.exp_log (hFpos n ω hω.1)] at hh
        simpa only [mul_comm] using hh
  exact (measureReal_mono hsubset).trans ((measureReal_union_le _ _).trans
    (add_le_add_right (hfirst n _ _ (Real.rpow_pos_of_pos hn0 _) (Real.rpow_pos_of_pos hn0 _)) _))

/-- A total-profile first moment gives the upper height bound, retaining the
random-normalizer exceptional probability explicitly. -/
theorem height_upper_tail_of_normalizer
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (A : ∀ n, Set (Ω n)) (C H : ∀ n, Ω n → ℝ) (horizon : ℕ → ℕ)
    {T w b x a : ℝ} (hx : 0 < x) (ha : 0 < a)
    (hbalance : 1 + b = x * a)
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    (hCpos : ∀ n ω, ω ∈ A n → 0 < C n ω)
    (hC : ∀ η > (0 : ℝ), Tendsto (fun n ↦ (μ n).real
      {ω | ω ∈ A n ∧ η ≤ |Real.log (C n ω) / Real.log n - b|}) atTop (𝓝 0))
    (hfirst : ∀ n B h, 0 < B → (μ n).real
      {ω | ω ∈ A n ∧ C n ω ≤ B ∧ h ≤ H n ω} ≤
        (1 + w * horizon n * B) / Real.exp (x * h)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (μ n).real
      {ω | ω ∈ A n ∧ a + ε ≤ H n ω / Real.log n}) atTop (𝓝 0) := by
  intro ε hε
  let η := x * ε / 2
  have hη : 0 < η := half_pos (mul_pos hx hε)
  have hgap : 1 + (b + η) < x * (a + ε) := by
    dsimp [η] at hη ⊢
    nlinarith only [hbalance, hη]
  have hc : 0 < x * (a + ε) := mul_pos hx (add_pos ha hε)
  have ht := (hC η hη).add
    (tendsto_profile_firstMoment_height_bound (w := w) horizon hhorizon hc hgap)
  rw [zero_add] at ht
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ ht
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hnR
  have hlog : 0 < Real.log n := Real.log_pos hnR
  have hsubset : {ω | ω ∈ A n ∧ a + ε ≤ H n ω / Real.log n} ⊆
      {ω | ω ∈ A n ∧ η ≤ |Real.log (C n ω) / Real.log n - b|} ∪
      {ω | ω ∈ A n ∧ C n ω ≤ (n : ℝ) ^ (b + η) ∧
        (a + ε) * Real.log n ≤ H n ω} := by
    intro ω hω
    by_cases he : η ≤ |Real.log (C n ω) / Real.log n - b|
    · exact Or.inl ⟨hω.1, he⟩
    · right
      have hc : Real.log (C n ω) / Real.log n < b + η := by
        have := (abs_lt.mp (lt_of_not_ge he)).2
        linarith
      have hc' := (div_lt_iff₀ hlog).mp hc
      refine ⟨hω.1, ?_, (le_div_iff₀ hlog).mp hω.2⟩
      rw [Real.rpow_def_of_pos hn0]
      have hh := Real.exp_lt_exp.mpr hc'
      rw [Real.exp_log (hCpos n ω hω.1)] at hh
      simpa only [mul_comm] using hh.le
  have hb := hfirst n ((n : ℝ) ^ (b + η)) ((a + ε) * Real.log n)
    (Real.rpow_pos_of_pos hn0 _)
  have heq : Real.exp (x * ((a + ε) * Real.log n)) = (n : ℝ) ^ (x * (a + ε)) := by
    rw [Real.rpow_def_of_pos hn0]
    congr 1
    ring
  rw [heq] at hb
  exact (measureReal_mono hsubset).trans ((measureReal_union_le _ _).trans
    (add_le_add_right hb _))

end HeightPaper
