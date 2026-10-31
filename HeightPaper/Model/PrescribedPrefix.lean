module

public import HeightPaper.Model.ComplexNormalizer
public import HeightPaper.Model.EpidemicEventConditioning

/-! # Dependence of prescribed profile laws on the complete finite event prefix -/

@[expose] public section

open MeasureTheory
open scoped BigOperators NNReal

namespace HeightPaper.Model

theorem prescribedWalk_congr_prefix {e f : ℕ → Bool} (i₀ : ℕ) {H : ℕ}
    (hef : ∀ i < H, e i = f i) {k : ℕ} (hk : k ≤ H) :
    prescribedWalk e i₀ k = prescribedWalk f i₀ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [prescribedWalk, prescribedWalk, hef k (by omega), ih (by omega)]

theorem birthReciprocal_congr_prefix {e f : ℕ → Bool} (i₀ : ℕ) {H : ℕ}
    (hef : ∀ i < H, e i = f i) {k : ℕ} (hk : k < H) :
    birthReciprocal e i₀ k = birthReciprocal f i₀ k := by
  rw [birthReciprocal, birthReciprocal, hef k hk, prescribedWalk_congr_prefix i₀ hef hk.le]

theorem prescribedNormalizerFrom_congr_prefix (w : ℂ) {e f : ℕ → Bool} (i₀ J : ℕ)
    {H : ℕ} (hef : ∀ i < H, e i = f i) {k : ℕ} (hk : k ≤ H) :
    prescribedNormalizerFrom w e i₀ J k = prescribedNormalizerFrom w f i₀ J k := by
  apply Finset.prod_congr rfl
  intro i hi
  have hiH := (Finset.mem_Ico.mp hi).2.trans_le hk
  rw [hef i hiH, prescribedWalk_congr_prefix i₀ hef hiH.le]

theorem realNormalizerFrom_congr_prefix (w : ℝ) {e f : ℕ → Bool} (i₀ J : ℕ)
    {H : ℕ} (hef : ∀ i < H, e i = f i) {k : ℕ} (hk : k ≤ H) :
    realNormalizerFrom w e i₀ J k = realNormalizerFrom w f i₀ J k := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [birthReciprocal_congr_prefix i₀ hef ((Finset.mem_Ico.mp hi).2.trans_le hk)]

theorem kernelPathLaw_prescribed_congr_prefix {e f : ℕ → Bool} (s₀ : State)
    {H : ℕ} (hef : ∀ i < H, e i = f i) :
    kernelPathLaw (fun i ↦ prescribedStep (e i)) s₀ H =
      kernelPathLaw (fun i ↦ prescribedStep (f i)) s₀ H := by
  induction H with
  | zero => rfl
  | succ H ih =>
      rw [kernelPathLaw, kernelPathLaw, ih (fun i hi ↦ hef i (by omega)), hef H (by omega)]

/-- Conditioning on the entire event word retains the exact law of the
earlier tree prefix, so moments can be computed at their actual event time. -/
theorem conditioned_profile_moment_eq (rate : ℝ≥0) (n H : ℕ) (events : ℕ → Bool)
    (hpos : ∀ i ≤ H, 0 < prescribedWalk events 1 i)
    (hsupport : ∃ q ∈ eventCylinder events 1 H, q ∈ (pathLaw rate n H).support)
    (w C : ℂ) (p : ℝ) {k : ℕ} (hk : k ≤ H) :
    (∫ q, ‖normalizedActiveWeight w (q.eval k) / C‖ ^ p
      ∂((pathLaw rate n H).filter (eventCylinder events 1 H) hsupport).toMeasure) =
      ∫ q, ‖normalizedActiveWeight w q.last / C‖ ^ p
        ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) k := by
  rw [pathLaw_filter_eventCylinder rate n events H hpos hsupport]
  change (∫ q, ‖normalizedActiveWeight w (q.eval k) / C‖ ^ p
    ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) H) = _
  rw [← kernelPathMeasure_map_prefixAt (fun i ↦ prescribedStep (events i)) (initial n) H k hk]
  rw [integral_map (FinitePath.measurable _).aemeasurable
    (FinitePath.measurable _).aestronglyMeasurable]
  rfl

/-- Conditioning on the complete epidemic event word preserves two profile
observations on the same earlier tree history, including martingale increments. -/
theorem conditioned_profile_difference_moment_eq (rate : ℝ≥0) (n H : ℕ)
    (events : ℕ → Bool) (hpos : ∀ i ≤ H, 0 < prescribedWalk events 1 i)
    (hsupport : ∃ q ∈ eventCylinder events 1 H, q ∈ (pathLaw rate n H).support)
    (w Cj Ck : ℂ) (p : ℝ) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ H) :
    (∫ q, ‖normalizedActiveWeight w (q.eval k) / Ck -
        normalizedActiveWeight w (q.eval j) / Cj‖ ^ p
      ∂((pathLaw rate n H).filter (eventCylinder events 1 H) hsupport).toMeasure) =
      ∫ q, ‖normalizedActiveWeight w q.last / Ck -
        normalizedActiveWeight w (q.eval j) / Cj‖ ^ p
        ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) k := by
  rw [pathLaw_filter_eventCylinder rate n events H hpos hsupport]
  change (∫ q, ‖normalizedActiveWeight w (q.eval k) / Ck -
    normalizedActiveWeight w (q.eval j) / Cj‖ ^ p
    ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) H) = _
  rw [← kernelPathMeasure_map_prefixAt (fun i ↦ prescribedStep (events i)) (initial n) H k hk]
  rw [integral_map (FinitePath.measurable _).aemeasurable
    (FinitePath.measurable _).aestronglyMeasurable]
  simp only [FinitePath.prefixAt_last, FinitePath.prefixAt_eval _ hjk]

end HeightPaper.Model
