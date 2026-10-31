module

public import HeightPaper.Model.KernelPath
public import HeightPaper.Model.NormalizedProfile

/-!
# Prescribed-event history laws and profile martingales

The prescribed attachment/freezing construction is realized on a single finite
history probability space. Its full-history conditional expectations give the
paper's profile multiplier and, when the normalizer does not vanish, a complex
martingale. Events are deterministic here; identification with the epidemic
conditioned on an event word is a separate statement.
-/

@[expose] public section

open MeasureTheory

namespace HeightPaper.Model

/-- The paper's prescribed event, with a uniform active vertex. Extinct states
are absorbing; the positive-walk theorems below exclude reaching them. -/
noncomputable def prescribedStep (birth : Bool) (s : State) : PMF State :=
  if h : s.active.Nonempty then
    (uniformActive s h).map (prescribedUpdate birth s)
  else PMF.pure s

theorem finite_support_prescribedStep (birth : Bool) (s : State) :
    (prescribedStep birth s).support.Finite := by
  classical
  by_cases h : s.active.Nonempty
  · rw [prescribedStep, dite_eq_left h]
    exact FinitePMF.finite_support_map _ (Set.toFinite _) _
  · rw [prescribedStep, dite_eq_right h, PMF.support_pure]
    exact Set.finite_singleton s

/-- The deterministic active-count walk associated with a prescribed event
sequence and its starting number of active vertices. -/
def prescribedWalk (events : ℕ → Bool) (i₀ : ℕ) : ℕ → ℕ
  | 0 => i₀
  | k + 1 => prescribedActiveCount (events k) (prescribedWalk events i₀ k)

/-- The active count is deterministic on every supported history while the
prescribed walk remains positive. -/
theorem infectious_kernelPathLaw_prescribed (events : ℕ → Bool) (s₀ : State) (k : ℕ)
    (hpos : ∀ j < k, 0 < prescribedWalk events (infectious s₀) j)
    (p : FinitePath k)
    (hp : p ∈ (kernelPathLaw (fun j ↦ prescribedStep (events j)) s₀ k).support) :
    infectious p.last = prescribedWalk events (infectious s₀) k := by
  induction k with
  | zero =>
      rw [kernelPathLaw, PMF.mem_support_pure_iff] at hp
      subst p
      rfl
  | succ k ih =>
      obtain ⟨q, hq, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
      obtain ⟨s, hs, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
      have hc := ih (fun j hj ↦ hpos j (by omega)) q hq
      have hactive : q.last.active.Nonempty := by
        apply Finset.card_pos.mp
        change 0 < infectious q.last
        rw [hc]
        exact hpos k (by omega)
      change s ∈ (prescribedStep (events k) q.last).support at hs
      rw [prescribedStep, dite_eq_left hactive] at hs
      obtain ⟨v, hv, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
      rw [FinitePath.append_last, infectious_prescribedUpdate (events k)
        ((mem_support_uniformActive hactive v).mp hv), hc]
      rfl

theorem prescribedStep_normalized_integral (w : ℂ) (birth : Bool) (s : State)
    (h : s.active.Nonempty) (hi : 0 < prescribedActiveCount birth (infectious s)) :
    (∫ t, normalizedActiveWeight w t ∂(prescribedStep birth s).toMeasure) =
      normalizedActiveWeight w s * prescribedProfileFactor w birth (infectious s) := by
  rw [prescribedStep, dite_eq_left h,
    ← PMF.toMeasure_map _ _ (measurable_of_countable _),
    integral_map_of_stronglyMeasurable (measurable_of_countable _)
      (measurable_state _).stronglyMeasurable]
  exact uniformPrescribed_normalized_integral w birth s h hi

/-- The exact conditional-expectation assertion of `lem:Mk is a martingale`,
for any complex weight, on the canonical full-history filtration. The denominator
in an infection factor is the count after that infection. -/
theorem prescribedPath_normalized_condExp (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N k : ℕ) (hk : k < N)
    (hpos : ∀ j ≤ N, 0 < prescribedWalk events (infectious s₀) j) :
    (fun p ↦ normalizedActiveWeight w (p.eval k) *
      prescribedProfileFactor w (events k) (prescribedWalk events (infectious s₀) k))
      =ᵐ[kernelPathMeasure (fun j ↦ prescribedStep (events j)) s₀ N]
      (kernelPathMeasure (fun j ↦ prescribedStep (events j)) s₀ N)[
        (fun p ↦ normalizedActiveWeight w (p.eval (k + 1))) | pathFiltration N k] := by
  apply kernelPath_condExp (E := ℂ) (fun j ↦ prescribedStep (events j))
    (fun j s ↦ finite_support_prescribedStep (events j) s) s₀ N k hk
    (normalizedActiveWeight w)
    (fun s ↦ normalizedActiveWeight w s *
      prescribedProfileFactor w (events k) (prescribedWalk events (infectious s₀) k))
  intro p hp
  have hc := infectious_kernelPathLaw_prescribed events s₀ k
    (fun j hj ↦ hpos j (by omega)) p hp
  have hactive : p.last.active.Nonempty := by
    apply Finset.card_pos.mp
    change 0 < infectious p.last
    rw [hc]
    exact hpos k hk.le
  rw [prescribedStep_normalized_integral w (events k) p.last hactive ?_, hc]
  rw [hc]
  exact hpos (k + 1) (by omega)

/-- The product normalizer through time `k` along the deterministic walk. -/
noncomputable def prescribedNormalizer (w : ℂ) (events : ℕ → Bool) (i₀ : ℕ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => prescribedNormalizer w events i₀ k *
      prescribedProfileFactor w (events k) (prescribedWalk events i₀ k)

/-- The exact expected normalized profile under the joint history law is its
initial value times the deterministic product. No nonvanishing assumption is
needed for this expectation identity. -/
theorem prescribedPath_normalized_integral (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N : ℕ)
    (hpos : ∀ j ≤ N, 0 < prescribedWalk events (infectious s₀) j) :
    (∫ p, normalizedActiveWeight w p.last
      ∂kernelPathMeasure (fun j ↦ prescribedStep (events j)) s₀ N) =
      normalizedActiveWeight w s₀ * prescribedNormalizer w events (infectious s₀) N := by
  induction N with
  | zero => simp [kernelPathMeasure, kernelPathLaw, prescribedNormalizer, FinitePath.last, PMF.toMeasure_pure]
  | succ N ih =>
      rw [kernelPathMeasure_integral_succ (fun j ↦ prescribedStep (events j))
        (fun j s ↦ finite_support_prescribedStep (events j) s)]
      simp only [FinitePath.append_last]
      have hmean :
          (fun p : FinitePath N ↦ ∫ s, normalizedActiveWeight w s
            ∂(prescribedStep (events N) p.last).toMeasure) =ᵐ[
              kernelPathMeasure (fun j ↦ prescribedStep (events j)) s₀ N]
          (fun p ↦ normalizedActiveWeight w p.last *
            prescribedProfileFactor w (events N) (prescribedWalk events (infectious s₀) N)) := by
        filter_upwards [ae_mem_support_kernelPathLaw (fun j ↦ prescribedStep (events j)) s₀ N]
          with p hp
        have hc := infectious_kernelPathLaw_prescribed events s₀ N
          (fun j hj ↦ hpos j (by omega)) p hp
        have hactive : p.last.active.Nonempty := by
          apply Finset.card_pos.mp
          change 0 < infectious p.last
          rw [hc]
          exact hpos N (by omega)
        rw [prescribedStep_normalized_integral w (events N) p.last hactive ?_, hc]
        rw [hc]
        exact hpos (N + 1) le_rfl
      rw [integral_congr_ae hmean, integral_mul_const,
        ih (fun j hj ↦ hpos j (by omega)), prescribedNormalizer, mul_assoc]

theorem prescribedNormalizer_ne_zero_of_le (w : ℂ) (events : ℕ → Bool) (i₀ : ℕ)
    {N k : ℕ} (hk : k ≤ N) (hN : prescribedNormalizer w events i₀ N ≠ 0) :
    prescribedNormalizer w events i₀ k ≠ 0 := by
  induction N with
  | zero => simpa only [Nat.eq_zero_of_le_zero hk, prescribedNormalizer] using hN
  | succ N ih =>
      by_cases h : k ≤ N
      · exact ih h (mul_ne_zero_iff.mp hN).1
      · have heq : k = N + 1 := by omega
        simpa only [heq] using hN

/-- Dividing the normalized profile by its deterministic product gives an actual
complex martingale. Only the final product is assumed nonzero, as in the paper;
all the earlier nonvanishing facts follow from it. -/
theorem prescribedPath_profile_martingale (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N : ℕ)
    (hpos : ∀ j ≤ N, 0 < prescribedWalk events (infectious s₀) j)
    (hC : prescribedNormalizer w events (infectious s₀) N ≠ 0) :
    Martingale (fun k p ↦ normalizedActiveWeight w (p.eval k) /
        prescribedNormalizer w events (infectious s₀) (min k N))
      (pathFiltration N) (kernelPathMeasure (fun j ↦ prescribedStep (events j)) s₀ N) := by
  apply kernelPath_martingale (fun j ↦ prescribedStep (events j))
    (fun j s ↦ finite_support_prescribedStep (events j) s) s₀ N
    (fun j s ↦ normalizedActiveWeight w s / prescribedNormalizer w events (infectious s₀) j)
  intro k hk p hp
  have hc := infectious_kernelPathLaw_prescribed events s₀ k
    (fun j hj ↦ hpos j (by omega)) p hp
  have hactive : p.last.active.Nonempty := by
    apply Finset.card_pos.mp
    change 0 < infectious p.last
    rw [hc]
    exact hpos k hk.le
  have hnext : 0 < prescribedActiveCount (events k) (infectious p.last) := by
    rw [hc]
    exact hpos (k + 1) (by omega)
  have hfactor : prescribedProfileFactor w (events k)
      (prescribedWalk events (infectious s₀) k) ≠ 0 :=
    (mul_ne_zero_iff.mp (prescribedNormalizer_ne_zero_of_le w events (infectious s₀)
      (show k + 1 ≤ N by omega) hC)).2
  rw [integral_div, prescribedStep_normalized_integral w (events k) p.last hactive hnext,
    prescribedNormalizer, hc]
  exact mul_div_mul_right _ _ hfactor

end HeightPaper.Model
