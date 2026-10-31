module

public import HeightPaper.Model.ProfilePathMoments
public import HeightPaper.Model.RealNormalizer

/-!
# The total tree profile and its height bound

Recovered vertices remain in the total profile. Its expectation along a
prescribed event word is the sum of the expected contributions of births.
This provides a first-moment upper-height route that does not require a
nonvanishing profile martingale.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.Model

/-- Generating function of all vertices, including recovered vertices. -/
def totalWeight {R : Type*} [CommSemiring R] (w : R) (s : State) : R :=
  ∑ v : Fin s.vertices, w ^ s.tree.depth v

@[simp] theorem totalWeight_initial {R : Type*} [CommSemiring R] (w : R) (n : ℕ) :
    totalWeight w (initial n) = 1 := by
  change (∑ _ : Fin 1, w ^ (0 : ℕ)) = 1
  simp

@[simp] theorem totalWeight_recover {R : Type*} [CommSemiring R] (w : R)
    (s : State) (v : Fin s.vertices) : totalWeight w (recover s v) = totalWeight w s := rfl

theorem totalWeight_infect {R : Type*} [CommSemiring R] (w : R)
    (s : State) (v : Fin s.vertices) :
    totalWeight w (infect s v) = totalWeight w s + w * w ^ s.tree.depth v := by
  unfold totalWeight
  change (∑ u : Fin (s.vertices + 1), w ^ (s.tree.attach v).depth u) = _
  rw [Fin.sum_univ_castSucc]
  simp only [Tree.depth_attach_old, Tree.depth_attach_new, pow_succ, mul_comm w]

theorem totalWeight_nonneg {w : ℝ} (hw : 0 ≤ w) (s : State) :
    0 ≤ totalWeight w s := Finset.sum_nonneg fun _ _ ↦ pow_nonneg hw _

theorem pow_height_le_totalWeight {w : ℝ} (hw : 0 ≤ w) (s : State) :
    w ^ height s ≤ totalWeight w s := by
  have hne : (Finset.univ : Finset (Fin s.vertices)).Nonempty :=
    ⟨⟨0, s.tree.size_pos⟩, Finset.mem_univ _⟩
  obtain ⟨v, hv, heq⟩ := Finset.exists_mem_eq_sup Finset.univ hne s.tree.depth
  change w ^ (Finset.univ.sup s.tree.depth) ≤ _
  rw [heq]
  exact Finset.single_le_sum (fun u _ ↦ pow_nonneg hw (s.tree.depth u)) hv

/-- Each infection adds its parent's profile contribution; freezing adds zero. -/
theorem prescribedStep_totalWeight_integral (w : ℝ) (birth : Bool) (s : State)
    (ha : s.active.Nonempty) :
    (∫ t, totalWeight w t ∂(prescribedStep birth s).toMeasure) =
      totalWeight w s + (if birth then w else 0) *
        (activeWeight w s / (infectious s : ℝ)) := by
  rw [prescribedStep_integral birth s ha, uniformActive_integral_real]
  have hi : (infectious s : ℝ) ≠ 0 := by exact_mod_cast ha.card_pos.ne'
  cases birth with
  | false =>
      simp only [prescribedUpdate, Bool.false_eq_true, ↓reduceIte, totalWeight_recover,
        Finset.sum_const, nsmul_eq_mul, zero_mul, add_zero]
      change (infectious s : ℝ) * totalWeight w s / infectious s = totalWeight w s
      field_simp
  | true =>
      simp only [prescribedUpdate, ↓reduceIte, totalWeight_infect,
        Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      change ((infectious s : ℝ) * totalWeight w s + w * activeWeight w s) /
        infectious s = _
      field_simp

/-- Exact total-profile expectation for the actual prescribed history law. -/
theorem prescribedPath_totalWeight_integral (w : ℝ) (events : ℕ → Bool)
    (s₀ : State) (N : ℕ)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i) :
    (∫ p, totalWeight w p.last
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N) =
      totalWeight w s₀ + ∑ k ∈ Finset.range N,
        (if events k then w else 0) *
          (normalizedActiveWeight (w : ℂ) s₀ *
            prescribedNormalizer (w : ℂ) events (infectious s₀) k).re := by
  induction N with
  | zero =>
      simp [kernelPathMeasure, kernelPathLaw, FinitePath.last, PMF.toMeasure_pure]
  | succ N ih =>
      rw [kernelPathMeasure_integral_succ (fun i ↦ prescribedStep (events i))
        (fun i s ↦ finite_support_prescribedStep (events i) s)]
      simp only [FinitePath.append_last]
      have heq :
          (fun p : FinitePath N ↦ ∫ t, totalWeight w t
            ∂(prescribedStep (events N) p.last).toMeasure) =ᵐ[
              kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N]
          (fun p ↦ totalWeight w p.last + (if events N then w else 0) *
            (activeWeight w p.last / (infectious p.last : ℝ))) := by
        filter_upwards [ae_mem_support_kernelPathLaw (fun i ↦ prescribedStep (events i)) s₀ N]
          with p hp
        have hc := infectious_kernelPathLaw_prescribed events s₀ N
          (fun i hi ↦ hpos i (by omega)) p hp
        have ha : p.last.active.Nonempty := by
          apply Finset.card_pos.mp
          change 0 < infectious p.last
          rw [hc]
          exact hpos N (by omega)
        exact prescribedStep_totalWeight_integral w (events N) p.last ha
      have hint (f : FinitePath N → ℝ) := integrable_kernelPathMeasure
        (fun i ↦ prescribedStep (events i))
        (fun i s ↦ finite_support_prescribedStep (events i) s) s₀ N f
      rw [integral_congr_ae heq, integral_add (hint _) (hint _), integral_const_mul,
        prescribedPath_realProfile_integral w events s₀ N (fun i hi ↦ hpos i (by omega)),
        ih (fun i hi ↦ hpos i (by omega)), Finset.sum_range_succ, add_assoc]

/-- First-moment upper bound on the height of the entire tree. -/
theorem prescribedPath_height_tail_le (w : ℝ) (hw : 1 ≤ w) (events : ℕ → Bool)
    (s₀ : State) (N h : ℕ)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i) :
    (kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N).real
      {p | h ≤ height p.last} ≤
      (totalWeight w s₀ + ∑ k ∈ Finset.range N,
        (if events k then w else 0) *
          (normalizedActiveWeight (w : ℂ) s₀ *
            prescribedNormalizer (w : ℂ) events (infectious s₀) k).re) / w ^ h := by
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hi := integrable_kernelPathMeasure (fun i ↦ prescribedStep (events i))
    (fun i s ↦ finite_support_prescribedStep (events i) s) s₀ N
    (fun p ↦ totalWeight w p.last)
  have hb := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun p : FinitePath N ↦ totalWeight_nonneg hw0.le p.last) hi (w ^ h)
  rw [prescribedPath_totalWeight_integral w events s₀ N hpos] at hb
  calc
    _ ≤ (kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N).real
        {p | w ^ h ≤ totalWeight w p.last} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro p hp
      exact (pow_le_pow_right₀ hw hp).trans (pow_height_le_totalWeight hw0.le p.last)
    _ ≤ _ := (le_div_iff₀ (pow_pos hw0 h)).mpr (by simpa only [mul_comm] using hb)

/-- For a single initial root and `w ≥ 1`, the final real normalizer bounds
all earlier expected birth contributions. -/
theorem prescribedPath_totalWeight_integral_le (w : ℝ) (hw : 1 ≤ w)
    (events : ℕ → Bool) (n N : ℕ)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events 1 i) :
    (∫ p, totalWeight w p.last
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N) ≤
      1 + w * N * realNormalizer w events 1 N := by
  rw [prescribedPath_totalWeight_integral w events (initial n) N (by simpa using hpos)]
  simp only [totalWeight_initial, normalizedActiveWeight, activeWeight_initial,
    infectious_initial, Nat.cast_one, div_one, one_mul, prescribedNormalizer_ofReal,
    Complex.ofReal_re]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _k ∈ Finset.range N, w * realNormalizer w events 1 N := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases he : events k = true
      · simp only [he, ↓reduceIte]
        exact mul_le_mul_of_nonneg_left
          (realNormalizer_mono hw events 1 (Finset.mem_range.mp hk).le)
          (zero_le_one.trans hw)
      · simpa [he] using mul_nonneg (zero_le_one.trans hw)
          (zero_le_one.trans (one_le_realNormalizer hw events 1 N))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- A compact upper-height bound using only the final product normalizer. -/
theorem prescribedPath_height_tail_le_realNormalizer (w : ℝ) (hw : 1 ≤ w)
    (events : ℕ → Bool) (n N h : ℕ)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events 1 i) :
    (kernelPathMeasure (fun i ↦ prescribedStep (events i)) (initial n) N).real
      {p | h ≤ height p.last} ≤ (1 + w * N * realNormalizer w events 1 N) / w ^ h := by
  have hb := prescribedPath_height_tail_le w hw events (initial n) N h (by simpa using hpos)
  rw [← prescribedPath_totalWeight_integral w events (initial n) N (by simpa using hpos)] at hb
  exact hb.trans (div_le_div_of_nonneg_right
    (prescribedPath_totalWeight_integral_le w hw events n N hpos)
    (pow_nonneg (zero_le_one.trans hw) h))

end HeightPaper.Model
