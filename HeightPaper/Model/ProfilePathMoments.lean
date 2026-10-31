module

public import HeightPaper.Model.PrescribedPath
public import HeightPaper.Model.ProfileMoments
public import HeightPaper.Model.KernelPathMarginal

/-! # Profile increment moments under the actual prescribed-event kernels -/

@[expose] public section

open MeasureTheory

namespace HeightPaper.Model

/-- Integrating the prescribed-event kernel is exactly integrating the uniformly
chosen active vertex. This applies equally to real moments and complex profiles. -/
theorem prescribedStep_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (birth : Bool) (s : State) (h : s.active.Nonempty) (f : State → E) :
    (∫ t, f t ∂(prescribedStep birth s).toMeasure) =
      ∫ v, f (prescribedUpdate birth s v) ∂(uniformActive s h).toMeasure := by
  rw [prescribedStep, dite_eq_left h,
    ← PMF.toMeasure_map _ _ (measurable_of_countable _),
    integral_map_of_stronglyMeasurable (measurable_of_countable _)
      (measurable_state _).stronglyMeasurable]

/-- The deterministic coefficient of the centered uniform-parent draw in the
normalized martingale increment. -/
noncomputable def prescribedIncrementCoeff (w C : ℂ) (birth : Bool) (i : ℕ) : ℂ :=
  if birth then w / (C * ((i : ℂ) + w)) else -1 / (C * ((i : ℂ) - 1))

/-- The actual one-step p-th increment moment. The random profile on the right
is retained explicitly so it can be averaged using the exact product identity. -/
theorem prescribedStep_profile_increment_moment_le (w C : ℂ) (birth : Bool) (s : State)
    (h : s.active.Nonempty) {p : ℝ} (hp : 1 ≤ p)
    (hnext : 0 < prescribedActiveCount birth (infectious s)) (hC : C ≠ 0)
    (hfactor : prescribedProfileFactor w birth (infectious s) ≠ 0) :
    (∫ t, ‖normalizedActiveWeight w t / (C * prescribedProfileFactor w birth (infectious s)) -
        normalizedActiveWeight w s / C‖ ^ p ∂(prescribedStep birth s).toMeasure) ≤
      ‖prescribedIncrementCoeff w C birth (infectious s)‖ ^ p * ((2 : ℝ) ^ p *
        (activeWeight (‖w‖ ^ p) s / (infectious s : ℝ))) := by
  rw [prescribedStep_integral birth s h]
  cases birth with
  | false =>
      have hI : 1 < infectious s := by
        simpa only [prescribedActiveCount, Bool.false_eq_true, ↓reduceIte, Nat.sub_pos_iff_lt]
          using hnext
      simpa only [prescribedUpdate, prescribedProfileFactor, prescribedIncrementCoeff,
        Bool.false_eq_true, ↓reduceIte, mul_one] using
        uniform_recover_martingale_increment_moment_le w C s h hp hI hC
  | true =>
      have hip : (infectious s : ℂ) + 1 ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero (infectious s)
      have heq : prescribedProfileFactor w true (infectious s) =
          ((infectious s : ℂ) + w) / ((infectious s : ℂ) + 1) := by
        simp only [prescribedProfileFactor, ↓reduceIte]
        field_simp
        ring
      have hIw : (infectious s : ℂ) + w ≠ 0 := by
        intro hz
        apply hfactor
        rw [heq, hz, zero_div]
      exact uniform_infect_martingale_increment_moment_le w C s h hp hC hIw

/-- The complex normalized profile at a real weight is the corresponding real
finite average, embedded in the complex numbers. -/
theorem normalizedActiveWeight_ofReal (x : ℝ) (s : State) :
    normalizedActiveWeight (x : ℂ) s =
      ((activeWeight x s / (infectious s : ℝ) : ℝ) : ℂ) := by
  simp [normalizedActiveWeight, activeWeight]

/-- The product identity also supplies exactly the real expected positive
profile needed in the averaged increment estimate. -/
theorem prescribedPath_realProfile_integral (x : ℝ) (events : ℕ → Bool)
    (s₀ : State) (N : ℕ)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i) :
    (∫ p, activeWeight x p.last / (infectious p.last : ℝ)
      ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N) =
      (normalizedActiveWeight (x : ℂ) s₀ * prescribedNormalizer (x : ℂ) events
        (infectious s₀) N).re := by
  have hint := integrable_kernelPathMeasure (fun i ↦ prescribedStep (events i))
    (fun i s ↦ finite_support_prescribedStep (events i) s) s₀ N
    (fun p ↦ normalizedActiveWeight (x : ℂ) p.last)
  have he := congrArg Complex.re (prescribedPath_normalized_integral (x : ℂ) events s₀ N hpos)
  have hre := integral_re hint
  simp only [RCLike.re_eq_complex_re] at hre
  rw [← hre] at he
  simpa only [normalizedActiveWeight_ofReal, Complex.ofReal_re] using he

/-- Reachable state marginals have the prescribed active count. -/
theorem infectious_prescribedKernelEvolve (events : ℕ → Bool) (s₀ : State) (k : ℕ)
    (hpos : ∀ j < k, 0 < prescribedWalk events (infectious s₀) j)
    (s : State)
    (hs : s ∈ (FinitePMF.kernelEvolve (PMF.pure s₀)
      (fun j ↦ prescribedStep (events j)) k).support) :
    infectious s = prescribedWalk events (infectious s₀) k := by
  rw [← kernelPathLaw_map_last] at hs
  obtain ⟨q, hq, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
  exact infectious_kernelPathLaw_prescribed events s₀ k hpos q hq

/-- The real expected profile, now stated for the iterated state marginal. -/
theorem prescribedKernelEvolve_realProfile_integral (x : ℝ) (events : ℕ → Bool)
    (s₀ : State) (N : ℕ)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i) :
    (∫ s, activeWeight x s / (infectious s : ℝ)
      ∂(FinitePMF.kernelEvolve (PMF.pure s₀) (fun i ↦ prescribedStep (events i)) N).toMeasure) =
      (normalizedActiveWeight (x : ℂ) s₀ * prescribedNormalizer (x : ℂ) events
        (infectious s₀) N).re := by
  rw [← kernelPathLaw_map_last,
    ← PMF.toMeasure_map _ _ (FinitePath.measurable _),
    integral_map_of_stronglyMeasurable (FinitePath.measurable _)
      (measurable_state _).stronglyMeasurable]
  exact prescribedPath_realProfile_integral x events s₀ N hpos

/-- Averaging the true conditional increment bound removes the random profile
using its exact product expectation. This is the input to cumulative martingale
moment bounds; no maximum over possible trees is assumed. -/
theorem prescribedKernelEvolve_increment_moment_le (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N k : ℕ) (hk : k < N) {p : ℝ} (hp : 1 ≤ p)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizer w events (infectious s₀) N ≠ 0) :
    (∫ s, ∫ t,
      ‖normalizedActiveWeight w t / prescribedNormalizer w events (infectious s₀) (k + 1) -
        normalizedActiveWeight w s / prescribedNormalizer w events (infectious s₀) k‖ ^ p
        ∂(prescribedStep (events k) s).toMeasure
        ∂(FinitePMF.kernelEvolve (PMF.pure s₀) (fun i ↦ prescribedStep (events i)) k).toMeasure) ≤
      (‖prescribedIncrementCoeff w (prescribedNormalizer w events (infectious s₀) k)
        (events k) (prescribedWalk events (infectious s₀) k)‖ ^ p * (2 : ℝ) ^ p) *
        (normalizedActiveWeight ((‖w‖ ^ p : ℝ) : ℂ) s₀ *
          prescribedNormalizer ((‖w‖ ^ p : ℝ) : ℂ) events (infectious s₀) k).re := by
  have hμ := FinitePMF.kernelEvolve_support_finite (PMF.pure s₀)
    (fun i ↦ prescribedStep (events i))
    (by rw [PMF.support_pure]; exact Set.finite_singleton _)
    (fun i s ↦ finite_support_prescribedStep (events i) s) k
  have hCk := prescribedNormalizer_ne_zero_of_le w events (infectious s₀) hk.le hC
  have hfactor := (mul_ne_zero_iff.mp
    (prescribedNormalizer_ne_zero_of_le w events (infectious s₀)
      (show k + 1 ≤ N by omega) hC)).2
  calc
    _ ≤ ∫ s,
        (‖prescribedIncrementCoeff w (prescribedNormalizer w events (infectious s₀) k)
          (events k) (prescribedWalk events (infectious s₀) k)‖ ^ p * (2 : ℝ) ^ p) *
          (activeWeight (‖w‖ ^ p) s / (infectious s : ℝ))
        ∂(FinitePMF.kernelEvolve (PMF.pure s₀) (fun i ↦ prescribedStep (events i)) k).toMeasure := by
      apply integral_mono_ae (FinitePMF.integrable_of_finite_support _ hμ _)
        (FinitePMF.integrable_of_finite_support _ hμ _)
      apply FinitePMF.ae_of_forall_mem_support
      intro s hs
      have hc := infectious_prescribedKernelEvolve events s₀ k
        (fun i hi ↦ hpos i (by omega)) s hs
      have hactive : s.active.Nonempty := by
        apply Finset.card_pos.mp
        change 0 < infectious s
        rw [hc]
        exact hpos k hk.le
      have hnext : 0 < prescribedActiveCount (events k) (infectious s) := by
        rw [hc]
        exact hpos (k + 1) (by omega)
      have hb := prescribedStep_profile_increment_moment_le w
        (prescribedNormalizer w events (infectious s₀) k) (events k) s hactive hp
        hnext hCk (by simpa only [hc] using hfactor)
      simpa only [prescribedNormalizer, hc, mul_assoc] using hb
    _ = _ := by
      rw [integral_const_mul,
        prescribedKernelEvolve_realProfile_integral (‖w‖ ^ p) events s₀ k
          (fun i hi ↦ hpos i (by omega))]

end HeightPaper.Model
