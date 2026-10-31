module

public import HeightPaper.Model.PrescribedPath

/-!
# Profile martingales after a deterministic cutoff

The process remains on its original whole-history probability space. Shifting
the filtration retains the random prefix, and allows earlier product factors
to vanish, exactly as in the paper's cutoff construction.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace HeightPaper.Model

/-- The full-history filtration, reindexed from time `j`. -/
def pathFiltrationFrom (N j : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (FinitePath N)) where
  seq k := pathFiltration N (j + k)
  mono' := fun _ _ h ↦ (pathFiltration N).mono (Nat.add_le_add_left h j)
  le' := fun k ↦ (pathFiltration N).le (j + k)

/-- A kernel martingale started after a cutoff, on the original history law.
The prefix before the cutoff remains random and part of the filtration. -/
theorem kernelPath_martingale_from {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (K : ℕ → State → PMF State) (hK : ∀ k s, (K k s).support.Finite)
    (s₀ : State) (N j : ℕ) (F : ℕ → State → E)
    (hF : ∀ k, j ≤ k → k < N → ∀ p ∈ (kernelPathLaw K s₀ k).support,
      (∫ s, F (k + 1) s ∂(K k p.last).toMeasure) = F k p.last) :
    Martingale (fun k p ↦ F (min (j + k) N) (p.eval (j + k)))
      (pathFiltrationFrom N j) (kernelPathMeasure K s₀ N) := by
  have hadapt : StronglyAdapted (pathFiltrationFrom N j)
      (fun k p ↦ F (min (j + k) N) (p.eval (j + k))) := by
    intro k
    apply Measurable.stronglyMeasurable
    intro A hA
    refine ⟨(fun p : FinitePath (j + k) ↦ F (min (j + k) N) p.last) ⁻¹' A, trivial, ?_⟩
    ext p
    simp only [Set.mem_preimage, FinitePath.prefixAt_last]
  have hint (k : ℕ) : Integrable (fun p ↦ F (min (j + k) N) (p.eval (j + k)))
      (kernelPathMeasure K s₀ N) := integrable_kernelPathMeasure K hK s₀ N _
  apply martingale_nat hadapt hint
  intro k
  by_cases hk : j + k < N
  · have hk' : j + (k + 1) ≤ N := by omega
    simpa only [Nat.min_eq_left hk.le, Nat.min_eq_left hk', Nat.add_assoc,
      pathFiltrationFrom] using
      kernelPath_condExp (E := E) K hK s₀ N (j + k) hk (F (j + k + 1)) (F (j + k))
        (hF (j + k) (by omega) hk)
  · have hkN : N ≤ j + k := by omega
    have hkN' : N ≤ j + (k + 1) := by omega
    have heq : (fun p : FinitePath N ↦ F (min (j + (k + 1)) N) (p.eval (j + (k + 1)))) =
        (fun p ↦ F (min (j + k) N) (p.eval (j + k))) := by
      funext p
      simp only [Nat.min_eq_right hkN, Nat.min_eq_right hkN',
        FinitePath.eval_of_ge _ hkN, FinitePath.eval_of_ge _ hkN']
    rw [heq, condExp_of_stronglyMeasurable (pathFiltrationFrom N j |>.le k)
      (hadapt k) (hint k)]

/-- The source's product from events `j` through `k - 1`; event `i` here is
indexed by the transition from time `i` to time `i + 1`. -/
noncomputable def prescribedNormalizerFrom (w : ℂ) (events : ℕ → Bool) (i₀ j k : ℕ) : ℂ :=
  ∏ i ∈ Finset.Ico j k, prescribedProfileFactor w (events i) (prescribedWalk events i₀ i)

@[simp] theorem prescribedNormalizerFrom_self (w : ℂ) (events : ℕ → Bool) (i₀ j : ℕ) :
    prescribedNormalizerFrom w events i₀ j j = 1 := by
  simp [prescribedNormalizerFrom]

theorem prescribedNormalizerFrom_succ (w : ℂ) (events : ℕ → Bool) (i₀ : ℕ)
    {j k : ℕ} (hjk : j ≤ k) :
    prescribedNormalizerFrom w events i₀ j (k + 1) =
      prescribedNormalizerFrom w events i₀ j k *
        prescribedProfileFactor w (events k) (prescribedWalk events i₀ k) := by
  exact Finset.prod_Ico_succ_top hjk _

/-- The paper's shifted complex profile martingale, retaining the entire random
past on the same full-history probability space. Nonvanishing is required only
for the product after `j`, allowing zero factors before the cutoff. -/
theorem prescribedPath_shifted_profile_martingale (w : ℂ) (events : ℕ → Bool)
    (s₀ : State) (N j : ℕ)
    (hpos : ∀ i ≤ N, 0 < prescribedWalk events (infectious s₀) i)
    (hC : prescribedNormalizerFrom w events (infectious s₀) j N ≠ 0) :
    Martingale (fun k p ↦ normalizedActiveWeight w (p.eval (j + k)) /
        prescribedNormalizerFrom w events (infectious s₀) j (min (j + k) N))
      (pathFiltrationFrom N j)
      (kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ N) := by
  apply kernelPath_martingale_from (fun i ↦ prescribedStep (events i))
    (fun i s ↦ finite_support_prescribedStep (events i) s) s₀ N j
    (fun i s ↦ normalizedActiveWeight w s / prescribedNormalizerFrom w events (infectious s₀) j i)
  intro k hjk hk p hp
  have hc := infectious_kernelPathLaw_prescribed events s₀ k
    (fun i hi ↦ hpos i (by omega)) p hp
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
    Finset.prod_ne_zero_iff.mp hC k (Finset.mem_Ico.mpr ⟨hjk, hk⟩)
  rw [integral_div, prescribedStep_normalized_integral w (events k) p.last hactive hnext,
    prescribedNormalizerFrom_succ w events (infectious s₀) hjk, hc]
  exact mul_div_mul_right _ _ hfactor

end HeightPaper.Model
