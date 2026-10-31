module

public import HeightPaper.StrongProfileStatement
public import HeightPaper.Probability.SourceWeakProfile
public import HeightPaper.Analysis.CompactUniform

/-!
# The exact survival boundary in the strong-profile statement

Extinction exactly at `floor(T*n)` is a vanishing event, weakly uniformly on
the source's compact parameter sets. This transfers an active-state local
profile estimate to the literal non-strict source survival convention.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace HeightPaper

open Model

def strongProfileBoundary (T : ℝ) (n : ℕ) : Set (FinitePath (2 * n + 1)) :=
  {q | ⌊T * n⌋₊ ≤ 2 * (q.eval (2 * n + 1)).vertices - 1 ∧
    ¬(q.eval ⌊T * n⌋₊).active.Nonempty}

theorem strongProfileBoundary_uniform_vanishing {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      (pathMeasure (l / n) n (2 * n + 1)).real (strongProfileBoundary T n) < ε := by
  let p : ℕ → ℝ≥0 → ℕ → ℝ := fun n l _ ↦
    (pathMeasure (l / n) n (2 * n + 1)).real (strongProfileBoundary T n)
  have hh := compact_uniform_tight_of_sequence hI p (fun _ _ _ _ _ ↦ le_rfl) ?_ ε hε
  · obtain ⟨_, N, hN⟩ := hh
    exact ⟨N, hN⟩
  · intro l hl ls hls η hη
    have hreal : Tendsto (fun n ↦ (ls n : ℝ)) atTop (𝓝 (l : ℝ)) :=
      NNReal.continuous_coe.continuousAt.tendsto.comp hls
    have hrates : Tendsto (fun n ↦ ((ls n / n : ℝ≥0) : ℝ) * n) atTop (𝓝 (l : ℝ)) := by
      apply hreal.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp only [NNReal.coe_div, NNReal.coe_natCast, div_mul_cancel₀ _ hnR]
    let δ := 1 - T / fluidExtinctionTime l
    have ht := fluidExtinctionTime_pos (hparams l hl).1
    have hδ : δ ∈ Ioo (0 : ℝ) 1 := by
      dsimp [δ]
      constructor
      · have := (div_lt_one ht).mpr (hparams l hl).2
        linarith
      · have := div_pos hT ht
        linarith
    have he : (1 - δ) * fluidExtinctionTime l = T := by
      dsimp [δ]
      field_simp [ht.ne']
      ring
    have hv := sourceSurvival_cutoff_inactive_tendsto_zero (fun n ↦ ls n / n)
      (hparams l hl).1 hδ hrates
    have hcut (n : ℕ) : sourceCutoff l δ n = ⌊T * n⌋₊ := by
      rw [sourceCutoff, he]
    have hevents (n : ℕ) :
        {q : FinitePath (2 * n + 1) | q.eval (2 * n + 1) ∈ sourceSurvivalEvent l δ n ∧
          ¬(q.eval (sourceCutoff l δ n)).active.Nonempty} = strongProfileBoundary T n := by
      ext q
      change (sourceCutoff l δ n ≤ 2 * (q.eval (2 * n + 1)).vertices - 1 ∧
        ¬(q.eval (sourceCutoff l δ n)).active.Nonempty) ↔ _
      rw [hcut]
      rfl
    have hv' : Tendsto (fun n ↦ p n (ls n) 0) atTop (𝓝 0) := by
      simpa only [hevents] using hv
    exact ⟨0, hv'.eventually (Iio_mem_nhds hη)⟩

/-- All analytic work may be done on terminal activity; this theorem supplies
the source's non-strict survival event without changing any uniform quantifier.
Its active-state estimate remains an explicit proof obligation. -/
theorem uniformStrongProfileStatement_of_active
    (hactive : ∀ I : Set ℝ≥0, IsCompact I → ∀ T > (0 : ℝ),
      ∀ K : Set ℝ, IsCompact K →
      (∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l ∧
        K ⊆ Ioo (0 : ℝ) (profileRoot l)) →
      ∀ ε > (0 : ℝ), ∃ R ≥ (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
        (evolve (l / n) n ⌊T * n⌋₊).toMeasure.real
          {s | s.active.Nonempty ∧ s ∈ strongProfileStateBad l K n R} < ε) :
    UniformStrongProfileStatement := by
  intro I hI T hT K hK hparams ε hε
  have heps : 0 < ε / 2 := half_pos hε
  obtain ⟨R, hR, N₁, hN₁⟩ := hactive I hI T hT K hK hparams (ε / 2) heps
  obtain ⟨N₂, hN₂⟩ := strongProfileBoundary_uniform_vanishing hI hT
    (fun l hl ↦ ⟨(hparams l hl).1, (hparams l hl).2.1⟩) heps
  refine ⟨R, hR, max N₁ N₂, ?_⟩
  intro n hn l hl
  have hA := hN₁ n (by omega) l hl
  have hB := hN₂ n (by omega) l hl
  have hH : ⌊T * n⌋₊ ≤ 2 * n + 1 := by
    let δ := 1 - T / fluidExtinctionTime l
    have ht := fluidExtinctionTime_pos (hparams l hl).1
    have hδ : δ ∈ Ioo (0 : ℝ) 1 := by
      dsimp [δ]
      constructor
      · have := (div_lt_one ht).mpr (hparams l hl).2.1
        linarith
      · have := div_pos hT ht
        linarith
    have he : (1 - δ) * fluidExtinctionTime l = T := by
      dsimp [δ]
      field_simp [ht.ne']
      ring
    simpa only [sourceCutoff, he] using sourceCutoff_le_steps (hparams l hl).1 hδ n
  rw [← pathMeasure_event_at (l / n) n (2 * n + 1) ⌊T * n⌋₊ hH] at hA
  change (pathMeasure (l / n) n (2 * n + 1)).real
    {q | (q.eval ⌊T * n⌋₊).active.Nonempty ∧
      q.eval ⌊T * n⌋₊ ∈ strongProfileStateBad l K n R} < ε / 2 at hA
  have hsub : strongProfileBad l T K n R ⊆
      {q | (q.eval ⌊T * n⌋₊).active.Nonempty ∧
        q.eval ⌊T * n⌋₊ ∈ strongProfileStateBad l K n R} ∪ strongProfileBoundary T n := by
    intro q hq
    by_cases ha : (q.eval ⌊T * n⌋₊).active.Nonempty
    · exact Or.inl ⟨ha, hq.2⟩
    · exact Or.inr ⟨hq.1, ha⟩
  have hbound := (measureReal_mono (μ := pathMeasure (l / n) n (2 * n + 1)) hsub).trans
    (measureReal_union_le _ _)
  linarith

end HeightPaper
