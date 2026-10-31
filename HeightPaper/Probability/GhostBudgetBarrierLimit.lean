module

public import HeightPaper.Probability.GhostStoppedComparison
public import HeightPaper.Analysis.FluidBarrier

/-!
# Staying above a small susceptible fraction after source extinction

An active-padded epidemic has the same susceptible budget as the continued
count chain. A sufficiently small fraction places its harmonic stopping
barrier beyond any prescribed finite macroscopic time. The already proved
stopped-martingale variance estimate then makes crossing improbable.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology NNReal

namespace HeightPaper.Model

theorem exists_ghostBudget_fluidBarrier (l T : ℝ)
    (hl : 0 < l) (hT : 0 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ T < fluidBarrier l c := by
  let c := Real.exp (-(l * (T + 3)))
  have hc : 0 < c := Real.exp_pos _
  have hc1 : c < 1 := by
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  refine ⟨c, hc, hc1, ?_⟩
  unfold fluidBarrier
  have hl0 : l ≠ 0 := hl.ne'
  dsimp [c]
  rw [Real.log_exp]
  have he := Real.exp_pos (-(l * (T + 3)))
  field_simp
  nlinarith

theorem ghostBudget_stopped_below_fluidThreshold_tendsto_zero
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ)
    {l T c : ℝ} (hl : 1 < l) (hc : 0 < c) (hc1 : c < 1)
    (hbar : T < fluidBarrier l c)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T)) :
    Tendsto (fun n ↦
      (stoppedCountLaw (rates n) (fluidThreshold c n)
        (ghostBudgetStart n (horizon n)) (horizon n)).toMeasure.real
          {s | s.susceptible < fluidThreshold c n}) atTop (𝓝 0) := by
  have hl0 : 0 < l := zero_lt_one.trans hl
  have hlc : 0 < l * c := mul_pos hl0 hc
  have hβ : 0 < fluidBarrier l c - T := sub_pos.mpr hbar
  have hpressure := tendsto_fluidThreshold_pressure rates hc.le hrates
  have hbarrier := tendsto_stoppingBarrier_fraction rates hl0.ne' hc hrates
  have hdiff : Tendsto (fun n ↦
      (stoppingBarrier (rates n) n (fluidThreshold c n) - horizon n) / n)
      atTop (𝓝 (fluidBarrier l c - T)) := by
    apply (hbarrier.sub hhorizon).congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    ring
  let bound : ℕ → ℝ := fun n ↦ (horizon n : ℝ) /
    ((rates n : ℝ) * fluidThreshold c n *
      (stoppingBarrier (rates n) n (fluidThreshold c n) - horizon n) ^ 2)
  have hbound : Tendsto bound atTop (𝓝 0) := by
    have ht := (hhorizon.div (hpressure.mul (hdiff.pow 2))
      (mul_ne_zero hlc.ne' (pow_ne_zero _ hβ.ne'))).mul
      (tendsto_one_div_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    dsimp [bound]
    field_simp
  have hevent : ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 0 < (rates n : ℝ) * fluidThreshold c n ∧
        0 < stoppingBarrier (rates n) n (fluidThreshold c n) - horizon n ∧
        fluidThreshold c n ≤ n := by
    filter_upwards [eventually_gt_atTop 0,
      hpressure.eventually (Ioi_mem_nhds hlc),
      hdiff.eventually (Ioi_mem_nhds hβ),
      eventually_fluidThreshold_le hc.le hc1] with n hn hp hb hth
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hb' : (0 : ℝ) <
        stoppingBarrier (rates n) n (fluidThreshold c n) - horizon n := by
      exact (div_pos_iff.mp hb).resolve_right (by intro h; linarith) |>.1
    exact ⟨hn, hp, hb', hth⟩
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hbound
  filter_upwards [hevent] with n hn
  have hr : 0 < rates n := by
    have hprod := hn.2.1
    have hth : (0 : ℝ) ≤ fluidThreshold c n := Nat.cast_nonneg _
    have hr0 : (0 : ℝ) < (rates n : ℝ) := by nlinarith
    exact_mod_cast hr0
  exact ghostBudget_stopped_below_probability_le (rates n) (fluidThreshold c n)
    n (horizon n) (horizon n) hr (fluidThreshold_pos _ _) hn.2.2.2 hn.2.2.1

end HeightPaper.Model
