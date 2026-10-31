module

public import HeightPaper.Probability.FiniteSaddleIntegralAmplitude
public import HeightPaper.Analysis.FiniteSaddleLogIdentity

/-! # The logarithmic strong profile estimate under the coupled law -/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace HeightPaper.CountCoupling

open Model

/-- The exact strong-profile bad event is rare under the genuine joint
birth-parent coupling at each fixed epidemic parameter. This includes zero
profile mass, exact lattice heights, and the logarithmic Gaussian correction. -/
theorem finiteStrongProfile_coupled_tight {l : ℝ≥0} (hl : 1 < (l : ℝ))
    {T : ℝ} (hT : 0 < T) (hText : T < fluidExtinctionTime l)
    {K : Set ℝ} (hK : IsCompact K) (hKd : K ⊆ Ioo 0 (profileRoot l))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R ≥ (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
      birthParentLaw.real {q | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n q.1 i) ∧
        coupledTreeState l n q ⌊T * n⌋₊ ∈ strongProfileStateBad l K n R} < δ := by
  by_cases hKne : K.Nonempty
  swap
  · refine ⟨0, le_rfl, 0, ?_⟩
    intro n hn
    have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    simp [strongProfileStateBad, he, hδ]
  obtain ⟨xmin, hxmin, hmin⟩ := hK.exists_isLeast hKne
  obtain ⟨xmax, hxmax, hmax⟩ := hK.exists_isGreatest hKne
  let θmin : ℝ := growthFactor l * Real.exp xmin
  let θmax : ℝ := growthFactor l * Real.exp xmax
  have hθmin : 0 < θmin := mul_pos (growthFactor_pos hl) (Real.exp_pos xmin)
  have hθmax : 0 < θmax := mul_pos (growthFactor_pos hl) (Real.exp_pos xmax)
  have hθbounds : ∀ x ∈ K,
      θmin ≤ growthFactor l * Real.exp x ∧
        growthFactor l * Real.exp x ≤ θmax := by
    intro x hx
    exact ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hmin hx))
      (growthFactor_pos hl).le,
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hmax hx))
      (growthFactor_pos hl).le⟩
  obtain ⟨c, hc, B, hB, NA, hamp⟩ :=
    finiteSaddle_compact_integral_amplitude_tight hl hT hText hK hKne hKd hδ
  let low : ℝ := Real.log c - Real.log (2 * Real.pi) -
    (1 / 2 : ℝ) * Real.log (θmax / 2)
  let high : ℝ := Real.log B - Real.log (2 * Real.pi) -
    (1 / 2 : ℝ) * Real.log (θmin / 2)
  let R : ℝ := max |low| |high| + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nlog, hNlog⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop 1)
  refine ⟨R, hR, max NA Nlog, ?_⟩
  intro n hn
  let H : ℕ := ⌊T * n⌋₊
  let A : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ x ∈ K, ∃ k : ℕ,
        (k : ℝ) = growthFactor l * Real.exp x * Real.log n ∧
        (‖(Real.sqrt (Real.log n * (growthFactor l * Real.exp x) / 2) : ℂ) *
          (∫ v : ℝ in -Real.pi..Real.pi,
            finiteSaddleIntegrandAtScale l H (Real.log n) x
              (coupledTreeHistory l n H q) v)‖ < c ∨
        B < ‖(Real.sqrt (Real.log n * (growthFactor l * Real.exp x) / 2) : ℂ) *
          (∫ v : ℝ in -Real.pi..Real.pi,
            finiteSaddleIntegrandAtScale l H (Real.log n) x
              (coupledTreeHistory l n H q) v)‖)}
  have hA : birthParentLaw.real A < δ := hamp n ((le_max_left _ _).trans hn)
  have ha : 0 < Real.log n := zero_lt_one.trans_le (hNlog n ((le_max_right _ _).trans hn))
  have hsub : {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      coupledTreeState l n q H ∈ strongProfileStateBad l K n R} ⊆ A := by
    rintro q ⟨hs, hbad⟩
    change ∃ x ∈ K, ∃ k : ℕ,
      (k : ℝ) = growthFactor l * Real.exp x * Real.log n ∧
      (normalizedActiveProfile (coupledTreeState l n q H) k = 0 ∨
        R < |Real.log (normalizedActiveProfile (coupledTreeState l n q H) k) -
          strongProfileLogScale l n x|) at hbad
    obtain ⟨x, hx, k, hk, hprofileBad⟩ := hbad
    by_contra hnot
    let Z : ℂ := (Real.sqrt (Real.log n * (growthFactor l * Real.exp x) / 2) : ℂ) *
      (∫ v : ℝ in -Real.pi..Real.pi,
        finiteSaddleIntegrandAtScale l H (Real.log n) x
          (coupledTreeHistory l n H q) v)
    have hZlo : c ≤ ‖Z‖ := by
      apply le_of_not_gt
      intro hh
      exact hnot ⟨hs, x, hx, k, hk, Or.inl hh⟩
    have hZhi : ‖Z‖ ≤ B := by
      apply le_of_not_gt
      intro hh
      exact hnot ⟨hs, x, hx, k, hk, Or.inr hh⟩
    have hZpos : 0 < ‖Z‖ := hc.trans_le hZlo
    have hθ : 0 < growthFactor l * Real.exp x :=
      mul_pos (growthFactor_pos hl) (Real.exp_pos x)
    have hident := coupled_profile_log_saddle_identity l n H k q x ha hθ hk hZpos
    have hθlo : θmin / 2 ≤ (growthFactor l * Real.exp x) / 2 := by
      linarith [(hθbounds x hx).1]
    have hθhi : (growthFactor l * Real.exp x) / 2 ≤ θmax / 2 := by
      linarith [(hθbounds x hx).2]
    have hlogZlo : Real.log c ≤ Real.log ‖Z‖ := Real.log_le_log hc hZlo
    have hlogZhi : Real.log ‖Z‖ ≤ Real.log B := Real.log_le_log hZpos hZhi
    have hlogθlo : Real.log (θmin / 2) ≤
        Real.log ((growthFactor l * Real.exp x) / 2) :=
      Real.log_le_log (by positivity) hθlo
    have hlogθhi : Real.log ((growthFactor l * Real.exp x) / 2) ≤
        Real.log (θmax / 2) :=
      Real.log_le_log (by positivity) hθhi
    have hElo : low ≤ Real.log (normalizedActiveProfile
        (coupledTreeState l n q H) k) - strongProfileLogScale l n x := by
      rw [hident.2]
      dsimp [low]
      linarith
    have hEhi : Real.log (normalizedActiveProfile
        (coupledTreeState l n q H) k) - strongProfileLogScale l n x ≤ high := by
      rw [hident.2]
      dsimp [high]
      linarith
    have habs : |Real.log (normalizedActiveProfile
        (coupledTreeState l n q H) k) - strongProfileLogScale l n x| ≤ R := by
      apply abs_le.mpr
      constructor
      · have hmax : |low| ≤ max |low| |high| := le_max_left _ _
        have hneg : -|low| ≤ low := neg_abs_le low
        dsimp [R]
        linarith
      · have hmax : |high| ≤ max |low| |high| := le_max_right _ _
        have hpos : high ≤ |high| := le_abs_self high
        dsimp [R]
        linarith
    exact hprofileBad.elim (fun hh => (ne_of_gt hident.1) hh)
      (fun hh => (not_lt_of_ge habs) hh)
  exact (measureReal_mono (μ := birthParentLaw) hsub).trans_lt hA

end HeightPaper.CountCoupling
