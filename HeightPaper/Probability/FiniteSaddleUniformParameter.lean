module

public import HeightPaper.Probability.FiniteResidualCompactCentral
public import HeightPaper.Probability.FiniteProfileAmplitudeTightness
public import HeightPaper.Probability.FiniteSaddleAmplitudeCentral
public import HeightPaper.Probability.FiniteFourierOuter

/-! # Stochastic saddle approximation uniformly in parameter and lattice tilt -/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped NNReal Topology

namespace HeightPaper.CountCoupling

open Model

/-- The normalized finite saddle integral is close to the local limit times
the actual finite entire normalizer residual, with one threshold for every
parameter and exact lattice tilt in the given compact sets. -/
theorem finiteSaddle_uniform_parameter_tilt_integral_tight
    {I : Set ℝ≥0} (hI : IsCompact I) (hIne : I.Nonempty)
    {T : ℝ} (hT : 0 < T)
    {K : Set ℝ} (hK : IsCompact K) (hKne : K.Nonempty)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l ∧
      K ⊆ Ioo 0 (profileRoot l))
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real {q | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n q.1 i) ∧
        ∃ x ∈ K, ∃ k : ℕ,
          (k : ℝ) = growthFactor l * Real.exp x * Real.log n ∧
          τ < ‖(Real.sqrt (Real.log n *
              (growthFactor l * Real.exp x) / 2) : ℂ) *
                (∫ v : ℝ in -Real.pi..Real.pi,
                  finiteSaddleIntegrandAtScale l ⌊T * n⌋₊ (Real.log n) x
                    (coupledTreeHistory l n ⌊T * n⌋₊ q) v) -
              (localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
                finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ q.1
                  (Real.log n) (x : ℂ)) * (Real.sqrt Real.pi : ℂ)‖} < δ := by
  obtain ⟨lmin, hlmin, hminL⟩ := hI.exists_isLeast hIne
  obtain ⟨lmax, hlmax, hmaxL⟩ := hI.exists_isGreatest hIne
  have hIlower : ∀ a ∈ I, (lmin : ℝ) ≤ (a : ℝ) := by
    intro a ha
    exact_mod_cast hminL ha
  have hparams' : ∀ a ∈ I, 1 < (a : ℝ) ∧ T < fluidExtinctionTime a := by
    intro a ha
    exact ⟨(hparams a ha).1, (hparams a ha).2.1⟩
  obtain ⟨xmin, hxmin, hmin⟩ := hK.exists_isLeast hKne
  obtain ⟨xmax, hxmax, hmax⟩ := hK.exists_isGreatest hKne
  let θmin : ℝ := growthFactor lmax * Real.exp xmin
  let θmax : ℝ := growthFactor lmin * Real.exp xmax
  have hθmin : 0 < θmin :=
    mul_pos (growthFactor_pos (hparams lmax hlmax).1) (Real.exp_pos xmin)
  have hθmax : 0 < θmax :=
    mul_pos (growthFactor_pos (hparams lmin hlmin).1) (Real.exp_pos xmax)
  have hθbounds : ∀ l ∈ I, ∀ x ∈ K,
      θmin ≤ growthFactor l * Real.exp x ∧
        growthFactor l * Real.exp x ≤ θmax := by
    intro l hl x hx
    have hgl : growthFactor lmax ≤ growthFactor l :=
      growthFactor_antitone (hparams l hl).1 (by exact_mod_cast hmaxL hl)
    have hgu : growthFactor l ≤ growthFactor lmin :=
      growthFactor_antitone (hparams lmin hlmin).1 (hIlower l hl)
    constructor
    · calc
        θmin = growthFactor lmax * Real.exp xmin := rfl
        _ ≤ growthFactor l * Real.exp xmin :=
          mul_le_mul_of_nonneg_right hgl (Real.exp_pos _).le
        _ ≤ growthFactor l * Real.exp x :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hmin hx))
            (growthFactor_pos (hparams l hl).1).le
    · calc
        growthFactor l * Real.exp x ≤ growthFactor lmin * Real.exp x :=
          mul_le_mul_of_nonneg_right hgu (Real.exp_pos _).le
        _ ≤ growthFactor lmin * Real.exp xmax :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hmax hx))
            (growthFactor_pos (hparams lmin hlmin).1).le
        _ = θmax := rfl
  have hthird : 0 < δ / 3 := by positivity
  obtain ⟨_c, _hc, B, hB, NA, hamp⟩ := finite_profileResidual_compact_tight
    hI (hparams lmin hlmin).1 hT hparams' hIlower hK hKne
    (hparams lmin hlmin).2.2 hthird
  let ε₀ : ℝ := τ / (8 * (Real.sqrt Real.pi + 1))
  let τ₀ : ℝ := τ / (8 * (Real.sqrt (θmax / 2) + 1))
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hτ₀ : 0 < τ₀ := by dsimp [τ₀]; positivity
  have hεsmall : ε₀ * Real.sqrt Real.pi < τ / 8 := by
    have he : ε₀ * (Real.sqrt Real.pi + 1) = τ / 8 := by
      dsimp [ε₀]
      field_simp
    linarith
  have hτsmall : Real.sqrt (θmax / 2) * τ₀ < τ / 8 := by
    have he : (Real.sqrt (θmax / 2) + 1) * τ₀ = τ / 8 := by
      dsimp [τ₀]
      field_simp
    linarith
  obtain ⟨t, ht, NC, hcenter⟩ := finite_profileResidual_compact_centered_disk
    hI (hparams lmin hlmin).1 hT hparams' hIlower hK hKne
    (hparams lmin hlmin).2.2 hε₀ hthird
  obtain ⟨NO, houter⟩ := finiteSaddle_outer_lattice_uniform hI
    hK hT hparams hτ₀ hthird
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hwindow0 : Tendsto (fun n : ℕ => saddleWindow (Real.log n)) atTop (𝓝 0) :=
    saddleWindow_tendsto_zero.comp hlog
  obtain ⟨Nδ, hNδ⟩ := eventually_atTop.mp
    (hwindow0.eventually (Iio_mem_nhds ht))
  obtain ⟨Nlog, hNlog⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop 1)
  obtain ⟨Ncubic, hNcubic⟩ := eventually_atTop.mp
    (hlog.eventually (saddleWindow_eventually_cubic_small θmax))
  let C : ℝ := 2 * (B + 2 * ε₀) * θmax * Real.sqrt Real.pi
  have hCubicLim : Tendsto (fun n : ℕ =>
      C * (Real.log n * saddleWindow (Real.log n) ^ 3)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (saddleWindow_cubic_tendsto_zero.const_mul C).comp hlog
  obtain ⟨NcubeSmall, hNcubeSmall⟩ := eventually_atTop.mp
    (hCubicLim.eventually (Iio_mem_nhds (by positivity : 0 < τ / 8)))
  let G : ℝ := (B + ε₀) * Real.sqrt (2 * Real.pi)
  have hGaussLim : Tendsto (fun n : ℕ => G *
      Real.exp (-(θmin / 4) * Real.log n *
        saddleWindow (Real.log n) ^ 2)) atTop (𝓝 0) := by
    have hh := saddleWindow_polynomial_tail_tendsto_zero
      (show 0 < θmin / 4 by positivity) 0
    simpa only [Function.comp_def, Real.rpow_zero, one_mul, mul_zero] using
      (hh.const_mul G).comp hlog
  obtain ⟨Ngauss, hNgauss⟩ := eventually_atTop.mp
    (hGaussLim.eventually (Iio_mem_nhds (by positivity : 0 < τ / 8)))
  refine ⟨NA + NC + NO + Nδ + Nlog + Ncubic + NcubeSmall + Ngauss, ?_⟩
  intro n hn l hl
  let a : ℝ := Real.log n
  let H : ℕ := ⌊T * n⌋₊
  let w : ℝ := saddleWindow a
  have ha1 : 1 ≤ a := hNlog n (by omega)
  have ha : 0 < a := zero_lt_one.trans_le ha1
  have hwpos : 0 < w := saddleWindow_pos ha
  have hw1 : w ≤ 1 := saddleWindow_le_one ha1
  have hwt : w < t := hNδ n (by omega)
  have hcub : a * θmax * w ^ 3 ≤ 1 := hNcubic n (by omega)
  have hcubSmall : 2 * (B + 2 * ε₀) * a * θmax * w ^ 3 *
      Real.sqrt Real.pi < τ / 8 := by
    have hh := hNcubeSmall n (by omega)
    change C * (a * w ^ 3) < τ / 8 at hh
    have heq : 2 * (B + 2 * ε₀) * a * θmax * w ^ 3 * Real.sqrt Real.pi =
        C * (a * w ^ 3) := by dsimp [C]; ring
    rw [heq]
    exact hh
  have hgaussSmall : (B + ε₀) * Real.exp (-a * θmin * w ^ 2 / 4) *
      Real.sqrt (2 * Real.pi) < τ / 8 := by
    have hh := hNgauss n (by omega)
    change G * Real.exp (-(θmin / 4) * a * w ^ 2) < τ / 8 at hh
    calc
      _ = (B + ε₀) * Real.sqrt (2 * Real.pi) *
          Real.exp (-a * θmin * w ^ 2 / 4) := by ring
      _ = G * Real.exp (-(θmin / 4) * a * w ^ 2) := by
        have heq : -a * θmin * w ^ 2 / 4 = -(θmin / 4) * a * w ^ 2 := by ring
        rw [heq]
      _ < τ / 8 := hh
  let E : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ y ∈ K, ∃ z ∈ closedBall (y : ℂ) t,
        ε₀ < ‖profileResidual (coupledTreeState l n q H) (growthFactor l) a z -
          localUnshiftedRankProfileLimit l 0 q (y : ℂ) *
            finiteUnshiftedNormalizerResidual l n H q.1 a (y : ℂ)‖}
  let A : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ y ∈ K,
        ‖profileResidual (coupledTreeState l n q H) (growthFactor l) a (y : ℂ)‖ < _c ∨
        B < ‖profileResidual (coupledTreeState l n q H) (growthFactor l) a (y : ℂ)‖}
  let O := finiteSaddleOuterBad l n H a w K τ₀
  have hE : birthParentLaw.real E < δ / 3 := hcenter n (by omega) l hl
  have hA : birthParentLaw.real A < δ / 3 := hamp n (by omega) l hl
  have hO : birthParentLaw.real O < δ / 3 := houter n (by omega) l hl
  have hsub : {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ y ∈ K, ∃ k : ℕ, (k : ℝ) = growthFactor l * Real.exp y * a ∧
        τ < ‖(Real.sqrt (a * (growthFactor l * Real.exp y) / 2) : ℂ) *
          (∫ v : ℝ in -Real.pi..Real.pi,
            finiteSaddleIntegrandAtScale l H a y (coupledTreeHistory l n H q) v) -
          (localUnshiftedRankProfileLimit l 0 q (y : ℂ) *
            finiteUnshiftedNormalizerResidual l n H q.1 a (y : ℂ)) *
              (Real.sqrt Real.pi : ℂ)‖} ⊆ (E ∪ A) ∪ O := by
    rintro q ⟨hs, y, hy, k, hk, hbad⟩
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    let θ : ℝ := growthFactor l * Real.exp y
    have hθ : 0 < θ := mul_pos (growthFactor_pos (hparams l hl).1) (Real.exp_pos y)
    have hθlo : θmin ≤ θ := (hθbounds l hl y hy).1
    have hθhi : θ ≤ θmax := (hθbounds l hl y hy).2
    let A₀ : ℂ := localUnshiftedRankProfileLimit l 0 q (y : ℂ) *
      finiteUnshiftedNormalizerResidual l n H q.1 a (y : ℂ)
    have hclose : ∀ v ∈ Icc (-w) w,
        ‖profileResidual (coupledTreeState l n q H) (growthFactor l) a
          ((y : ℂ) + (v : ℂ) * Complex.I) - A₀‖ ≤ ε₀ := by
      intro v hv
      have hvabs : |v| ≤ w := abs_le.mpr ⟨hv.1, hv.2⟩
      have hz : (y : ℂ) + (v : ℂ) * Complex.I ∈ closedBall (y : ℂ) t := by
        rw [mem_closedBall, dist_eq_norm]
        have heq : (y : ℂ) + (v : ℂ) * Complex.I - (y : ℂ) =
            (v : ℂ) * Complex.I := by ring
        rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
        exact hvabs.trans hwt.le
      apply le_of_not_gt
      intro hh
      exact hnot.1.1 ⟨hs, y, hy, _, hz, hh⟩
    have hcenter : ‖profileResidual (coupledTreeState l n q H)
        (growthFactor l) a (y : ℂ)‖ ≤ B := by
      apply le_of_not_gt
      intro hh
      exact hnot.1.2 ⟨hs, y, hy, Or.inr hh⟩
    have houterBound : Real.sqrt a * ‖finiteSaddleOuterIntegralAtScale l H a y w
        (coupledTreeHistory l n H q)‖ ≤ τ₀ := by
      apply le_of_not_gt
      intro hh
      exact hnot.2 ⟨hs, y, hy, k, hk, hh⟩
    have hA₀ : ‖A₀‖ ≤ B + ε₀ := by
      have hc : ‖profileResidual (coupledTreeState l n q H)
          (growthFactor l) a (y : ℂ) - A₀‖ ≤ ε₀ := by
        simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
          hclose 0 ⟨by linarith [hwpos], hwpos.le⟩
      have hh := norm_le_norm_add_norm_sub
        (profileResidual (coupledTreeState l n q H) (growthFactor l) a (y : ℂ)) A₀
      linarith
    have hcubY : a * θ * w ^ 3 ≤ 1 := by
      have hfac : 0 ≤ a * w ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hθhi hfac, hcub]
    have hdet := finiteSaddle_normalized_error_of_central_outer l n H q
      ha hθ hwpos.le hw1 hε₀.le hB.le hτ₀.le hcubY A₀ hclose hcenter houterBound
    have hsqrt : Real.sqrt (a * θ / 2) = Real.sqrt a * Real.sqrt (θ / 2) := by
      rw [show a * θ / 2 = a * (θ / 2) by ring, Real.sqrt_mul ha.le]
    have hsqrta : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
    have houterEq : Real.sqrt (a * θ / 2) * (τ₀ / Real.sqrt a) =
        Real.sqrt (θ / 2) * τ₀ := by
      rw [hsqrt]
      field_simp
    have hθsqrt : Real.sqrt (θ / 2) ≤ Real.sqrt (θmax / 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have houterSmall : Real.sqrt (θ / 2) * τ₀ < τ / 8 :=
      (mul_le_mul_of_nonneg_right hθsqrt hτ₀.le).trans_lt hτsmall
    have hcubBound : 2 * (B + 2 * ε₀) * a * θ * w ^ 3 *
        Real.sqrt Real.pi ≤
        2 * (B + 2 * ε₀) * a * θmax * w ^ 3 * Real.sqrt Real.pi := by
      gcongr
    have hgaussBound : ‖A₀‖ * Real.exp (-a * θ * w ^ 2 / 4) *
        Real.sqrt (2 * Real.pi) ≤
        (B + ε₀) * Real.exp (-a * θmin * w ^ 2 / 4) *
          Real.sqrt (2 * Real.pi) := by
      have hexp : Real.exp (-a * θ * w ^ 2 / 4) ≤
          Real.exp (-a * θmin * w ^ 2 / 4) :=
        Real.exp_le_exp.mpr (by
          have hm := mul_le_mul_of_nonneg_right hθlo
            (by positivity : 0 ≤ a * w ^ 2 / 4)
          nlinarith [hm])
      calc
        _ ≤ (B + ε₀) * Real.exp (-a * θ * w ^ 2 / 4) *
            Real.sqrt (2 * Real.pi) := by gcongr
        _ ≤ _ := by gcongr
    rw [houterEq] at hdet
    have hdet' : ‖(Real.sqrt (a * θ / 2) : ℂ) *
        (∫ v : ℝ in -Real.pi..Real.pi,
          finiteSaddleIntegrandAtScale l H a y (coupledTreeHistory l n H q) v) -
        A₀ * (Real.sqrt Real.pi : ℂ)‖ < τ := by
      have hcubTerm : (ε₀ + 2 * (B + 2 * ε₀) * a * θ * w ^ 3) *
          Real.sqrt Real.pi = ε₀ * Real.sqrt Real.pi +
            2 * (B + 2 * ε₀) * a * θ * w ^ 3 * Real.sqrt Real.pi := by ring
      rw [hcubTerm] at hdet
      linarith [hcubBound, hcubSmall, hgaussBound, hgaussSmall, hεsmall, houterSmall]
    exact (not_lt_of_ge hdet'.le) hbad
  have hh := (measureReal_mono (μ := birthParentLaw) hsub).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (measureReal_union_le _ _) le_rfl))
  linarith

end HeightPaper.CountCoupling
