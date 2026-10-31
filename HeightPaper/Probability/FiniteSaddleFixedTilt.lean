module

public import HeightPaper.Probability.FiniteSaddleAmplitudeCentral
public import HeightPaper.Probability.FiniteProfileAmplitudeTightness
public import HeightPaper.Probability.FiniteFourierOuter

/-! # The stochastic saddle estimate at one admissible real tilt -/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped NNReal Topology

namespace HeightPaper.CountCoupling

open Model

/-- The normalized finite saddle integral is close in probability to the
canonical local profile at the real tilt times the actual finite normalizer
residual. This is the fixed-tilt stochastic assembly, before taking a supremum
over the paper's compact lattice tilt set. -/
theorem finiteSaddle_fixed_tilt_integral_tight {l : ℝ≥0} (hl : 1 < (l : ℝ))
    {T x : ℝ} (hT : 0 < T) (hText : T < fluidExtinctionTime l)
    (hx : x ∈ Ioo 0 (profileRoot l)) {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      birthParentLaw.real {q | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n q.1 i) ∧
        ∃ k : ℕ, (k : ℝ) = growthFactor l * Real.exp x * Real.log n ∧
          τ < ‖(Real.sqrt (Real.log n *
              (growthFactor l * Real.exp x) / 2) : ℂ) *
                (∫ v : ℝ in -Real.pi..Real.pi,
                  finiteSaddleIntegrandAtScale l ⌊T * n⌋₊ (Real.log n) x
                    (coupledTreeHistory l n ⌊T * n⌋₊ q) v) -
              (localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
                finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ q.1
                  (Real.log n) (x : ℂ)) * (Real.sqrt Real.pi : ℂ)‖} < δ := by
  let I : Set ℝ≥0 := {l}
  have hI : IsCompact I := isCompact_singleton
  have hparams : ∀ a ∈ I, 1 < (a : ℝ) ∧ T < fluidExtinctionTime a := by
    intro a ha
    have he : a = l := mem_singleton_iff.mp ha
    simpa only [he] using And.intro hl hText
  have hIlower : ∀ a ∈ I, (l : ℝ) ≤ (a : ℝ) := by
    intro a ha
    rw [mem_singleton_iff.mp ha]
  obtain ⟨p, hp, η, hη, ρ, hρ, hw⟩ :=
    exists_localProfile_unshifted_moment_disk hl hx.1 hx.2
  have hr : 0 < ρ / 4 := by positivity
  have hrR : ρ / 4 < ρ / 2 := by linarith
  have hRρ : ρ / 2 < ρ := by linarith
  have hright : ∀ z ∈ closedBall (x : ℂ) (ρ / 2), 1 ≤ (Complex.exp z).re := by
    intro z hz
    exact (hw l le_rfl z ((mem_closedBall.mp hz).trans_lt hRρ)).1.le
  have hwindow : ∀ a ≥ (l : ℝ), ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot a ∧ p * z.re < 2 * profileRoot a ∧
        complexProfileMomentExponent a z p ≤ -1 - η :=
    fun a ha z hz => (hw a ha z hz).2
  have hθ : 0 < growthFactor l * Real.exp x :=
    mul_pos (growthFactor_pos hl) (Real.exp_pos x)
  have hthird : 0 < δ / 3 := by positivity
  obtain ⟨_c, _hc, B, hB, NA, hamp⟩ := finite_profileResidual_compact_tight
    hI hl hT hparams hIlower isCompact_singleton (Set.singleton_nonempty x)
    (by intro y hy; simpa only [mem_singleton_iff.mp hy] using hx) hthird
  let ε₀ : ℝ := τ / (8 * (Real.sqrt Real.pi + 1))
  let τ₀ : ℝ := τ / (8 * (Real.sqrt ((growthFactor l * Real.exp x) / 2) + 1))
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hτ₀ : 0 < τ₀ := by dsimp [τ₀]; positivity
  have hεsmall : ε₀ * Real.sqrt Real.pi < τ / 8 := by
    have he : ε₀ * (Real.sqrt Real.pi + 1) = τ / 8 := by
      dsimp [ε₀]
      field_simp
    linarith
  have hτsmall : Real.sqrt ((growthFactor l * Real.exp x) / 2) * τ₀ < τ / 8 := by
    have he : (Real.sqrt ((growthFactor l * Real.exp x) / 2) + 1) * τ₀ = τ / 8 := by
      dsimp [τ₀]
      field_simp
    linarith
  obtain ⟨t, ht, NC, hcenter⟩ := finite_profileResidual_centered_disk
    hI hl hT hparams hIlower hp.1 hp.2.le hη hr hrR hRρ hright hwindow
    hε₀ hthird
  have houterParams : ∀ a ∈ I, 1 < (a : ℝ) ∧
      T < fluidExtinctionTime a ∧ ({x} : Set ℝ) ⊆ Ioo 0 (profileRoot a) := by
    intro a ha
    have he : a = l := mem_singleton_iff.mp ha
    subst a
    refine ⟨hl, hText, ?_⟩
    intro y hy
    simpa only [mem_singleton_iff.mp hy] using hx
  obtain ⟨NO, houter⟩ := finiteSaddle_outer_lattice_uniform hI
    isCompact_singleton hT houterParams hτ₀ hthird
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hwindow0 : Tendsto (fun n : ℕ => saddleWindow (Real.log n)) atTop (𝓝 0) :=
    saddleWindow_tendsto_zero.comp hlog
  obtain ⟨Nδ, hNδ⟩ := eventually_atTop.mp
    (hwindow0.eventually (Iio_mem_nhds ht))
  obtain ⟨Nlog, hNlog⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop 1)
  obtain ⟨Ncubic, hNcubic⟩ := eventually_atTop.mp
    (hlog.eventually (saddleWindow_eventually_cubic_small
      (growthFactor l * Real.exp x)))
  let C : ℝ := 2 * (B + 2 * ε₀) * (growthFactor l * Real.exp x) * Real.sqrt Real.pi
  have hCubicLim : Tendsto (fun n : ℕ =>
      C * (Real.log n * saddleWindow (Real.log n) ^ 3)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (saddleWindow_cubic_tendsto_zero.const_mul C).comp hlog
  obtain ⟨NcubeSmall, hNcubeSmall⟩ := eventually_atTop.mp
    (hCubicLim.eventually (Iio_mem_nhds (by positivity : 0 < τ / 8)))
  let G : ℝ := (B + ε₀) * Real.sqrt (2 * Real.pi)
  have hGaussLim : Tendsto (fun n : ℕ => G *
      Real.exp (-(growthFactor l * Real.exp x / 4) * Real.log n *
        saddleWindow (Real.log n) ^ 2)) atTop (𝓝 0) := by
    have hh := saddleWindow_polynomial_tail_tendsto_zero
      (show 0 < growthFactor l * Real.exp x / 4 by positivity) 0
    simpa only [Function.comp_def, Real.rpow_zero, one_mul, mul_zero] using
      (hh.const_mul G).comp hlog
  obtain ⟨Ngauss, hNgauss⟩ := eventually_atTop.mp
    (hGaussLim.eventually (Iio_mem_nhds (by positivity : 0 < τ / 8)))
  refine ⟨NA + NC + NO + Nδ + Nlog + Ncubic + NcubeSmall + Ngauss, ?_⟩
  intro n hn
  let a : ℝ := Real.log n
  let H : ℕ := ⌊T * n⌋₊
  let w : ℝ := saddleWindow a
  let θ : ℝ := growthFactor l * Real.exp x
  have ha1 : 1 ≤ a := hNlog n (by omega)
  have ha : 0 < a := zero_lt_one.trans_le ha1
  have hwpos : 0 < w := saddleWindow_pos ha
  have hw1 : w ≤ 1 := saddleWindow_le_one ha1
  have hwt : w < t := hNδ n (by omega)
  have hcub : a * θ * w ^ 3 ≤ 1 := hNcubic n (by omega)
  have hcubSmall : 2 * (B + 2 * ε₀) * a * θ * w ^ 3 *
      Real.sqrt Real.pi < τ / 8 := by
    have hh := hNcubeSmall n (by omega)
    change C * (a * w ^ 3) < τ / 8 at hh
    have heq : 2 * (B + 2 * ε₀) * a * θ * w ^ 3 * Real.sqrt Real.pi =
        C * (a * w ^ 3) := by dsimp [C, θ]; ring
    rw [heq]
    exact hh
  have hgaussSmall : (B + ε₀) * Real.exp (-a * θ * w ^ 2 / 4) *
      Real.sqrt (2 * Real.pi) < τ / 8 := by
    have hh := hNgauss n (by omega)
    change G * Real.exp (-(θ / 4) * a * w ^ 2) < τ / 8 at hh
    calc
      _ = (B + ε₀) * Real.sqrt (2 * Real.pi) *
          Real.exp (-a * θ * w ^ 2 / 4) := by ring
      _ = G * Real.exp (-(θ / 4) * a * w ^ 2) := by
        have heq : -a * θ * w ^ 2 / 4 = -(θ / 4) * a * w ^ 2 := by ring
        rw [heq]
      _ < τ / 8 := hh
  let E : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ z ∈ closedBall (x : ℂ) t,
        ε₀ < ‖profileResidual (coupledTreeState l n q H) (growthFactor l) a z -
          localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
            finiteUnshiftedNormalizerResidual l n H q.1 a (x : ℂ)‖}
  let A : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ y ∈ ({x} : Set ℝ),
        ‖profileResidual (coupledTreeState l n q H) (growthFactor l) a (y : ℂ)‖ < _c ∨
        B < ‖profileResidual (coupledTreeState l n q H) (growthFactor l) a (y : ℂ)‖}
  let O := finiteSaddleOuterBad l n H a w ({x} : Set ℝ) τ₀
  have hE : birthParentLaw.real E < δ / 3 := hcenter n (by omega) l (mem_singleton l)
  have hA : birthParentLaw.real A < δ / 3 := hamp n (by omega) l (mem_singleton l)
  have hO : birthParentLaw.real O < δ / 3 := houter n (by omega) l (mem_singleton l)
  have hsub : {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ k : ℕ, (k : ℝ) = growthFactor l * Real.exp x * a ∧
        τ < ‖(Real.sqrt (a * θ / 2) : ℂ) *
          (∫ v : ℝ in -Real.pi..Real.pi,
            finiteSaddleIntegrandAtScale l H a x (coupledTreeHistory l n H q) v) -
          (localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
            finiteUnshiftedNormalizerResidual l n H q.1 a (x : ℂ)) *
              (Real.sqrt Real.pi : ℂ)‖} ⊆ (E ∪ A) ∪ O := by
    rintro q ⟨hs, k, hk, hbad⟩
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    let A₀ : ℂ := localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
      finiteUnshiftedNormalizerResidual l n H q.1 a (x : ℂ)
    have hclose : ∀ v ∈ Icc (-w) w,
        ‖profileResidual (coupledTreeState l n q H) (growthFactor l) a
          ((x : ℂ) + (v : ℂ) * Complex.I) - A₀‖ ≤ ε₀ := by
      intro v hv
      have hvabs : |v| ≤ w := abs_le.mpr ⟨hv.1, hv.2⟩
      have hz : (x : ℂ) + (v : ℂ) * Complex.I ∈ closedBall (x : ℂ) t := by
        rw [mem_closedBall, dist_eq_norm]
        have heq : (x : ℂ) + (v : ℂ) * Complex.I - (x : ℂ) =
            (v : ℂ) * Complex.I := by ring
        rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
        exact hvabs.trans hwt.le
      apply le_of_not_gt
      intro hh
      exact hnot.1.1 ⟨hs, _, hz, hh⟩
    have hcenter : ‖profileResidual (coupledTreeState l n q H)
        (growthFactor l) a (x : ℂ)‖ ≤ B := by
      apply le_of_not_gt
      intro hh
      exact hnot.1.2 ⟨hs, x, mem_singleton x, Or.inr hh⟩
    have houterBound : Real.sqrt a * ‖finiteSaddleOuterIntegralAtScale l H a x w
        (coupledTreeHistory l n H q)‖ ≤ τ₀ := by
      apply le_of_not_gt
      intro hh
      exact hnot.2 ⟨hs, x, mem_singleton x, k, hk, hh⟩
    have hA₀ : ‖A₀‖ ≤ B + ε₀ := by
      have hc : ‖profileResidual (coupledTreeState l n q H)
          (growthFactor l) a (x : ℂ) - A₀‖ ≤ ε₀ := by
        simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
          hclose 0 ⟨by linarith [hwpos], hwpos.le⟩
      have hh := norm_le_norm_add_norm_sub
        (profileResidual (coupledTreeState l n q H) (growthFactor l) a (x : ℂ)) A₀
      linarith
    have hdet := finiteSaddle_normalized_error_of_central_outer l n H q
      ha hθ hwpos.le hw1 hε₀.le hB.le hτ₀.le hcub A₀ hclose hcenter houterBound
    have hsqrt : Real.sqrt (a * θ / 2) = Real.sqrt a * Real.sqrt (θ / 2) := by
      rw [show a * θ / 2 = a * (θ / 2) by ring, Real.sqrt_mul ha.le]
    have hsqrta : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
    have houterEq : Real.sqrt (a * θ / 2) * (τ₀ / Real.sqrt a) =
        Real.sqrt (θ / 2) * τ₀ := by
      rw [hsqrt]
      field_simp
    have hgauss : ‖A₀‖ * Real.exp (-a * θ * w ^ 2 / 4) *
        Real.sqrt (2 * Real.pi) ≤
        (B + ε₀) * Real.exp (-a * θ * w ^ 2 / 4) *
          Real.sqrt (2 * Real.pi) := by
      gcongr
    rw [houterEq] at hdet
    have hηterm : ε₀ * Real.sqrt Real.pi < τ / 8 := hεsmall
    have houterTerm : Real.sqrt (θ / 2) * τ₀ < τ / 8 := hτsmall
    have hdet' : ‖(Real.sqrt (a * θ / 2) : ℂ) *
        (∫ v : ℝ in -Real.pi..Real.pi,
          finiteSaddleIntegrandAtScale l H a x (coupledTreeHistory l n H q) v) -
        A₀ * (Real.sqrt Real.pi : ℂ)‖ < τ := by
      have hcubTerm : (ε₀ + 2 * (B + 2 * ε₀) * a * θ * w ^ 3) *
          Real.sqrt Real.pi = ε₀ * Real.sqrt Real.pi +
            2 * (B + 2 * ε₀) * a * θ * w ^ 3 * Real.sqrt Real.pi := by ring
      rw [hcubTerm] at hdet
      linarith [hgauss, hcubSmall, hgaussSmall, hηterm, houterTerm]
    exact (not_lt_of_ge hdet'.le) hbad
  have hh := (measureReal_mono (μ := birthParentLaw) hsub).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (measureReal_union_le _ _) le_rfl))
  linarith

end HeightPaper.CountCoupling
