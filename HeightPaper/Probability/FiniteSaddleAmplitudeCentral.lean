module

public import HeightPaper.Probability.LocalProfileAnalyticModulus
public import HeightPaper.Probability.FiniteResidualTightness
public import HeightPaper.Probability.FiniteProfileAmplitude
public import HeightPaper.Probability.FiniteFourierIntegral
public import HeightPaper.Analysis.ProfileSaddleAssembly

/-! # Central amplitude comparison on a fixed saddle disk -/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal

namespace HeightPaper.CountCoupling

open Model

/-- The finite Fourier integrand is exactly the entire residual amplitude
times the centered Poisson phase. -/
theorem finiteSaddleIntegrandAtScale_eq_residual_phase (l : ℝ) (H : ℕ)
    (a x v : ℝ) (q : FinitePath H) :
    finiteSaddleIntegrandAtScale l H a x q v =
      profileResidual q.last (growthFactor l) a
        ((x : ℂ) + (v : ℂ) * Complex.I) *
        Complex.exp ((a : ℂ) * poissonSaddlePhase (growthFactor l * Real.exp x) v) := by
  simpa only [finiteSaddleIntegrandAtScale] using
    (profileResidual_saddle_integrand_eq q.last (growthFactor l) a x v).symm

/-- Exact lattice inversion for the coupled finite epidemic, expressed in the
same integrand used by the stochastic outer-tail estimate. -/
theorem normalizedActiveProfile_coupled_saddle_inversion (l : ℝ) (n H k : ℕ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) (a x : ℝ)
    (hk : (k : ℝ) = a * (growthFactor l * Real.exp x)) :
    (2 * Real.pi : ℝ) * (normalizedActiveProfile (coupledTreeState l n q H) k : ℂ) =
      Complex.exp ((-a * poissonRateAtTilt (growthFactor l) x : ℝ) : ℂ) *
        ∫ v : ℝ in -Real.pi..Real.pi,
          finiteSaddleIntegrandAtScale l H a x (coupledTreeHistory l n H q) v := by
  have hstate : (coupledTreeHistory l n H q).last = coupledTreeState l n q H := rfl
  rw [normalizedActiveProfile_saddle_inversion _ _ _ _ _ hk]
  congr 1
  apply intervalIntegral.integral_congr
  intro v _
  rw [finiteSaddleIntegrandAtScale_eq_residual_phase, hstate]

/-- The deterministic normalized saddle estimate with the actual finite
epidemic amplitude and the actual outer integral. The residual stays inside
the oscillatory integral. -/
theorem finiteSaddle_normalized_error_of_central_outer
    (l : ℝ) (n H : ℕ) (q : (ℕ → ℝ) × (ℕ → ℝ))
    {a x δ η B τ : ℝ} (ha : 0 < a)
    (hθ : 0 < growthFactor l * Real.exp x)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η)
    (hB : 0 ≤ B) (hτ : 0 ≤ τ)
    (hsmall : a * (growthFactor l * Real.exp x) * δ ^ 3 ≤ 1)
    (A₀ : ℂ)
    (hclose : ∀ v ∈ Icc (-δ) δ,
      ‖profileResidual (coupledTreeState l n q H) (growthFactor l) a
        ((x : ℂ) + (v : ℂ) * Complex.I) - A₀‖ ≤ η)
    (hcenter : ‖profileResidual (coupledTreeState l n q H)
      (growthFactor l) a (x : ℂ)‖ ≤ B)
    (houter : Real.sqrt a * ‖finiteSaddleOuterIntegralAtScale l H a x δ
      (coupledTreeHistory l n H q)‖ ≤ τ) :
    ‖(Real.sqrt (a * (growthFactor l * Real.exp x) / 2) : ℂ) *
        (∫ v : ℝ in -Real.pi..Real.pi,
          finiteSaddleIntegrandAtScale l H a x (coupledTreeHistory l n H q) v) -
      A₀ * (Real.sqrt Real.pi : ℂ)‖ ≤
      (η + 2 * (B + 2 * η) * a * (growthFactor l * Real.exp x) * δ ^ 3) *
        Real.sqrt Real.pi +
      Real.sqrt (a * (growthFactor l * Real.exp x) / 2) * (τ / Real.sqrt a) +
      ‖A₀‖ * Real.exp (-a * (growthFactor l * Real.exp x) * δ ^ 2 / 4) *
        Real.sqrt (2 * Real.pi) := by
  let A : ℝ → ℂ := fun v => profileResidual (coupledTreeState l n q H)
    (growthFactor l) a ((x : ℂ) + (v : ℂ) * Complex.I)
  have hcenter0 : ‖A 0 - A₀‖ ≤ η := by
    simpa only [A, Complex.ofReal_zero, zero_mul, add_zero] using
      hclose 0 ⟨by linarith, hδ⟩
  have hA₀ : ‖A₀‖ ≤ B + η := by
    have hh := norm_le_norm_add_norm_sub (A 0) A₀
    have hc : ‖A 0‖ ≤ B := by
      simpa only [A, Complex.ofReal_zero, zero_mul, add_zero] using hcenter
    linarith
  have hAbound : ∀ v ∈ Icc (-δ) δ, ‖A v‖ ≤ B + 2 * η := by
    intro v hv
    have hh := norm_le_norm_add_norm_sub A₀ (A v)
    rw [norm_sub_rev] at hh
    have hc : ‖A v - A₀‖ ≤ η := hclose v hv
    linarith
  have hcont : ContinuousOn A (Icc (-Real.pi) Real.pi) := by
    apply Continuous.continuousOn
    exact (differentiable_profileResidual _ _ _).continuous.comp (by fun_prop)
  have hstate : (coupledTreeHistory l n H q).last = coupledTreeState l n q H := rfl
  have hfun : (fun v : ℝ => A v * Complex.exp
      ((a : ℂ) * poissonSaddlePhase (growthFactor l * Real.exp x) v)) =
      finiteSaddleIntegrandAtScale l H a x (coupledTreeHistory l n H q) := by
    funext v
    rw [finiteSaddleIntegrandAtScale_eq_residual_phase, hstate]
  have houter' : ‖(∫ v : ℝ in -Real.pi..-δ,
        A v * Complex.exp ((a : ℂ) * poissonSaddlePhase
          (growthFactor l * Real.exp x) v)) +
      (∫ v : ℝ in δ..Real.pi,
        A v * Complex.exp ((a : ℂ) * poissonSaddlePhase
          (growthFactor l * Real.exp x) v))‖ ≤ τ / Real.sqrt a := by
    rw [hfun]
    change ‖finiteSaddleOuterIntegralAtScale l H a x δ
      (coupledTreeHistory l n H q)‖ ≤ τ / Real.sqrt a
    apply (le_div_iff₀ (Real.sqrt_pos.mpr ha)).mpr
    simpa only [mul_comm] using houter
  have hh := poissonSaddleAmplitude_lattice_error_of_outer ha hθ hδ hδ1
    (by positivity : 0 ≤ B + 2 * η) hη (by positivity : 0 ≤ τ / Real.sqrt a)
    hsmall A A₀ hcont hAbound (fun v hv => hclose v hv) houter'
  simpa only [hfun] using hh

/-- Uniformly on a small complex disk around a real saddle, the actual finite
residual amplitude is close to the local profile limit at the center times the
finite entire normalizer residual at that center. No convergence of the latter
is assumed. -/
theorem finite_profileResidual_centered_disk
    {I : Set ℝ≥0} (hI : IsCompact I) {l₀ T x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (hIlower : ∀ l ∈ I, l₀ ≤ (l : ℝ))
    (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hr : 0 < r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ∃ t > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      birthParentLaw.real {q | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n q.1 i) ∧
        ∃ z ∈ closedBall (x : ℂ) t,
          τ < ‖profileResidual (coupledTreeState l n q ⌊T * n⌋₊)
            (growthFactor l) (Real.log n) z -
            localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
              finiteUnshiftedNormalizerResidual l n ⌊T * n⌋₊ q.1
                (Real.log n) (x : ℂ)‖} < δ := by
  have hquarter : 0 < δ / 4 := by positivity
  have hKroot : ∀ l ∈ I, ∀ z ∈ closedBall (x : ℂ) r,
      z.re ≤ 2 * profileRoot l := by
    intro l hl z hz
    have hw := hwindow l (hIlower l hl) z
      ((mem_closedBall.mp hz).trans_lt (hrR.trans hRρ))
    have hroot : 0 ≤ profileRoot l := (profileRoot_pos (hparams l hl).1).le
    linarith [hw.2.1]
  have hKexp : ∀ z ∈ closedBall (x : ℂ) r, 1 ≤ (Complex.exp z).re := by
    intro z hz
    exact hright z (closedBall_subset_closedBall hrR.le hz)
  obtain ⟨M, hM, NR, hres⟩ := finiteUnshiftedNormalizerResidual_uniform_bounds
    hI hT hparams hKroot hKexp hquarter
  obtain ⟨B, hB, hupper⟩ := localProfile_unshifted_disk_upper_tight
    hl₀ hp hp2 hη hr.le hrR hRρ hright hwindow hquarter
  have hε : 0 < τ / (3 * M) := by positivity
  obtain ⟨t₀, ht₀, NC, hcenter⟩ := uniform_finite_profile_centered_disk
    hI hl₀ hT hparams hIlower hp hp2 hη hr hrR hRρ hright hwindow
    hε hquarter
  obtain ⟨NS, hsurv⟩ := uniform_survival_disagreement hI hT hparams hquarter
  let t := min (min (t₀ / 2) (r / 2)) (τ * r / (6 * B * M))
  have ht : 0 < t := by dsimp [t]; positivity
  have htm : t ≤ min (t₀ / 2) (r / 2) := min_le_left _ _
  have htt₀ : t < t₀ := (htm.trans (min_le_left _ _)).trans_lt (by linarith)
  have htr : t < r := (htm.trans (min_le_right _ _)).trans_lt (by linarith)
  have hsmall : B * (2 * M / r) * t ≤ τ / 3 := by
    have hle : t ≤ τ * r / (6 * B * M) := min_le_right _ _
    have hm := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ B * (2 * M / r))
    have heq : B * (2 * M / r) * (τ * r / (6 * B * M)) = τ / 3 := by
      field_simp
      ring
    rw [heq] at hm
    exact hm
  refine ⟨t, ht, max NR (max NC NS), ?_⟩
  intro n hn l hl
  let H := ⌊T * n⌋₊
  let C : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ z ∈ closedBall (x : ℂ) t₀,
        τ / (3 * M) < ‖finiteUnshiftedRankProfile l n q H z -
          localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖}
  let U : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧
      ∃ z ∈ closedBall (x : ℂ) r,
        B < ‖localUnshiftedRankProfileLimit l 0 q z‖}
  let Q : Set (ℕ → ℝ) :=
    {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
      ∃ z ∈ closedBall (x : ℂ) r,
        M < ‖finiteUnshiftedNormalizerResidual l n H u (Real.log n) z‖ ∨
          ‖finiteUnshiftedNormalizerResidual l n H u (Real.log n) z‖ < M⁻¹}
  let S : Set (ℕ → ℝ) :=
    {u | ¬((∀ i ≤ H, 0 < finiteWalk l n u i) ↔ ∀ i, 0 < localWalk l u i)}
  have hC : birthParentLaw.real C < δ / 4 :=
    hcenter n ((le_max_left _ _).trans ((le_max_right _ _).trans hn)) l hl
  have hU : birthParentLaw.real U < δ / 4 := hupper l (hIlower l hl) 0
  have hQ : birthParentLaw.real {q | q.1 ∈ Q} < δ / 4 :=
    (birthParentLaw_real_fst_le Q).trans_lt
      (hres n ((le_max_left _ _).trans hn) l hl)
  have hS : birthParentLaw.real {q | q.1 ∈ S} < δ / 4 :=
    (birthParentLaw_real_fst_le S).trans_lt
      (hsurv n ((le_max_right _ _).trans ((le_max_right _ _).trans hn)) l hl)
  have hsub : {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧
      ∃ z ∈ closedBall (x : ℂ) t,
        τ < ‖profileResidual (coupledTreeState l n q H)
          (growthFactor l) (Real.log n) z -
          localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
            finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n) (x : ℂ)‖} ⊆
      ((C ∪ U) ∪ {q | q.1 ∈ Q}) ∪ {q | q.1 ∈ S} := by
    rintro q ⟨hs, z, hz, hbad⟩
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    have hls : ∀ i, 0 < (localWalk l q.1 i : ℝ) := by
      have he : (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ↔
          ∀ i, 0 < localWalk l q.1 i := not_not.mp hnot.2
      exact_mod_cast he.mp hs
    have hL : ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ ≤ B := by
      apply le_of_not_gt
      intro hh
      exact hnot.1.1.2 ⟨hls, (x : ℂ), mem_closedBall_self hr.le, hh⟩
    have hG : ∀ w ∈ ball (x : ℂ) r,
        ‖finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n) w‖ ≤ M := by
      intro w hw
      apply le_of_not_gt
      intro hh
      exact hnot.1.2 ⟨hs, w, ball_subset_closedBall hw, Or.inl hh⟩
    have hclose : ‖finiteUnshiftedRankProfile l n q H z -
        localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ ≤ τ / (3 * M) := by
      apply le_of_not_gt
      intro hh
      exact hnot.1.1.1 ⟨hs, z, closedBall_subset_closedBall htt₀.le hz, hh⟩
    have hzb : z ∈ ball (x : ℂ) r :=
      mem_ball.mpr ((mem_closedBall.mp hz).trans_lt htr)
    have hprod := analytic_product_amplitude_error hr hM.le
      (differentiable_finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n)).differentiableOn
      hG hzb hclose
    have hzt : ‖z - (x : ℂ)‖ ≤ t := by
      simpa only [dist_eq_norm] using (mem_closedBall.mp hz)
    have hmul := mul_le_mul_of_nonneg_left hzt (by positivity : 0 ≤ B * (2 * M / r))
    have hprod' : ‖finiteUnshiftedRankProfile l n q H z *
        finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n) z -
        localUnshiftedRankProfileLimit l 0 q (x : ℂ) *
          finiteUnshiftedNormalizerResidual l n H q.1 (Real.log n) (x : ℂ)‖ ≤
        τ / 3 + τ / 3 := by
      calc
        _ ≤ (τ / (3 * M)) * M +
            ‖localUnshiftedRankProfileLimit l 0 q (x : ℂ)‖ *
              (2 * M / r) * ‖z - (x : ℂ)‖ := hprod
        _ ≤ τ / 3 + B * (2 * M / r) * t := by
          have heq : (τ / (3 * M)) * M = τ / 3 := by field_simp
          rw [heq]
          have hmulL := mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ (2 * M / r) * ‖z - (x : ℂ)‖)
          nlinarith [hmul, hmulL]
        _ ≤ τ / 3 + τ / 3 := by linarith
    have hexp : 1 ≤ (Complex.exp z).re := hright z
      (closedBall_subset_closedBall hrR.le (ball_subset_closedBall hzb))
    rw [profileResidual_eq_unshifted_mul_residual l (Real.log n) n H q hexp] at hbad
    linarith
  have hh := (measureReal_mono (μ := birthParentLaw) hsub).trans
    ((measureReal_union_le _ _).trans
      (add_le_add
        ((measureReal_union_le _ _).trans
          (add_le_add (measureReal_union_le _ _) le_rfl)) le_rfl))
  linarith

end HeightPaper.CountCoupling
