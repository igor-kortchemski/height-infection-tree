module

public import HeightPaper.Probability.FiniteFourierIntegral
public import HeightPaper.Probability.FiniteTreeCouplingLaw
public import HeightPaper.Probability.ConditionalProductBound
public import HeightPaper.Analysis.ProfileSaddleGeometry
public import HeightPaper.Analysis.ProfileSaddleWindow
public import HeightPaper.Analysis.ProfileSaddleTailScale
public import HeightPaper.Analysis.ProfileTimeScale

/-! # Uniform outer Fourier errors on the actual saddle lattice -/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace HeightPaper.CountCoupling

open Model

def finiteSaddleOuterBad (l : ℝ) (n H : ℕ) (a δ : ℝ) (K : Set ℝ) (τ : ℝ) :
    Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧ ∃ x ∈ K, ∃ r : ℕ,
    (r : ℝ) = growthFactor l * Real.exp x * a ∧
      τ < Real.sqrt a * ‖finiteSaddleOuterIntegralAtScale l H a x δ
        (coupledTreeHistory l n H q)‖}

theorem measurableSet_finiteSaddleOuterBad (l : ℝ) (n H : ℕ) (a δ : ℝ)
    (K : Set ℝ) (τ : ℝ) : MeasurableSet (finiteSaddleOuterBad l n H a δ K τ) := by
  have hs : MeasurableSet {u | ∀ i ≤ H, 0 < finiteWalk l n u i} := by
    apply measurableSet_of_finiteBirth_prefix l n H
    intro u v he
    simp only [mem_ofPred_eq]
    exact forall₂_congr (fun i hi ↦ by rw [finiteWalk_congr_birth_prefix he hi])
  have he : MeasurableSet {h : FinitePath H | ∃ x ∈ K, ∃ r : ℕ,
      (r : ℝ) = growthFactor l * Real.exp x * a ∧
        τ < Real.sqrt a * ‖finiteSaddleOuterIntegralAtScale l H a x δ h‖} := by trivial
  exact (hs.preimage measurable_fst).inter (he.preimage (measurable_coupledTreeHistory l n H))

/-- Finite-support Markov after exact transport of the full prescribed history
from the independent parent uniforms. -/
theorem rankHistory_norm_probability_le (events : ℕ → Bool) (s₀ : State) (H : ℕ)
    (F : FinitePath H → ℂ) {A τ B : ℝ} (hA : 0 ≤ A) (hτ : 0 < τ)
    (hmean : (∫ q, ‖F q‖ ∂kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ H) ≤ B) :
    uniformLaw.real {v | τ < A * ‖F (rankHistory events s₀ H v)‖} ≤ A * B / τ := by
  let ν := kernelPathMeasure (fun i ↦ prescribedStep (events i)) s₀ H
  have hi : Integrable (fun q ↦ A * ‖F q‖) ν :=
    integrable_kernelPathMeasure _ (fun i s ↦ finite_support_prescribedStep _ s) s₀ H _
  have hmap : uniformLaw.real {v | τ < A * ‖F (rankHistory events s₀ H v)‖} =
      ν.real {q | τ < A * ‖F q‖} := by
    dsimp only [ν]
    rw [← rankHistory_law events s₀ H]
    exact (map_measureReal_apply (μ := uniformLaw) (s := {q | τ < A * ‖F q‖})
      (measurable_rankHistory events s₀ H) (by trivial)).symm
  rw [hmap]
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := ν)
    (ae_of_all ν (fun q ↦ mul_nonneg hA (norm_nonneg (F q)))) hi τ
  calc
    _ ≤ ν.real {q | τ ≤ A * ‖F q‖} := measureReal_mono (μ := ν) (fun q (h : τ < A * ‖F q‖) ↦ h.le) (measure_ne_top _ _)
    _ ≤ (∫ q, A * ‖F q‖ ∂ν) / τ := (le_div_iff₀ hτ).mpr (by nlinarith)
    _ ≤ A * B / τ := by
      rw [integral_const_mul]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmean hA) hτ.le

/-- A finite lattice union bound, with an explicit conditional first-moment
envelope and the count-word bad event added by product integration. -/
theorem finiteSaddleOuterBad_le_bad_add {l a X δ B τ : ℝ} (hl : 1 < l) (ha : 0 < a)
    {n H : ℕ} {K : Set ℝ} (hK : ∀ x ∈ K, x ≤ X) (hB : 0 ≤ B) (hτ : 0 < τ)
    (E : Set (ℕ → ℝ)) (hE : MeasurableSet E)
    (hmean : ∀ u, u ∉ E → (∀ i ≤ H, 0 < finiteWalk l n u i) → ∀ x ∈ K,
      (∫ q, ‖finiteSaddleOuterIntegralAtScale l H a x δ q‖
        ∂kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) H) ≤ B) :
    birthParentLaw.real (finiteSaddleOuterBad l n H a δ K τ) ≤ uniformLaw.real E +
      ((saddleHeightRange (growthFactor l) a X).card : ℝ) * (Real.sqrt a * B / τ) := by
  apply birthParentLaw_real_le_bad_add (measurableSet_finiteSaddleOuterBad _ _ _ _ _ _ _).nullMeasurableSet
    hE (by positivity)
  apply ae_of_all
  intro u hu
  by_cases hs : ∀ i ≤ H, 0 < finiteWalk l n u i
  · let S := saddleHeightRange (growthFactor l) a X
    let A : ℕ → Set (ℕ → ℝ) := fun r ↦ {v | saddleTilt (growthFactor l) a r ∈ K ∧
      τ < Real.sqrt a * ‖finiteSaddleOuterIntegralAtScale l H a (saddleTilt (growthFactor l) a r) δ
        (rankHistory (finiteBirth l n u) (initial n) H v)‖}
    have hsub : {v | (u, v) ∈ finiteSaddleOuterBad l n H a δ K τ} ⊆ ⋃ r ∈ S, A r := by
      rintro v ⟨_, x, hx, r, hr, hb⟩
      have htilt := saddleTilt_eq_of_lattice (growthFactor_pos hl) ha hr
      refine mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact mem_saddleHeightRange_of_lattice (growthFactor_pos hl).le ha.le (hK x hx) hr
      · simpa only [A, mem_ofPred_eq, htilt, coupledTreeHistory] using And.intro hx hb
    calc
      _ ≤ uniformLaw.real (⋃ r ∈ S, A r) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ r ∈ S, uniformLaw.real (A r) := measureReal_biUnion_finset_le S A
      _ ≤ ∑ _r ∈ S, Real.sqrt a * B / τ := by
        apply Finset.sum_le_sum
        intro r _
        by_cases hx : saddleTilt (growthFactor l) a r ∈ K
        · exact (measureReal_mono (μ := uniformLaw) (fun _ hv ↦ hv.2) (measure_ne_top _ _)).trans
            (rankHistory_norm_probability_le _ _ H _ (Real.sqrt_nonneg a) hτ (hmean u hu hs _ hx))
        · simp only [A, hx, false_and, Set.ofPred_false, measureReal_empty]
          positivity
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, S]
  · simp only [finiteSaddleOuterBad, mem_ofPred_eq, hs, false_and, Set.ofPred_false, measureReal_empty]
    positivity

/-- Uniform Gaussian domination of the weighted moment scale when the event
clock and inversion clock differ by only a bounded additive amount. -/
theorem finiteSaddleScale_le_outer_envelope {l η p a δ c x : ℝ} {H : ℕ}
    (hl : 1 < l) (hη : 0 ≤ η) (hp : 1 ≤ p) (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 ≤ c)
    (hcπ : c ≤ 1 / Real.pi ^ 2) (hcη : c ≤ η / 2)
    (hloglo : a / 2 ≤ Real.log H) (hloghi : Real.log H ≤ 2 * a) :
    finiteSaddleScale l η H x δ p ≤ (1 + 2 * a) * (2 * Real.exp (-c * a * δ ^ 2)) := by
  have hγ := (growthFactor_gt_one hl).le
  have hex := Real.one_le_exp_iff.mpr hx
  have hprod : 1 ≤ p * growthFactor l * Real.exp x := by
    calc
      1 = 1 * 1 * 1 := by norm_num
      _ ≤ p * growthFactor l * Real.exp x := by gcongr
  have hlog : 0 ≤ Real.log H := (by positivity : 0 ≤ a / 2).trans hloglo
  have hcoef : c * a ≤ (2 / Real.pi ^ 2) * p * growthFactor l * Real.exp x * Real.log H := by
    calc
      c * a ≤ (1 / Real.pi ^ 2) * a := mul_le_mul_of_nonneg_right hcπ ha
      _ = (2 / Real.pi ^ 2) * 1 * (a / 2) := by ring
      _ ≤ (2 / Real.pi ^ 2) * (p * growthFactor l * Real.exp x) * Real.log H := by gcongr
      _ = _ := by ring
  have hδsq : δ ^ 2 ≤ 1 := by nlinarith
  have hsecond : c * a * δ ^ 2 ≤ η * Real.log H := by
    calc
      _ ≤ c * a := mul_le_of_le_one_right (mul_nonneg hc ha) hδsq
      _ ≤ (η / 2) * a := mul_le_mul_of_nonneg_right hcη ha
      _ = η * (a / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hloglo hη
  have he₁ : Real.exp (-(2 / Real.pi ^ 2) * p * growthFactor l * Real.exp x * Real.log H * δ ^ 2) ≤
      Real.exp (-c * a * δ ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg δ)]
  have he₂ : Real.exp (-η * Real.log H) ≤ Real.exp (-c * a * δ ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold finiteSaddleScale
  calc
    _ ≤ (1 + 2 * a) * (Real.exp (-c * a * δ ^ 2) + Real.exp (-c * a * δ ^ 2)) := by
      apply mul_le_mul (by linarith) (add_le_add he₁ he₂) (by positivity) (by positivity)
    _ = _ := by ring

/-- A common first-moment bound for every tilt in a bounded positive interval. -/
theorem finiteSaddle_outer_integral_uniform_mean_le
    {l D η Γ X L a δ c p : ℝ} (hl : 1 < l) (hD : 0 ≤ D) (hη : 0 ≤ η)
    (hΓ : growthFactor l ≤ Γ) (_hX : 0 ≤ X) (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hp : 1 < p) (hp2 : p ≤ 2) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hc : 0 ≤ c) (hcπ : c ≤ 1 / Real.pi ^ 2) (hcη : c ≤ η / 2)
    {n H : ℕ} (hH : 1 ≤ H) (hloglo : a / 2 ≤ Real.log H) (hloghi : Real.log H ≤ 2 * a)
    (hdiff : Real.log H - a ≤ L) {u : ℕ → ℝ} (hs : ∀ i ≤ H, 0 < finiteWalk l n u i)
    {x : ℝ} (hx : 0 ≤ x) (hxX : x ≤ X) (hxroot : x ≤ 2 * profileRoot l)
    (hmargin : complexProfileMomentExponent l (x : ℂ) p ≤ -1 - η)
    (hgood : u ∉ finiteSaddleMomentBad η D l n H) :
    (∫ q, ‖finiteSaddleOuterIntegralAtScale l H a x δ q‖
      ∂kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) H) ≤
      2 * Real.pi * Real.exp (Γ * (Real.exp X - 1) * L) *
        (D * ((1 + 2 * a) * (2 * Real.exp (-c * a * δ ^ 2)))) ^ p⁻¹ := by
  have hγ := (growthFactor_pos hl).le
  have hΓ0 := hγ.trans hΓ
  have hex : 0 ≤ Real.exp x - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hx)
  have hfactor : Real.exp (growthFactor l * (Real.exp x - 1) * (Real.log H - a)) ≤
      Real.exp (Γ * (Real.exp X - 1) * L) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ growthFactor l * (Real.exp x - 1) * L :=
        mul_le_mul_of_nonneg_left hdiff (mul_nonneg hγ hex)
      _ ≤ _ := by gcongr
  have hscale := finiteSaddleScale_le_outer_envelope hl hη hp.le ha hx hδ hδ1 hc hcπ hcη hloglo hloghi
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hH)
  have hroot := Real.rpow_le_rpow (show 0 ≤ D * finiteSaddleScale l η H x δ p by
    unfold finiteSaddleScale; positivity) (mul_le_mul_of_nonneg_left hscale hD)
    (by positivity : 0 ≤ p⁻¹)
  apply (finiteSaddle_outer_integral_atScale_mean_le hl hD hs hH le_rfl
    (finiteSafeCutoff_le_horizon _ _ _ _) a hx hxroot hp hp2 hδ
    (hδ1.trans (by linarith [Real.one_le_pi_div_two])) hmargin hgood).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hfactor (by positivity)) hroot
    (by apply Real.rpow_nonneg; unfold finiteSaddleScale; positivity) (by positivity)

/-- The direct outer Fourier integral is negligible, simultaneously over every
actual lattice tilt in a compact interior interval, under the genuine joint
birth-and-parent construction. The normalization is exactly `log n`. -/
theorem finiteSaddle_outer_lattice_uniform {I : Set ℝ≥0} {K : Set ℝ}
    (hI : IsCompact I) (hK : IsCompact K) {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l ∧
      K ⊆ Ioo (0 : ℝ) (profileRoot l))
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I, birthParentLaw.real
      (finiteSaddleOuterBad l n ⌊T * n⌋₊ (Real.log n) (saddleWindow (Real.log n)) K τ) < ε := by
  by_cases hIne : I.Nonempty
  swap
  · exact ⟨0, fun _ _ l hl ↦ False.elim (hIne ⟨l, hl⟩)⟩
  by_cases hKne : K.Nonempty
  swap
  · refine ⟨0, fun n _ l _ ↦ ?_⟩
    have he : finiteSaddleOuterBad l n ⌊T * n⌋₊ (Real.log n) (saddleWindow (Real.log n)) K τ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro q ⟨_, x, hx, _⟩
      exact hKne ⟨x, hx⟩
    rw [he, measureReal_empty]
    exact hε
  obtain ⟨l₀, hl₀, hmin⟩ := hI.exists_isLeast hIne
  obtain ⟨X, hX, hmax⟩ := hK.exists_isGreatest hKne
  let Γ := growthFactor l₀
  have hΓ : 0 < Γ := growthFactor_pos (hparams l₀ hl₀).1
  have hX0 : 0 ≤ X := ((hparams l₀ hl₀).2.2 hX).1.le
  obtain ⟨p, hp, η, hη, hmargin⟩ := exists_uniform_compact_profile_moment_margin hI hK
    (fun l hl ↦ ⟨(hparams l hl).1, (hparams l hl).2.2⟩)
  have hp0 : 0 < p := zero_lt_one.trans hp.1
  let c := min (1 / Real.pi ^ 2) (η / 2)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨D, hD, NM, hM⟩ := finiteSaddleMoment_uniform_bound hI hT
    (fun l hl ↦ ⟨(hparams l hl).1, (hparams l hl).2.1⟩) η hhalf
  obtain ⟨L, hL, NL, hscale⟩ := log_floor_sub_log_bounded hT
  let C := Γ * Real.exp X
  have hC : 0 ≤ C := mul_nonneg hΓ.le (Real.exp_pos X).le
  let Q : ℕ → ℝ := fun n ↦ (2 * Real.pi * Real.exp (Γ * (Real.exp X - 1) * L) / τ) *
    ((C * Real.log n + 2) * Real.sqrt (Real.log n) *
      (D * (1 + 2 * Real.log n) * (2 * Real.exp (-c * Real.log n * saddleWindow (Real.log n) ^ 2))) ^ p⁻¹)
  have hQ : Tendsto Q atTop (𝓝 0) := by
    have hlognat : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hh := (saddleWindow_outer_scale_tendsto_zero hD hC hp0 hc).comp hlognat
    simpa only [Q, Function.comp_def, mul_zero] using
      hh.const_mul (2 * Real.pi * Real.exp (Γ * (Real.exp X - 1) * L) / τ)
  obtain ⟨NQ, hNQ⟩ := eventually_atTop.mp (hQ.eventually (Iio_mem_nhds hhalf))
  obtain ⟨NA, hNA⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max 1 (2 * L)))
  refine ⟨max NM (max NL (max NQ NA)), fun n hn l hl ↦ ?_⟩
  let a := Real.log n
  let H := ⌊T * n⌋₊
  have ha1 : 1 ≤ a := (le_max_left _ _).trans (hNA n (by omega))
  have haL : 2 * L ≤ a := (le_max_right _ _).trans (hNA n (by omega))
  have ha : 0 < a := zero_lt_one.trans_le ha1
  obtain ⟨_hn0, hH0, hlog⟩ := hscale n (by omega)
  have hH : 1 ≤ H := hH0
  have hloglo : a / 2 ≤ Real.log H := by
    have hh := (abs_le.mp hlog).1
    dsimp only [a, H] at *
    linarith
  have hloghi : Real.log H ≤ 2 * a := by
    have hh := (abs_le.mp hlog).2
    dsimp only [a, H] at *
    linarith
  have hδ := saddleWindow_pos ha
  have hδ1 := saddleWindow_le_one ha1
  have hl1 := (hparams l hl).1
  have hγΓ : growthFactor l ≤ Γ := growthFactor_antitone (hparams l₀ hl₀).1 (by exact_mod_cast hmin hl)
  let B := 2 * Real.pi * Real.exp (Γ * (Real.exp X - 1) * L) *
    (D * (1 + 2 * a) * (2 * Real.exp (-c * a * saddleWindow a ^ 2))) ^ p⁻¹
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmean (u : ℕ → ℝ) (hu : u ∉ finiteSaddleMomentBad η D l n H)
      (hs : ∀ i ≤ H, 0 < finiteWalk l n u i) (x : ℝ) (hx : x ∈ K) :
      (∫ q, ‖finiteSaddleOuterIntegralAtScale l H a x (saddleWindow a) q‖
        ∂kernelPathMeasure (fun i ↦ prescribedStep (finiteBirth l n u i)) (initial n) H) ≤ B := by
    have hxwin := (hparams l hl).2.2 hx
    have hr : 0 < profileRoot l := hxwin.1.trans hxwin.2
    simpa only [B, mul_assoc] using finiteSaddle_outer_integral_uniform_mean_le hl1 hD hη.le
      hγΓ hX0 hL.le ha.le hp.1 hp.2.le hδ.le hδ1 hc.le (min_le_left _ _) (min_le_right _ _)
      hH hloglo hloghi (abs_le.mp hlog).2 hs hxwin.1.le (hmax hx)
      (by
        have hrootpos : 0 ≤ profileRoot l := hr.le
        linarith [hxwin.2]) (hmargin l hl x hx) hu
  have hprob := finiteSaddleOuterBad_le_bad_add hl1 ha (fun x hx ↦ hmax hx) hB hτ
    (finiteSaddleMomentBad η D l n H) (measurableSet_finiteSaddleMomentBad _ _ _ _ _) hmean
  have hcard : ((saddleHeightRange (growthFactor l) a X).card : ℝ) ≤ C * a + 2 := by
    apply (saddleHeightRange_card_le (growthFactor_pos hl1).le ha.le).trans
    dsimp only [C]
    gcongr
  have htail : ((saddleHeightRange (growthFactor l) a X).card : ℝ) * (Real.sqrt a * B / τ) ≤ Q n := by
    calc
      _ ≤ (C * a + 2) * (Real.sqrt a * B / τ) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = Q n := by dsimp only [Q, B, a]; ring
  have hm := hM n (show NM ≤ n by omega) l hl
  have hq := hNQ n (show NQ ≤ n by omega)
  calc
    _ ≤ uniformLaw.real (finiteSaddleMomentBad η D l n H) +
        ((saddleHeightRange (growthFactor l) a X).card : ℝ) * (Real.sqrt a * B / τ) := hprob
    _ ≤ ε / 2 + Q n := add_le_add (le_of_lt hm) htail
    _ < ε := by linarith [hq]

end HeightPaper.CountCoupling
