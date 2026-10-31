module

public import HeightPaper.Probability.FiniteProfileDiskBound
public import HeightPaper.Probability.ConditionalProductBound

/-! # Joint finite-profile disk tails from conditional moment controls -/

@[expose] public section

open MeasureTheory Complex Metric Set Filter
open scoped Topology NNReal

namespace HeightPaper.CountCoupling

open Model

def finiteProfileDiskBad (l : ℝ) (n H j : ℕ) (K : Set ℂ) (ε : ℝ) :
    Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {q | (∀ i ≤ H, 0 < finiteWalk l n q.1 i) ∧ ∃ z ∈ K,
    ε < ‖prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n q.1) (initial n)
        (finiteSafeCutoff l n H q.1) H (rankState (finiteBirth l n q.1) (initial n) q.2 H) -
      prescribedNormalizedProfile (Complex.exp z) (finiteBirth l n q.1) (initial n)
        (finiteSafeCutoff l n H q.1) j (rankState (finiteBirth l n q.1) (initial n) q.2 j)‖}

theorem measurableSet_finiteProfileDiskBad (l : ℝ) (n H j : ℕ) (hj : j ≤ H)
    (K : Set ℂ) (ε : ℝ) : MeasurableSet (finiteProfileDiskBad l n H j K ε) := by
  have hs : MeasurableSet {u | ∀ i ≤ H, 0 < finiteWalk l n u i} := by
    apply measurableSet_of_finiteBirth_prefix l n H
    intro u v he
    simp only [mem_ofPred_eq]
    exact forall₂_congr (fun i hi => by rw [finiteWalk_congr_birth_prefix he hi])
  exact (hs.preimage measurable_fst).inter
    (measurableSet_finite_rankProfile_difference l n H j H hj le_rfl K ε)

theorem finiteProfileDiskBad_le_bad_add (l : ℝ) (n H j : ℕ) (hj : j ≤ H)
    (z₀ : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hwindow : ∀ z ∈ closedBall z₀ R, z.re ≤ 2 * profileRoot l)
    {p M ε : ℝ} (hp : 1 ≤ p) (hM : 0 ≤ M) (hε : 0 < ε)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hgood : ∀ u, u ∉ B → (∀ i ≤ H, 0 < finiteWalk l n u i) →
      finiteSafeCutoff l n H u ≤ j ∧
        ∀ z ∈ sphere z₀ R, finiteProfileDifferenceMoment l n H u j H z p ≤ M) :
    birthParentLaw.real (finiteProfileDiskBad l n H j (closedBall z₀ r) ε) ≤
      uniformLaw.real B + (R / (2 * Real.pi * (R - r)) * (2 * Real.pi) * M ^ p⁻¹) / ε := by
  apply birthParentLaw_real_le_bad_add
    (measurableSet_finiteProfileDiskBad l n H j hj _ ε).nullMeasurableSet hB
    (show 0 ≤ (R / (2 * Real.pi * (R - r)) * (2 * Real.pi) * M ^ p⁻¹) / ε by
      have hR : 0 < R := hr.trans_lt hrR
      have hgap : 0 < R - r := sub_pos.mpr hrR
      positivity)
  apply ae_of_all
  intro u hu
  by_cases hs : ∀ i ≤ H, 0 < finiteWalk l n u i
  · obtain ⟨hJ, hm⟩ := hgood u hu hs
    apply le_trans (measureReal_mono (μ := uniformLaw) ?_)
      (finiteProfile_uniform_difference_probability_le hs hJ hj le_rfl z₀ hr hrR hwindow hp hε hm)
    exact fun v hv => hv.2
  · simp only [finiteProfileDiskBad, mem_ofPred_eq, hs, false_and, Set.ofPred_false, measureReal_empty]
    have hR : 0 < R := hr.trans_lt hrR
    have hgap : 0 < R - r := sub_pos.mpr hrR
    positivity

/-- On a common moment-decay disk, sufficiently late finite profiles are
uniformly close in joint probability to one fixed early profile. Constants
are selected before the epidemic parameter and population. -/
theorem finiteProfile_disk_tail_uniform_with_cutoff {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    (z₀ : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {p η : ℝ} (hp : p ∈ Ioc (1 : ℝ) 2) (hη : 0 < η)
    (hwindow : ∀ l ∈ I, ∀ z ∈ closedBall z₀ R,
      0 ≤ z.re ∧ z.re ≤ 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A N : ℕ, 1 ≤ A ∧ ∀ n ≥ N, A ≤ ⌊T * n⌋₊ ∧ ∀ l ∈ I, ∀ j ≥ A, j ≤ ⌊T * n⌋₊ →
      birthParentLaw.real (finiteProfileDiskBad l n ⌊T * n⌋₊ j (closedBall z₀ r) ε) < δ ∧
        uniformLaw.real {u | (∀ i ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u i) ∧
          j < finiteSafeCutoff l n ⌊T * n⌋₊ u} < δ := by
  have hthird : 0 < δ / 3 := by positivity
  obtain ⟨J₀, N₀, hcut⟩ := finiteSafeCutoff_survival_uniform_tight hI hT hparams hthird
  obtain ⟨B, hB, N₁, hmoment⟩ := finiteProfileDifferenceMoment_uniform_tail hI hT hparams hη hthird
  let M : ℕ → ℝ := fun j => 16 * Real.exp B * ((j : ℝ) ^ (-η) / η)
  let C : ℕ → ℝ := fun j =>
    (R / (2 * Real.pi * (R - r)) * (2 * Real.pi) * (M j) ^ p⁻¹) / ε
  have hMt : Tendsto M atTop (𝓝 0) := by
    have hh := (((tendsto_rpow_neg_atTop hη).comp tendsto_natCast_atTop_atTop).div_const η).const_mul
      (16 * Real.exp B)
    simpa only [M, Function.comp_def, zero_div, mul_zero] using hh
  have hCt : Tendsto C atTop (𝓝 0) := by
    have hh := ((hMt.rpow_const_nhds_zero (inv_pos.mpr (zero_lt_one.trans hp.1))).const_mul
      (R / (2 * Real.pi * (R - r)) * (2 * Real.pi))).div_const ε
    simpa only [C, mul_zero, zero_div] using hh
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp (hCt.eventually (Iio_mem_nhds hthird))
  let A := max A₀ (max J₀ 1)
  have hA : 1 ≤ A := (le_max_right J₀ 1).trans (le_max_right A₀ _)
  have hJA : J₀ ≤ A := (le_max_left J₀ 1).trans (le_max_right A₀ _)
  have hH : Tendsto (fun n : ℕ => ⌊T * n⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hT)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hH.eventually_ge_atTop A)
  refine ⟨A, N₀ + N₁ + N₂, hA, ?_⟩
  intro n hn
  have hAH := hN₂ n (by omega)
  refine ⟨hAH, ?_⟩
  intro l hl j hj hjH
  have hCj : C j < δ / 3 := hA₀ j ((le_max_left _ _).trans hj)
  let H := ⌊T * n⌋₊
  let E₀ : Set (ℕ → ℝ) := {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧ j < finiteSafeCutoff l n H u}
  let E₁ : Set (ℕ → ℝ) := {u | (∀ i ≤ H, 0 < finiteWalk l n u i) ∧
    finiteSafeCutoff l n H u ≤ j ∧ ∃ z ∈ sphere z₀ R,
      M j < finiteProfileDifferenceMoment l n H u j H z p}
  have hE₀ : MeasurableSet E₀ := by
    apply measurableSet_of_finiteBirth_prefix l n H
    intro u v he
    have hsurv := forall₂_congr (fun i (hi : i ≤ H) =>
      show (0 < finiteWalk l n u i) ↔ (0 < finiteWalk l n v i) by
        rw [finiteWalk_congr_birth_prefix he hi])
    simp only [E₀, mem_ofPred_eq, hsurv, finiteSafeCutoff_congr_birth_prefix he]
  have hE₁ : MeasurableSet E₁ := by
    apply measurableSet_of_finiteBirth_prefix l n H
    intro u v he
    have hsurv := forall₂_congr (fun i (hi : i ≤ H) =>
      show (0 < finiteWalk l n u i) ↔ (0 < finiteWalk l n v i) by
        rw [finiteWalk_congr_birth_prefix he hi])
    simp only [E₁, mem_ofPred_eq, hsurv, finiteSafeCutoff_congr_birth_prefix he,
      finiteProfileDifferenceMoment_congr_birth_prefix he hjH le_rfl]
  have hp₀ : uniformLaw.real E₀ < δ / 3 := by
    apply lt_of_le_of_lt (measureReal_mono (μ := uniformLaw) ?_) (hcut n (by omega) l hl)
    intro u hu
    change J₀ < if ∀ i ≤ H, 0 < finiteWalk l n u i then finiteSafeCutoff l n H u else 0
    rw [ite_eq_left hu.1]
    exact (hJA.trans hj).trans_lt hu.2
  have hp₁ : uniformLaw.real E₁ < δ / 3 := by
    apply lt_of_le_of_lt (measureReal_mono (μ := uniformLaw) ?_) (hmoment n (by omega) l hl)
    rintro u ⟨hs, hJ, z, hz, hlarge⟩
    obtain ⟨hz0, hzr, he⟩ := hwindow l hl z (sphere_subset_closedBall hz)
    exact ⟨hs, j, H, hA.trans hj, hjH, le_rfl, hJ, z, hz0, hzr, p, hp, he, hlarge⟩
  have hm : 0 ≤ M j := by dsimp [M]; positivity
  have hb := finiteProfileDiskBad_le_bad_add l n H j hjH z₀ hr hrR
    (fun z hz => (hwindow l hl z hz).2.1) hp.1.le hm hε (E₀ ∪ E₁) (hE₀.union hE₁) ?_
  · have hu := measureReal_union_le (μ := uniformLaw) E₀ E₁
    change birthParentLaw.real _ ≤ uniformLaw.real (E₀ ∪ E₁) + C j at hb
    exact ⟨by linarith, by change uniformLaw.real E₀ < δ; linarith⟩
  · intro u hu hs
    have hJ : finiteSafeCutoff l n H u ≤ j :=
      le_of_not_gt (fun h => hu (Or.inl ⟨hs, h⟩))
    exact ⟨hJ, fun z hz => le_of_not_gt (fun h => hu (Or.inr ⟨hs, hJ, z, hz, h⟩))⟩

end HeightPaper.CountCoupling
