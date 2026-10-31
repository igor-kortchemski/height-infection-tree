module

public import HeightPaper.Probability.LocalProfileCarrier
public import HeightPaper.Probability.ConditionalProductBound
public import HeightPaper.Probability.FiniteProfileDiskBound

/-!
# Uniform joint tails for the unshifted local profile

The conditional moment multiplier is tight under the birth-word law. Finite
joint disk events are measurable through a finite word and two state codes,
so the conditional circle bounds lift to the independent birth-parent law.
-/

@[expose] public section

open MeasureTheory Complex Metric Set Filter
open scoped Topology

namespace HeightPaper.CountCoupling

open Model

theorem measurableSet_of_localBirth_rankStates (l : ℝ) (n H j k : ℕ)
    {E : Set ((ℕ → ℝ) × (ℕ → ℝ))}
    (hE : ∀ q q', (∀ i < H, localBirth l q.1 i = localBirth l q'.1 i) →
      rankState (localBirth l q.1) (initial n) q.2 j =
        rankState (localBirth l q'.1) (initial n) q'.2 j →
      rankState (localBirth l q.1) (initial n) q.2 k =
        rankState (localBirth l q'.1) (initial n) q'.2 k → (q ∈ E ↔ q' ∈ E)) :
    MeasurableSet E := by
  let f : ((ℕ → ℝ) × (ℕ → ℝ)) → (Fin H → Bool) × (State × State) := fun q ↦
    (fun i ↦ localBirth l q.1 i,
      rankState (localBirth l q.1) (initial n) q.2 j,
      rankState (localBirth l q.1) (initial n) q.2 k)
  have hf : Measurable f :=
    (Measurable.of_eval (fun i : Fin H ↦ (measurable_localBirth l i).comp measurable_fst)).prodMk
      (((measurable_pi_apply j).comp (measurable_local_rankTrajectory l (initial n))).prodMk
        ((measurable_pi_apply k).comp (measurable_local_rankTrajectory l (initial n))))
  have heq : f ⁻¹' (f '' E) = E := by
    ext q
    constructor
    · rintro ⟨q', hq', hcode⟩
      exact (hE q' q (fun i hi ↦ congrFun (congrArg Prod.fst hcode) ⟨i, hi⟩)
        (congrArg (fun a ↦ a.2.1) hcode) (congrArg (fun a ↦ a.2.2) hcode)).mp hq'
    · intro hq
      exact ⟨q, hq, rfl⟩
  rw [← heq]
  exact hf (Set.to_countable _).measurableSet

theorem measurableSet_local_survival (l : ℝ) :
    MeasurableSet {u : ℕ → ℝ | ∀ i, 0 < (localWalk l u i : ℝ)} := by
  have hh := MeasurableSet.iInter (fun i ↦
    measurableSet_lt (measurable_const : Measurable (fun _ : ℕ → ℝ ↦ (0 : ℝ)))
      (measurable_localWalk_real l i))
  convert hh using 1
  ext u
  simp

def localUnshiftedProfileDiskDifferenceBad (l : ℝ) (n j k : ℕ) (K : Set ℂ) (ε : ℝ) :
    Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {q | (∀ i, 0 < (localWalk l q.1 i : ℝ)) ∧ ∃ z ∈ K,
    ε < ‖localUnshiftedRankProfile l n q k z - localUnshiftedRankProfile l n q j z‖}

theorem measurableSet_localUnshiftedProfileDiskDifferenceBad (l : ℝ) (n j k : ℕ)
    (hjk : j ≤ k) (K : Set ℂ) (ε : ℝ) :
    MeasurableSet (localUnshiftedProfileDiskDifferenceBad l n j k K ε) := by
  apply ((measurableSet_local_survival l).preimage measurable_fst).inter
  apply measurableSet_of_localBirth_rankStates l n k j k
  intro q q' he hsj hsk
  have hC (i : ℕ) (hi : i ≤ k) (z : ℂ) :=
    prescribedNormalizerFrom_congr_prefix (Complex.exp z) 1 0 he hi
  change (∃ z ∈ K, ε < ‖localUnshiftedRankProfile l n q k z - localUnshiftedRankProfile l n q j z‖) ↔
    ∃ z ∈ K, ε < ‖localUnshiftedRankProfile l n q' k z - localUnshiftedRankProfile l n q' j z‖
  simp only [localUnshiftedRankProfile, prescribedNormalizedProfile,
    infectious_initial, hsj, hsk, hC j hjk, hC k le_rfl]

theorem localUnshiftedProfileDiskDifferenceBad_le_bad_add (l : ℝ) (n j k : ℕ)
    (hjk : j ≤ k) (z₀ : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hright : ∀ z ∈ closedBall z₀ R, 1 ≤ (Complex.exp z).re)
    {p M ε : ℝ} (hp : 1 ≤ p) (hM : 0 ≤ M) (hε : 0 < ε)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hgood : ∀ u, u ∉ B → (∀ i, 0 < (localWalk l u i : ℝ)) →
      localSafeCutoff l u ≤ j ∧
        ∀ z ∈ sphere z₀ R, localProfileMomentDifference l u n z p j k ≤ M) :
    birthParentLaw.real (localUnshiftedProfileDiskDifferenceBad l n j k (closedBall z₀ r) ε) ≤
      uniformLaw.real B + (R / (2 * Real.pi * (R - r)) * (2 * Real.pi) * M ^ p⁻¹) / ε := by
  have hR : 0 < R := hr.trans_lt hrR
  have hgap : 0 < R - r := sub_pos.mpr hrR
  apply birthParentLaw_real_le_bad_add
    (measurableSet_localUnshiftedProfileDiskDifferenceBad l n j k hjk _ ε).nullMeasurableSet hB
    (by positivity)
  apply ae_of_all
  intro u hu
  by_cases hs : ∀ i, 0 < (localWalk l u i : ℝ)
  · obtain ⟨hJj, hm⟩ := hgood u hu hs
    have hC (i : ℕ) (z : ℂ) (hz : z ∈ closedBall z₀ R) :
        prescribedNormalizerFrom (Complex.exp z) (localBirth l u) 1 (localSafeCutoff l u) i ≠ 0 :=
      norm_pos_iff.mp (zero_lt_one.trans_le
        (one_le_norm_prescribedNormalizerFrom (hright z hz) (localBirth l u) 1 _ i))
    apply (measureReal_mono (μ := uniformLaw) (show
      {v | (u, v) ∈ localUnshiftedProfileDiskDifferenceBad l n j k (closedBall z₀ r) ε} ⊆
        {v | ∃ z ∈ closedBall z₀ r,
          ε < ‖prescribedNormalizedProfile (Complex.exp z) (localBirth l u) (initial n)
              (localSafeCutoff l u) k (rankState (localBirth l u) (initial n) v k) -
            prescribedNormalizedProfile (Complex.exp z) (localBirth l u) (initial n)
              (localSafeCutoff l u) j (rankState (localBirth l u) (initial n) v j)‖} from ?_)).trans
    · apply (rankTrajectory_measureReal_preimage_le (localBirth l u) (initial n)
        {ω | ∃ z ∈ closedBall z₀ r,
          ε < ‖prescribedNormalizedProfile (Complex.exp z) (localBirth l u) (initial n)
              (localSafeCutoff l u) k (ω k) -
            prescribedNormalizedProfile (Complex.exp z) (localBirth l u) (initial n)
              (localSafeCutoff l u) j (ω j)‖}).trans
      apply prescribedTrajectory_uniform_difference_probability_le_of_two_normalizers
        (localBirth l u) (initial n) (localSafeCutoff l u) z₀ hr hrR hJj hjk
        (by simpa only [infectious_initial] using hC j)
        (by simpa only [infectious_initial] using hC k) hp hε
      exact hm
    · rintro v ⟨_, z, hz, he⟩
      refine ⟨z, hz, he.trans_le ?_⟩
      exact norm_unshifted_profile_difference_le
        (hright z (closedBall_subset_closedBall hrR.le hz)) (localBirth l u) (initial n) _ _
        hJj (hJj.trans hjk)
  · simp only [localUnshiftedProfileDiskDifferenceBad, mem_ofPred_eq, hs, false_and,
      Set.ofPred_false, measureReal_empty]
    positivity

/-- One shared late-time threshold controls every pair of local times and
all epidemic parameters above the lower endpoint. -/
theorem localProfile_unshifted_two_time_disk_tail_uniform {l₀ x p η ρ r R : ℝ}
    (hl₀ : 1 < l₀) (hp : 1 < p) (hp2 : p ≤ 2) (hη : 0 < η)
    (hr : 0 ≤ r) (hrR : r < R) (hRρ : R < ρ)
    (hright : ∀ z ∈ closedBall (x : ℂ) R, 1 ≤ (Complex.exp z).re)
    (hwindow : ∀ l ≥ l₀, ∀ z : ℂ, dist z (x : ℂ) < ρ →
      0 ≤ z.re ∧ z.re < profileRoot l ∧ p * z.re < 2 * profileRoot l ∧
        complexProfileMomentExponent l z p ≤ -1 - η)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ l ≥ l₀, ∀ n j k : ℕ, A ≤ j → j ≤ k →
      birthParentLaw.real (localUnshiftedProfileDiskDifferenceBad l n j k
        (closedBall (x : ℂ) r) ε) < δ := by
  have hthird : 0 < δ / 3 := by positivity
  obtain ⟨D, hD, hDtight⟩ := localProfileMomentBad_uniform_tight hl₀ hp hp2 hη hwindow hthird
  obtain ⟨J₀, hJtight⟩ := localSafeCutoff_uniform_tight hl₀ hthird
  let M : ℕ → ℝ := fun j ↦ D * (j : ℝ) ^ (-η)
  let C : ℕ → ℝ := fun j ↦
    (R / (2 * Real.pi * (R - r)) * (2 * Real.pi) * (M j) ^ p⁻¹) / ε
  have hMt : Tendsto M atTop (𝓝 0) := by
    simpa only [M, Function.comp_def, mul_zero] using
      (((tendsto_rpow_neg_atTop hη).comp tendsto_natCast_atTop_atTop).const_mul D)
  have hCt : Tendsto C atTop (𝓝 0) := by
    have hh := ((hMt.rpow_const_nhds_zero (inv_pos.mpr (zero_lt_one.trans hp))).const_mul
      (R / (2 * Real.pi * (R - r)) * (2 * Real.pi))).div_const ε
    simpa only [C, mul_zero, zero_div] using hh
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp (hCt.eventually (Iio_mem_nhds hthird))
  let A := max A₀ (max J₀ 1)
  refine ⟨A, (le_max_right J₀ 1).trans (le_max_right A₀ _), ?_⟩
  intro l hl n j k hj hjk
  let E₀ : Set (ℕ → ℝ) := {u | j < localSafeCutoff l u}
  let E₁ := localProfileMomentBad p η ρ x D l
  have hE₀ : MeasurableSet E₀ :=
    measurableSet_lt measurable_const (measurable_localSafeCutoff l)
  have hE₁ : MeasurableSet E₁ := measurableSet_localProfileMomentBad _ _ _ _ _ _
  have h₀ : uniformLaw.real E₀ ≤ δ / 3 := by
    apply (measureReal_mono (μ := uniformLaw) (show E₀ ⊆ {u | J₀ < localSafeCutoff l u} from ?_)).trans
      (hJtight l hl)
    intro u hu
    exact ((le_max_left J₀ 1).trans ((le_max_right A₀ _).trans hj)).trans_lt hu
  have h₁ : uniformLaw.real E₁ ≤ δ / 3 := hDtight l hl
  have hCj : C j < δ / 3 := hA₀ j ((le_max_left A₀ _).trans hj)
  have hb := localUnshiftedProfileDiskDifferenceBad_le_bad_add l n j k hjk (x : ℂ) hr hrR
    hright hp.le (show 0 ≤ M j by dsimp [M]; positivity) hε (E₀ ∪ E₁) (hE₀.union hE₁) ?_
  · change birthParentLaw.real _ ≤ uniformLaw.real (E₀ ∪ E₁) + C j at hb
    have hu := measureReal_union_le (μ := uniformLaw) E₀ E₁
    linarith
  · intro u hu hs
    have hJj : localSafeCutoff l u ≤ j := le_of_not_gt (fun h ↦ hu (Or.inl h))
    refine ⟨hJj, ?_⟩
    intro z hz
    apply le_of_not_gt
    intro hbad
    apply hu (Or.inr ?_)
    refine ⟨hs, n, j, k, hJj, ?_, hjk, z, ?_, hbad⟩
    · exact (le_max_right J₀ 1).trans ((le_max_right A₀ _).trans hj)
    · rw [mem_sphere] at hz
      rw [hz]
      exact hRρ

end HeightPaper.CountCoupling
