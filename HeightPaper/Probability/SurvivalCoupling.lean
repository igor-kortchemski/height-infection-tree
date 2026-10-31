module

public import HeightPaper.Probability.CountCouplingLaw
public import HeightPaper.Probability.UniformWalkBounds
public import HeightPaper.Probability.EarlyExtinctionTightness
public import HeightPaper.Analysis.CompactUniform
public import HeightPaper.Analysis.LogCutoff

/-!
# Agreement of the finite and infinite survival indicators

An early logarithmic prefix agrees with probability tending to one. Extinction
of the finite epidemic after that prefix is negligible before fluid extinction.
Conversely, a local walk surviving the entire finite horizon but dying later
violates the uniform eventual linear lower bound. All three error probabilities
are controlled uniformly on a compact supercritical parameter set.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology symmDiff

namespace HeightPaper.CountCoupling

def finiteSurvival (l : ℝ) (n H : ℕ) : Set (ℕ → ℝ) :=
  {u | ∀ j ≤ H, 0 < finiteWalk l n u j}

def localSurvival (l : ℝ) : Set (ℕ → ℝ) :=
  {u | ∀ k, 0 < localWalk l u k}

def lateLocalExtinction (l : ℝ) (H : ℕ) : Set (ℕ → ℝ) :=
  {u | ∃ k, H < k ∧ localWalk l u k ≤ 0}

def finiteExtinctionBetween (l : ℝ) (n K H : ℕ) : Set (ℕ → ℝ) :=
  {u | 0 < (absorbedCounts l n u K).2 ∧ (absorbedCounts l n u H).2 = 0}

/-- Every survival disagreement is explained by a late local death, a failed
early coupling, or a finite epidemic dying after that early prefix. -/
theorem survival_symmDiff_subset {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : 0 < n)
    (K H : ℕ) :
    finiteSurvival l n H ∆ localSurvival l ⊆ lateLocalExtinction l H ∪
      ({u | ∃ k ≤ K, finiteWalk l n u k ≠ localWalk l u k} ∪
        finiteExtinctionBetween l n K H) := by
  classical
  intro u hu
  rcases hu with ⟨hfin, hloc⟩ | ⟨hloc, hfin⟩
  · apply Or.inl
    have hh : ∃ k, localWalk l u k ≤ 0 := by
      simpa only [localSurvival, mem_ofPred_eq, not_forall, not_lt] using hloc
    obtain ⟨k, hk⟩ := hh
    refine ⟨k, ?_, hk⟩
    by_contra h
    have hp := hfin k (by omega)
    have hs := (walk_sandwich hl hn u k).2
    omega
  · apply Or.inr
    by_cases hdis : ∃ k ≤ K, finiteWalk l n u k ≠ localWalk l u k
    · exact Or.inl hdis
    · apply Or.inr
      have hsmall : ∀ k ≤ K, 0 < finiteWalk l n u k := by
        intro k hk
        have heq : finiteWalk l n u k = localWalk l u k := by
          by_contra hne
          exact hdis ⟨k, hk, hne⟩
        rw [heq]
        exact hloc k
      refine ⟨(finiteWalk_survival_iff l n u K).mp hsmall K le_rfl, ?_⟩
      by_contra hz
      have hpos : 0 < (absorbedCounts l n u H).2 := by omega
      apply hfin
      exact (finiteWalk_survival_iff l n u H).mpr
        (fun j hj ↦ absorbedCounts_pos_past l n u hj hpos)

theorem lateLocalExtinction_probability_le {l₀ l : ℝ} (h₀ : 1 < l₀)
    (hl : l₀ ≤ l) (H : ℕ) :
    uniformLaw.real (lateLocalExtinction l H) ≤
      uniformLaw.real (lateLowerFailure l₀ (H + 1)) := by
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  rintro u ⟨k, hk, hz⟩
  refine ⟨k, by omega, ?_⟩
  have hmono := localWalk_mono (show 0 ≤ l₀ by linarith) hl u k
  have hzero : (localWalk l₀ u k : ℝ) ≤ 0 := by exact_mod_cast hmono.trans hz
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  exact hzero.trans_lt (mul_pos (half_pos (localDrift_pos h₀)) hkpos)

/-- The exact count-path law transfers extinction between two times to the
original state-history law, where its genuine event count exceeds the early time. -/
theorem finiteExtinctionBetween_probability_le (l : ℝ≥0) (n K H : ℕ) (hKH : K ≤ H) :
    uniformLaw.real (finiteExtinctionBetween l n K H) ≤
      (Model.evolve (l / n) n H).toMeasure.real
        {s | Model.infectious s = 0 ∧ K < Model.eventCount s} := by
  let A : Set (Fin (H + 1) → ℕ × ℕ) :=
    {c | 0 < (c ⟨K, by omega⟩).2 ∧ (c (Fin.last H)).2 = 0}
  have hA : MeasurableSet A := (Set.to_countable _).measurableSet
  have hmap := congrArg (fun μ : Measure (Fin (H + 1) → ℕ × ℕ) ↦ μ A)
    (uniformCountHistory_eq_epidemic l n H)
  rw [Measure.map_apply (measurable_uniformCountHistory l n H) hA,
    Measure.map_apply (Model.FinitePath.measurable _) hA] at hmap
  have heq : uniformLaw.real (finiteExtinctionBetween l n K H) =
      (Model.pathMeasure (l / n) n H).real
        {p | 0 < Model.infectious (p.eval K) ∧ Model.infectious p.last = 0} := by
    apply congrArg ENNReal.toReal at hmap
    simpa only [Measure.real, Set.preimage, A, finiteExtinctionBetween,
      uniformCountHistory, stateCountHistory, mem_ofPred_eq, Model.counts, Model.FinitePath.eval,
      Nat.min_eq_left hKH, Model.FinitePath.last, Fin.val_last] using hmap
  rw [heq, ← Model.pathMeasure_event_at (l / n) n H H le_rfl]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply PMF.toMeasure_mono _ (show MeasurableSet
    {p : Model.FinitePath H | 0 < Model.infectious (p.eval K) ∧
      Model.infectious p.last = 0} from trivial)
  intro p hp
  have hs := (Model.mem_support_pathLaw_iff p).mp hp.2
  have hz : Model.infectious (p.eval H) = 0 := by simpa using hp.1.2
  exact ⟨hz, hs.active_earlier_lt_eventCount hKH le_rfl hp.1.1 hz⟩

/-- An explicit three-term error bound for the survival indicators. -/
theorem survival_symmDiff_probability_le {l₀ : ℝ} (h₀ : 1 < l₀) (l : ℝ≥0)
    (hl : l₀ ≤ (l : ℝ)) {n K H : ℕ} (hn : 0 < n) (hKn : K ≤ n) (hKH : K ≤ H) :
    uniformLaw.real (finiteSurvival l n H ∆ localSurvival l) ≤
      uniformLaw.real (lateLowerFailure l₀ (H + 1)) + (l : ℝ) * (K : ℝ)^2 / n +
        (Model.evolve (l / n) n H).toMeasure.real
          {s | Model.infectious s = 0 ∧ K < Model.eventCount s} := by
  have hsub := measureReal_mono (μ := uniformLaw)
    (survival_symmDiff_subset l.coe_nonneg hn K H) (measure_ne_top _ _)
  have hu := measureReal_union_le (μ := uniformLaw) (lateLocalExtinction l H)
    ({u | ∃ k ≤ K, finiteWalk l n u k ≠ localWalk l u k} ∪ finiteExtinctionBetween l n K H)
  have hv := measureReal_union_le (μ := uniformLaw)
    {u | ∃ k ≤ K, finiteWalk l n u k ≠ localWalk l u k} (finiteExtinctionBetween l n K H)
  have ha := lateLocalExtinction_probability_le h₀ hl H
  have hb := prefix_disagreement_probability_le l.coe_nonneg hn hKn
  have hc := finiteExtinctionBetween_probability_le l n K H hKH
  linarith

theorem logCutoff_sq_div_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (logCutoff n : ℝ)^2 / n) atTop (𝓝 0) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ by positivity)) _ h
  exact Eventually.of_forall (fun n ↦ div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.log_natCast_nonneg n)) 2)
    (Nat.cast_nonneg n))

theorem logCutoff_div_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (logCutoff n : ℝ) / n) atTop (𝓝 0) := by
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ by positivity)) _ h
  exact Eventually.of_forall (fun n ↦ div_le_div_of_nonneg_right
    (Nat.floor_le (Real.log_natCast_nonneg n)) (Nat.cast_nonneg n))

theorem eventually_logCutoff_le_horizon {T : ℝ} (hT : 0 < T) :
    ∀ᶠ n : ℕ in atTop, logCutoff n ≤ ⌊T * n⌋₊ := by
  filter_upwards [logCutoff_div_tendsto_zero.eventually_lt (tendsto_floor_fraction hT.le) hT,
    eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  exact_mod_cast ((div_lt_div_iff_of_pos_right hnR).mp hn).le

/-- Compact uniformity for the inherited finite late-extinction estimate;
the rate-sequence theorem supplies all hypotheses of the compactness upgrade. -/
theorem finite_late_extinction_uniform {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
      (Model.evolve (l / n) n ⌊T * n⌋₊).toMeasure.real
        {s | Model.infectious s = 0 ∧ logCutoff n < Model.eventCount s} < ε := by
  let p : ℕ → ℝ≥0 → ℕ → ℝ := fun n l _ ↦
    (Model.evolve (l / n) n ⌊T * n⌋₊).toMeasure.real
      {s | Model.infectious s = 0 ∧ logCutoff n < Model.eventCount s}
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
    have ht := Model.evolve_extinct_eventCount_tail_tendsto_zero
      (fun n ↦ ls n / n) (fun n ↦ ⌊T * n⌋₊) logCutoff (hparams l hl).1
      ⟨hT, (hparams l hl).2⟩ hrates (tendsto_floor_fraction hT.le) tendsto_logCutoff_atTop
    exact ⟨0, ht.eventually (Iio_mem_nhds hη)⟩

/-- The finite-horizon and local infinite survival indicators agree in
probability, weakly uniformly on every compact supercritical parameter set.
The time and size thresholds are chosen before the parameter. -/
theorem uniform_survival_disagreement {I : Set ℝ≥0} (hI : IsCompact I)
    {T : ℝ} (hT : 0 < T)
    (hparams : ∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I, uniformLaw.real {u |
      ¬ ((∀ j ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u j) ↔ ∀ k, 0 < localWalk l u k)} < ε := by
  classical
  by_cases hne : I.Nonempty
  · obtain ⟨l₀, hleast⟩ := hI.exists_isLeast hne
    obtain ⟨L, hgreatest⟩ := hI.exists_isGreatest hne
    have h₀ : 1 < (l₀ : ℝ) := (hparams l₀ hleast.1).1
    have hε3 : 0 < ε / 3 := by positivity
    obtain ⟨Nfin, hfin⟩ := finite_late_extinction_uniform hI hT hparams hε3
    have hpre : Tendsto (fun n : ℕ ↦ (L : ℝ) * (logCutoff n : ℝ)^2 / n)
        atTop (𝓝 0) := by
      convert logCutoff_sq_div_tendsto_zero.const_mul (L : ℝ) using 1
      · funext n
        ring
      · simp
    have hH : Tendsto (fun n : ℕ ↦ ⌊T * n⌋₊) atTop atTop :=
      tendsto_nat_floor_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hT)
    have hlate := (lateLowerFailure_tendsto h₀).comp ((tendsto_add_atTop_nat 1).comp hH)
    apply eventually_atTop.mp
    filter_upwards [hpre.eventually (Iio_mem_nhds hε3), hlate.eventually (Iio_mem_nhds hε3),
      eventually_ge_atTop Nfin, eventually_gt_atTop 0, eventually_logCutoff_le,
      eventually_logCutoff_le_horizon hT] with n hnpre hnlate hnfin hn0 hnkn hnkh
    intro l hl
    have hlow : (l₀ : ℝ) ≤ l := by exact_mod_cast hleast.2 hl
    have hupp : (l : ℝ) ≤ L := by exact_mod_cast hgreatest.2 hl
    have hbound := survival_symmDiff_probability_le h₀ l hlow hn0 hnkn hnkh
    have hprefix : (l : ℝ) * (logCutoff n : ℝ)^2 / n ≤
        (L : ℝ) * (logCutoff n : ℝ)^2 / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hupp (sq_nonneg _)) (Nat.cast_nonneg n)
    have hsmall := hfin n hnfin l hl
    have heq : {u : ℕ → ℝ |
        ¬ ((∀ j ≤ ⌊T * n⌋₊, 0 < finiteWalk l n u j) ↔ ∀ k, 0 < localWalk l u k)} =
        finiteSurvival l n ⌊T * n⌋₊ ∆ localSurvival l := by
      ext u
      simp only [mem_ofPred_eq, mem_symmDiff, finiteSurvival, localSurvival]
      tauto
    rw [heq]
    change uniformLaw.real (lateLowerFailure (l₀ : ℝ) (⌊T * n⌋₊ + 1)) < ε / 3 at hnlate
    change (L : ℝ) * (logCutoff n : ℝ)^2 / n < ε / 3 at hnpre
    linarith
  · exact ⟨0, fun _ _ l hl ↦ (hne ⟨l, hl⟩).elim⟩

end HeightPaper.CountCoupling
