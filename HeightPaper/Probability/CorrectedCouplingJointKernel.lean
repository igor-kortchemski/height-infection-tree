module

public import HeightPaper.Probability.CorrectedCouplingJointPrefix

/-!
# The next-token kernel on complete joint logical histories

The causal physical partitions are summed before any assertion about a
logical history is made. The kernel depends only on that history's word and
last forest, so it factors out of the countable partition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace HeightPaper.CountCoupling

noncomputable def jointHistoryKernel (N : ℕ) (r : List Bool → ℝ) (h : List CouplingToken) :
    Measure CouplingToken :=
  sourceMiddleTokenLaw (jointHistoryForest (Finset.range N) h) (r (jointHistoryWord h))

theorem middle_logical_kernel_on_jointPrefix
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hp1 : p ≤ 1)
    (r : List Bool → ℝ) (h : List CouplingToken) :
    (pairedUniformLaw.restrict (jointPrefixEvent N p q r h)).map
      (fun w ↦ correctedCouplingLogicalToken N p q r w h.length) =
      pairedUniformLaw (jointPrefixEvent N p q r h) • jointHistoryKernel N r h := by
  let E := jointHistoryEvent N p q r h
  let T := fun w ↦ correctedCouplingLogicalToken N p q r w h.length
  have hT : Measurable T := measurable_correctedCouplingLogicalToken N p q r _
  have hE (a : ℕ × FiniteCouplingState) : MeasurableSet (E a) :=
    measurableSet_jointHistoryEvent N p q r h a
  have hd : Pairwise (Disjoint on E) := jointHistoryEvent_pairwise N p q r h
  have hc : (⋃ a, E a) =ᵐ[pairedUniformLaw] jointPrefixEvent N p q r h :=
    jointHistoryEvent_ae_cover N hN hp hp1 q r h
  have hloc (a : ℕ × FiniteCouplingState) :
      (pairedUniformLaw.restrict (E a)).map T = pairedUniformLaw (E a) • jointHistoryKernel N r h := by
    by_cases hne : (E a).Nonempty
    · obtain ⟨w, hw⟩ := hne
      obtain ⟨hlen, hword, hforest⟩ := jointHistoryEvent_state N p q r h a w hw
      have hk := middle_logical_kernel_on_event N hN hp hpq hp1 r a.1 (E a) (hE a)
        (jointHistoryEvent_congr_prefix N p q r h a) a.2 (fun _ hz ↦ hz.2.2)
      simpa only [hlen, hword, hforest, jointHistoryKernel, T, jointHistoryWord,
        List.length_map] using hk
    · have he : E a = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [he, Measure.restrict_empty, Measure.map_zero, measure_empty, zero_smul]
  calc
    _ = Measure.sum (fun a ↦ (pairedUniformLaw.restrict (E a)).map T) := by
      rw [← Measure.restrict_congr_set hc, Measure.restrict_iUnion hd hE,
        Measure.map_sum hT.aemeasurable]
    _ = Measure.sum (fun a ↦ pairedUniformLaw (E a) • jointHistoryKernel N r h) := by
      congr 1
      funext a
      exact hloc a
    _ = _ := by
      ext D hD
      rw [Measure.sum_apply _ hD]
      simp only [Measure.smul_apply, smul_eq_mul]
      rw [ENNReal.tsum_mul_right, ← measure_iUnion hd hE, measure_congr hc]

theorem couplingTokenPrefix_append_iff (x : ℕ → CouplingToken) (h : List CouplingToken)
    (t : CouplingToken) :
    couplingTokenPrefix x (h.length + 1) = h ++ [t] ↔
      couplingTokenPrefix x h.length = h ∧ x h.length = t := by
  rw [couplingTokenPrefix_succ]
  constructor
  · intro he
    have hp := List.append_inj he (couplingTokenPrefix_length x h.length)
    exact ⟨hp.1, by simpa only [List.singleton_inj] using hp.2⟩
  · rintro ⟨hh, ht⟩
    rw [hh, ht]

theorem correctedCoupling_joint_cylinder_factor
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hp1 : p ≤ 1)
    (r : List Bool → ℝ) (h : List CouplingToken) (t : CouplingToken) :
    pairedUniformLaw (jointPrefixEvent N p q r (h ++ [t])) =
      pairedUniformLaw (jointPrefixEvent N p q r h) * jointHistoryKernel N r h {t} := by
  have hk := congrArg (fun ν : Measure CouplingToken ↦ ν {t})
    (middle_logical_kernel_on_jointPrefix N hN hp hpq hp1 r h)
  rw [Measure.map_apply (measurable_correctedCouplingLogicalToken N p q r h.length)
      (measurableSet_singleton t),
    Measure.restrict_apply ((measurableSet_singleton t).preimage
      (measurable_correctedCouplingLogicalToken N p q r h.length)),
    Measure.smul_apply, smul_eq_mul] at hk
  have he : jointPrefixEvent N p q r (h ++ [t]) =
      (fun w ↦ correctedCouplingLogicalToken N p q r w h.length) ⁻¹' {t} ∩
        jointPrefixEvent N p q r h := by
    ext w
    simp only [jointPrefixEvent, Set.mem_ofPred_eq, List.length_append, List.length_singleton,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      couplingTokenPrefix_append_iff, and_comm]
  rw [he]
  exact hk

end HeightPaper.CountCoupling
