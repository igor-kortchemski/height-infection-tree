module

public import HeightPaper.Probability.CorrectedCouplingUpperExtinction

/-!
# The upper forest's active count

The upper forest chooses a uniform active vertex whenever one exists and
uses the constant recovery threshold `p`. Its active cardinality follows
the unabsorbed nearest-neighbor count walk until the first hit of zero.
Combined with negative drift, this proves almost-sure extinction of the
finite-stage upper genealogy on the two-uniform space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace HeightPaper.CountCoupling

noncomputable def upperStage (roots : Finset ℕ) (p : ℝ)
    (w : (Fin 2 × ℕ) → ℝ) : ℕ → CouplingGenealogy
  | 0 => CouplingGenealogy.initial roots
  | k + 1 =>
      let s := upperStage roots p w k
      if hs : s.carrier.active.Nonempty then
        s.update (s.selectedActive hs (w (0, k))) s.fresh
          (recoveryThresholdBirth p (w (1, k)))
      else s

@[simp] theorem upperStage_zero (roots : Finset ℕ) (p : ℝ)
    (w : (Fin 2 × ℕ) → ℝ) :
    upperStage roots p w 0 = CouplingGenealogy.initial roots := rfl

theorem upperStage_succ (roots : Finset ℕ) (p : ℝ)
    (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) :
    upperStage roots p w (k + 1) =
      let s := upperStage roots p w k
      if hs : s.carrier.active.Nonempty then
        s.update (s.selectedActive hs (w (0, k))) s.fresh
          (recoveryThresholdBirth p (w (1, k)))
      else s := rfl

/-- One selected update changes the active cardinality by exactly the
birth/recovery increment. -/
theorem CouplingGenealogy.active_card_update
    (s : CouplingGenealogy) (v fresh : ℕ)
    (hv : v ∈ s.carrier.active)
    (hfresh : fresh ∉ s.carrier.vertices)
    (b : Bool) :
    (s.update v fresh b).carrier.active.card =
      if b then s.carrier.active.card + 1
      else s.carrier.active.card - 1 := by
  have hfa : fresh ∉ s.carrier.active :=
    fun h ↦ hfresh (s.carrier.active_sub_vertices h)
  cases b <;>
    simp [CouplingGenealogy.update, CouplingCarrier.update,
      hv, hfa, Finset.card_erase_of_mem hv]

/-- Before the first zero of the constant-threshold word, the actual active
set has exactly its integer count. -/
theorem upperStage_active_card_before_hit
    (N : ℕ) (p : ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (k : ℕ)
    (hpre : ∀ j < k,
      0 < couplingActiveCount N
        (adaptiveCouplingWord (fun _ ↦ p)
          (fun t ↦ w (1, t)) j)) :
    ((upperStage (Finset.range N) p w k).carrier.active.card : ℤ) =
      couplingActiveCount N
        (adaptiveCouplingWord (fun _ ↦ p)
          (fun t ↦ w (1, t)) k) := by
  induction k with
  | zero => simp [upperStage, CouplingGenealogy.initial,
      couplingActiveCount]
  | succ k ih =>
      have hpre' : ∀ j < k,
          0 < couplingActiveCount N
            (adaptiveCouplingWord (fun _ ↦ p)
              (fun t ↦ w (1, t)) j) :=
        fun j hj ↦ hpre j (by omega)
      have hk : 0 < couplingActiveCount N
          (adaptiveCouplingWord (fun _ ↦ p)
            (fun t ↦ w (1, t)) k) := hpre k (by omega)
      have hcard := ih hpre'
      have hs : (upperStage (Finset.range N) p w k).carrier.active.Nonempty := by
        apply Finset.card_pos.mp
        omega
      rw [upperStage_succ]
      simp only [dite_eq_left hs]
      rw [CouplingGenealogy.active_card_update]
      · rw [adaptiveCouplingWord_succ,
          couplingActiveCount_append_singleton]
        by_cases hb : recoveryThresholdBirth p (w (1, k)) = true
        · simp only [ite_eq_left hb]
          omega
        · simp only [ite_eq_right hb]
          omega
      · exact (upperStage (Finset.range N) p w k).selectedActive_mem hs _
      · exact (upperStage (Finset.range N) p w k).fresh_not_mem

/-- The upper genealogy eventually has no active vertex, with probability
one. This discharges the extinction premise used by the first-acceptance
rejection theorem for the actual constant-threshold upper process. -/
theorem upperStage_ae_eventually_empty
    (N : ℕ) (hN : 0 < N)
    {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) :
    ∀ᵐ w ∂pairedUniformLaw,
      ∃ k, (upperStage (Finset.range N) p w k).carrier.active = ∅ := by
  have hrec : pairedUniformLaw.map
      (fun w : (Fin 2 × ℕ) → ℝ ↦ fun k ↦ w (1, k)) =
      uniformLaw := by
    change pairedUniformLaw.map (Prod.snd ∘ splitUniforms) = uniformLaw
    rw [← Measure.map_map measurable_snd measurable_splitUniforms,
      pairedUniformLaw_map_split, birthParentLaw_map_snd]
  have hm : Measurable
      (fun w : (Fin 2 × ℕ) → ℝ ↦ fun k ↦ w (1, k)) :=
    measurable_pi_iff.mpr (fun k ↦ measurable_pi_apply (1, k))
  have hset : MeasurableSet
      {u : ℕ → ℝ | ∃ k,
        couplingActiveCount N
          (adaptiveCouplingWord (fun _ ↦ p) u k) = 0} := by
    simp only [ofPred_exists]
    apply MeasurableSet.iUnion
    intro k
    exact ((measurable_of_countable (couplingActiveCount N)).comp
      (measurable_adaptiveCouplingWord (fun _ ↦ p) k))
      (measurableSet_singleton (0 : ℤ))
  have hhit : ∀ᵐ w ∂pairedUniformLaw,
      ∃ k, couplingActiveCount N
        (adaptiveCouplingWord (fun _ ↦ p)
          (fun t ↦ w (1, t)) k) = 0 := by
    have h := constantCouplingCount_ae_hits_zero N hN hp hp1
    rw [← hrec] at h
    exact (ae_map_iff hm.aemeasurable hset).mp h
  filter_upwards [hhit] with w hw
  let k := Nat.find hw
  have hk : couplingActiveCount N
      (adaptiveCouplingWord (fun _ ↦ p)
        (fun t ↦ w (1, t)) k) = 0 := Nat.find_spec hw
  have hpre : ∀ j < k,
      0 < couplingActiveCount N
        (adaptiveCouplingWord (fun _ ↦ p)
          (fun t ↦ w (1, t)) j) := by
    intro j hj
    by_contra hnot
    have hnonpos : couplingActiveCount N
        (adaptiveCouplingWord (fun _ ↦ p)
          (fun t ↦ w (1, t)) j) ≤ 0 := by omega
    obtain ⟨i, hij, hi⟩ :=
      constantCouplingCount_hit_zero_of_nonpos N hN p
        (fun t ↦ w (1, t)) j hnonpos
    exact Nat.find_min hw (lt_of_le_of_lt hij hj) hi
  have hcard := upperStage_active_card_before_hit N p w k hpre
  rw [hk] at hcard
  exact ⟨k, Finset.card_eq_zero.mp (by exact_mod_cast hcard)⟩

end HeightPaper.CountCoupling
