module

public import HeightPaper.Probability.CorrectedCouplingMiddleRejection

/-!
# Stable chronological labels in the physical middle forest

Fresh births occur above all existing middle labels in both construction
branches. The rank of every old vertex is therefore permanent. These ranks
give an explicit isomorphism to the chronological middle limit, without
claiming that ordered sibling-address inclusions survive renumbering.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

def CouplingGenealogy.ChronoLE (s t : CouplingGenealogy) : Prop :=
  s.TreeLE t ∧ ∀ x ∈ s.carrier.vertices,
    couplingLabelRank t.carrier.vertices x = couplingLabelRank s.carrier.vertices x

theorem CouplingGenealogy.chronoLE_refl (s : CouplingGenealogy) : s.ChronoLE s :=
  ⟨s.treeLE_refl, fun _ _ ↦ rfl⟩

theorem CouplingGenealogy.chronoLE_trans {s t u : CouplingGenealogy}
    (hst : s.ChronoLE t) (htu : t.ChronoLE u) : s.ChronoLE u :=
  ⟨CouplingGenealogy.treeLE_trans hst.1 htu.1,
    fun x hx ↦ (htu.2 x (hst.1.1 hx)).trans (hst.2 x hx)⟩

theorem CouplingGenealogy.chronoLE_update (s : CouplingGenealogy) (v fresh : ℕ)
    (hgt : ∀ x ∈ s.carrier.vertices, x < fresh) (b : Bool) : s.ChronoLE (s.update v fresh b) := by
  have hf : fresh ∉ s.carrier.vertices := fun hx ↦ (Nat.lt_irrefl _) (hgt fresh hx)
  refine ⟨s.treeLE_update v fresh hf b, ?_⟩
  intro x hx
  by_cases hv : v ∈ s.carrier.active
  · cases b
    · have hV : (s.update v fresh false).carrier.vertices = s.carrier.vertices := by
        simp [CouplingGenealogy.update, CouplingCarrier.update, hv]
      rw [hV]
    · have hV : (s.update v fresh true).carrier.vertices = insert fresh s.carrier.vertices := by
        simp [CouplingGenealogy.update, CouplingCarrier.update, hv]
      rw [hV, couplingLabelRank_insert_old s.carrier.vertices hgt hx]
  · have he : s.update v fresh b = s := by simp [CouplingGenealogy.update, CouplingCarrier.update, hv]
    rw [he]

theorem CorrectedCouplingState.middle_chronoLE_step (s : CorrectedCouplingState)
    (hfaith : s.faithful = true → s.trees.Ordered)
    (p q : ℝ) (r : List Bool → ℝ) (u recovery : ℝ) :
    s.trees.middle.ChronoLE (s.step p q r u recovery).trees.middle := by
  by_cases hg : s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q
  · by_cases hu : s.trees.upper.carrier.active.Nonempty
    · have ho := hfaith hg.1
      have hgt : ∀ x ∈ s.trees.middle.carrier.vertices, x < s.trees.upper.fresh :=
        fun x hx ↦ s.trees.upper.mem_lt_fresh (ho.2.1.1 hx)
      simpa only [CorrectedCouplingState.step, hg, hu, and_self, ↓reduceDIte, ↓reduceIte,
        CouplingTriple.step] using s.trees.middle.chronoLE_update
          (s.trees.upper.selectedActive hu u) s.trees.upper.fresh hgt
          (recoveryThresholdBirth (r s.word) recovery)
    · simp only [CorrectedCouplingState.step, hg, hu, and_self, ↓reduceDIte]
      exact s.trees.middle.chronoLE_refl
  · rw [s.step_middle_of_bad p q r hg]
    exact s.trees.middle.chronoLE_update _ s.trees.middle.fresh
      (fun _ hx ↦ s.trees.middle.mem_lt_fresh hx) _

theorem correctedCouplingStage_middle_chronoLE
    (roots : Finset ℕ) (p q : ℝ) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    {i j : ℕ} (hij : i ≤ j) :
    (correctedCouplingStage roots p q r w i).trees.middle.ChronoLE
      (correctedCouplingStage roots p q r w j).trees.middle := by
  induction j, hij using Nat.le_induction with
  | base => exact CouplingGenealogy.chronoLE_refl _
  | succ j _ ih =>
      exact CouplingGenealogy.chronoLE_trans ih
        (CorrectedCouplingState.middle_chronoLE_step _
          (correctedCouplingStage_faithful_ordered roots p q r w j) p q r _ _)

noncomputable def firstVertexTime (T : ℕ → FiniteCouplingGenealogy) (x : ℕ) : ℕ :=
  firstLongWord (fun j ↦ if x ∈ (T j).1.carrier.vertices then [false] else []) 0

theorem firstVertexTime_spec (T : ℕ → FiniteCouplingGenealogy) (x j : ℕ)
    (hx : x ∈ (T j).1.carrier.vertices) :
    x ∈ (T (firstVertexTime T x)).1.carrier.vertices ∧ firstVertexTime T x ≤ j := by
  let W := fun k ↦ if x ∈ (T k).1.carrier.vertices then [false] else []
  have hex : ∃ k, 0 < (W k).length := ⟨j, by simp [W, hx]⟩
  have hspec := firstLongWord_spec W 0 hex
  have hmem : x ∈ (T (firstVertexTime T x)).1.carrier.vertices := by
    by_contra hn
    change 0 < (W (firstVertexTime T x)).length at hspec
    simp [W, hn] at hspec
  refine ⟨hmem, ?_⟩
  by_contra hn
  have hmin := firstLongWord_min W 0 (show j < firstLongWord W 0 by change j < firstVertexTime T x; omega)
  simp [W, hx] at hmin

theorem measurable_firstVertexTime (x : ℕ) : Measurable (fun T ↦ firstVertexTime T x) := by
  have hW : Measurable (fun T : ℕ → FiniteCouplingGenealogy ↦
      fun j ↦ if x ∈ (T j).1.carrier.vertices then [false] else []) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_of_countable
      (fun s : FiniteCouplingGenealogy ↦ if x ∈ s.1.carrier.vertices then [false] else [])).comp
        (measurable_pi_apply j)
  exact (measurable_firstLongWord 0).comp hW

noncomputable def globalChronologicalLabel (T : ℕ → FiniteCouplingGenealogy) (x : ℕ) : ℕ :=
  couplingLabelRank (T (firstVertexTime T x)).1.carrier.vertices x

theorem globalChronologicalLabel_at_stage (T : ℕ → FiniteCouplingGenealogy)
    (hmono : ∀ i j, i ≤ j → (T i).1.ChronoLE (T j).1) (x j : ℕ)
    (hx : x ∈ (T j).1.carrier.vertices) :
    globalChronologicalLabel T x = couplingLabelRank (T j).1.carrier.vertices x := by
  obtain ⟨hmem, hle⟩ := firstVertexTime_spec T x j hx
  exact ((hmono _ _ hle).2 x hmem).symm

theorem globalChronologicalLabel_injOn (T : ℕ → FiniteCouplingGenealogy)
    (hmono : ∀ i j, i ≤ j → (T i).1.ChronoLE (T j).1) :
    Set.InjOn (globalChronologicalLabel T) {x | ∃ j, x ∈ (T j).1.carrier.vertices} := by
  rintro x ⟨i, hx⟩ y ⟨j, hy⟩ he
  have hxk := (hmono i (max i j) (le_max_left _ _)).1.1 hx
  have hyk := (hmono j (max i j) (le_max_right _ _)).1.1 hy
  rw [globalChronologicalLabel_at_stage T hmono x (max i j) hxk,
    globalChronologicalLabel_at_stage T hmono y (max i j) hyk] at he
  exact couplingLabelRank_injOn _ hxk hyk he

end HeightPaper.CountCoupling
