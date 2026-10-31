module

public import HeightPaper.Probability.CorrectedCouplingLimitCode

/-!
# Explicit isomorphisms from stable physical labels to cofinal chronological limits

No correspondence of sibling addresses is assumed. Old birth ranks supply
the vertex bijection, and chronological parent formulas supply both
directions of the edge correspondence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

theorem couplingLabelRank_mem_roots_iff (N : ℕ) (V : Finset ℕ)
    (hroots : Finset.range N ⊆ V) {x : ℕ} (_hx : x ∈ V) :
    couplingLabelRank V x ∈ Finset.range N ↔ x ∈ Finset.range N := by
  constructor
  · intro hr
    by_contra hxN
    have hxge : N ≤ x := Nat.le_of_not_gt (fun h ↦ hxN (Finset.mem_range.mpr h))
    have hsub : Finset.range N ⊆ V.filter (fun y ↦ y < x) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨hroots hy, (Finset.mem_range.mp hy).trans_le hxge⟩
    have hcard : N ≤ couplingLabelRank V x := by
      simpa only [Finset.card_range, couplingLabelRank] using Finset.card_le_card hsub
    exact Nat.not_lt_of_ge hcard (Finset.mem_range.mp hr)
  · intro hxN
    rw [couplingLabelRank_root V N hroots (Finset.mem_range.mp hxN)]
    exact hxN

theorem trajectoryForest_edge_vertices (N : ℕ) (T : ℕ → FiniteCouplingGenealogy)
    (hv : ∀ j, (T j).1.Valid (Finset.range N)) (x y : ℕ)
    (he : (trajectoryForest N T).edge x y) :
    x ∈ (trajectoryForest N T).vertices ∧ y ∈ (trajectoryForest N T).vertices := by
  obtain ⟨j, hy, hyN, hp⟩ := (trajectoryForest_edge N T x y).mp he
  have hx := (hv j).2 y hy hyN |>.1
  rw [hp] at hx
  exact ⟨(trajectoryForest_vertex N T x).mpr ⟨j, hx⟩,
    (trajectoryForest_vertex N T y).mpr ⟨j, hy⟩⟩

theorem trajectoryForest_root_mem (N : ℕ) (T : ℕ → FiniteCouplingGenealogy)
    (hv : ∀ j, (T j).1.Valid (Finset.range N)) (i : Fin N) :
    (trajectoryForest N T).root i ∈ (trajectoryForest N T).vertices :=
  (trajectoryForest_vertex N T i.val).mpr ⟨0, (hv 0).1 (Finset.mem_range.mpr i.isLt)⟩

noncomputable def cofinalChronologicalTrajectory (T : ℕ → FiniteCouplingGenealogy)
    (σ : ℕ → ℕ) : ℕ → FiniteCouplingGenealogy := fun k ↦ (T (σ k)).chronological

noncomputable def cofinalChronologicalEmbedding (N : ℕ) (T : ℕ → FiniteCouplingGenealogy)
    (hmono : ∀ i j, i ≤ j → (T i).1.ChronoLE (T j).1)
    (hv : ∀ j, (T j).1.Valid (Finset.range N))
    (σ : ℕ → ℕ) (hcofinal : ∀ j, ∃ k, j ≤ σ k) :
    RootedForest.Embedding (trajectoryForest N T)
      (trajectoryForest N (cofinalChronologicalTrajectory T σ)) where
  map := globalChronologicalLabel T
  mapsTo := by
    intro x hx
    obtain ⟨j, hxj⟩ := (trajectoryForest_vertex N T x).mp hx
    obtain ⟨k, hjk⟩ := hcofinal j
    have hxk := (hmono j (σ k) hjk).1.1 hxj
    apply (trajectoryForest_vertex N _ _).mpr
    refine ⟨k, ?_⟩
    change globalChronologicalLabel T x ∈ Finset.range (T (σ k)).1.carrier.vertices.card
    rw [globalChronologicalLabel_at_stage T hmono x (σ k) hxk]
    exact Finset.mem_range.mpr (couplingLabelRank_lt_card _ hxk)
  injOn := by
    intro x hx y hy he
    exact globalChronologicalLabel_injOn T hmono
      ((trajectoryForest_vertex N T x).mp hx) ((trajectoryForest_vertex N T y).mp hy) he
  map_root := by
    intro i
    change globalChronologicalLabel T i.val = i.val
    rw [globalChronologicalLabel_at_stage T hmono i.val 0 ((hv 0).1 (Finset.mem_range.mpr i.isLt))]
    exact couplingLabelRank_root _ N (hv 0).1 i.isLt
  map_edge := by
    intro x y he
    obtain ⟨j, hy, hyN, hp⟩ := (trajectoryForest_edge N T x y).mp he
    obtain ⟨k, hjk⟩ := hcofinal j
    have hk := hmono j (σ k) hjk
    have hyk := hk.1.1 hy
    have hx : x ∈ (T j).1.carrier.vertices := by
      have h := ((hv j).2 y hy hyN).1
      rwa [hp] at h
    have hxk := hk.1.1 hx
    have hpK : (T (σ k)).1.parent y = x := (hk.1.2 y hy).symm.trans hp
    apply (trajectoryForest_edge N _ _ _).mpr
    refine ⟨k, ?_, ?_, ?_⟩
    · change globalChronologicalLabel T y ∈ Finset.range (T (σ k)).1.carrier.vertices.card
      rw [globalChronologicalLabel_at_stage T hmono y (σ k) hyk]
      exact Finset.mem_range.mpr (couplingLabelRank_lt_card _ hyk)
    · rw [globalChronologicalLabel_at_stage T hmono y (σ k) hyk]
      exact fun h ↦ hyN ((couplingLabelRank_mem_roots_iff N _ (hv (σ k)).1 hyk).mp h)
    · change (T (σ k)).1.chronological.parent (globalChronologicalLabel T y) = globalChronologicalLabel T x
      rw [globalChronologicalLabel_at_stage T hmono y (σ k) hyk,
        globalChronologicalLabel_at_stage T hmono x (σ k) hxk,
        CouplingGenealogy.chronological_parent_rank _ hyk, hpK]

theorem globalChronologicalLabel_surjOn_cofinal (N : ℕ) (T : ℕ → FiniteCouplingGenealogy)
    (hmono : ∀ i j, i ≤ j → (T i).1.ChronoLE (T j).1) (σ : ℕ → ℕ) :
    Set.SurjOn (globalChronologicalLabel T) (trajectoryForest N T).vertices
      (trajectoryForest N (cofinalChronologicalTrajectory T σ)).vertices := by
  intro n hn
  obtain ⟨k, hk⟩ := (trajectoryForest_vertex N _ n).mp hn
  change n ∈ Finset.range (T (σ k)).1.carrier.vertices.card at hk
  let x := couplingLabelAtRank (T (σ k)).1.carrier.vertices n
  obtain ⟨hx, hrank⟩ := couplingLabelAtRank_spec _ (Finset.mem_range.mp hk)
  refine ⟨x, (trajectoryForest_vertex N T x).mpr ⟨σ k, hx⟩, ?_⟩
  exact (globalChronologicalLabel_at_stage T hmono x (σ k) hx).trans hrank

theorem cofinalChronological_edge_reflects (N : ℕ) (T : ℕ → FiniteCouplingGenealogy)
    (hmono : ∀ i j, i ≤ j → (T i).1.ChronoLE (T j).1)
    (hv : ∀ j, (T j).1.Valid (Finset.range N)) (σ : ℕ → ℕ)
    (x : ℕ) (hx : x ∈ (trajectoryForest N T).vertices)
    (y : ℕ) (hy : y ∈ (trajectoryForest N T).vertices)
    (he : (trajectoryForest N (cofinalChronologicalTrajectory T σ)).edge
      (globalChronologicalLabel T x) (globalChronologicalLabel T y)) :
    (trajectoryForest N T).edge x y := by
  obtain ⟨k, hny, hnyN, hp⟩ := (trajectoryForest_edge N _ _ _).mp he
  let V := (T (σ k)).1.carrier.vertices
  change globalChronologicalLabel T y ∈ Finset.range V.card at hny
  let z := couplingLabelAtRank V (globalChronologicalLabel T y)
  obtain ⟨hz, hzrank⟩ := couplingLabelAtRank_spec V (Finset.mem_range.mp hny)
  have hzglob : globalChronologicalLabel T z = globalChronologicalLabel T y :=
    (globalChronologicalLabel_at_stage T hmono z (σ k) hz).trans hzrank
  have hzy : z = y := globalChronologicalLabel_injOn T hmono
    ⟨σ k, hz⟩ ((trajectoryForest_vertex N T y).mp hy) hzglob
  have hyK : y ∈ V := hzy ▸ hz
  have hyrank := globalChronologicalLabel_at_stage T hmono y (σ k) hyK
  have hyN : y ∉ Finset.range N := by
    intro hyN
    apply hnyN
    rw [hyrank]
    exact (couplingLabelRank_mem_roots_iff N V (hv (σ k)).1 hyK).mpr hyN
  have hpar := ((hv (σ k)).2 y hyK hyN).1
  have hglobpar : globalChronologicalLabel T ((T (σ k)).1.parent y) = globalChronologicalLabel T x := by
    rw [globalChronologicalLabel_at_stage T hmono _ (σ k) hpar]
    change (T (σ k)).1.chronological.parent (globalChronologicalLabel T y) = globalChronologicalLabel T x at hp
    rw [hyrank, CouplingGenealogy.chronological_parent_rank _ hyK] at hp
    exact hp
  have hparent : (T (σ k)).1.parent y = x := globalChronologicalLabel_injOn T hmono
    ⟨σ k, hpar⟩ ((trajectoryForest_vertex N T x).mp hx) hglobpar
  exact (trajectoryForest_edge N T x y).mpr ⟨σ k, hyK, hyN, hparent⟩

noncomputable def cofinalChronologicalInverseEmbedding (N : ℕ) (T : ℕ → FiniteCouplingGenealogy)
    (hmono : ∀ i j, i ≤ j → (T i).1.ChronoLE (T j).1)
    (hv : ∀ j, (T j).1.Valid (Finset.range N))
    (σ : ℕ → ℕ) (hcofinal : ∀ j, ∃ k, j ≤ σ k) :
    RootedForest.Embedding (trajectoryForest N (cofinalChronologicalTrajectory T σ)) (trajectoryForest N T) :=
  (cofinalChronologicalEmbedding N T hmono hv σ hcofinal).reverse
    (globalChronologicalLabel_surjOn_cofinal N T hmono σ)
    (trajectoryForest_root_mem N T hv)
    (trajectoryForest_edge_vertices N _ (fun k ↦ CouplingGenealogy.chronological_valid _ N (hv (σ k))))
    (cofinalChronological_edge_reflects N T hmono hv σ)

end HeightPaper.CountCoupling
