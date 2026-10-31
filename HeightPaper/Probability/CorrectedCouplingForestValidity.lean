module

public import HeightPaper.Probability.CorrectedCouplingRootedSandwich
public import HeightPaper.Combinatorics.RootedForestValidity

/-!
# The countable limits are genuine rooted forests

Each nonroot vertex has one parent, every vertex is reachable from an indexed
root, and no directed cycles occur. Validity is retained off the favorable
coupling event; the middle is allowed to be infinite there.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

theorem CouplingGenealogy.root_path (N : ℕ) (s : CouplingGenealogy) (hs : s.Valid (Finset.range N))
    {x : ℕ} (hx : x ∈ s.carrier.vertices) :
    Relation.ReflTransGen (finiteGenealogyForest N s).edge (s.rootOf (Finset.range N) x) x := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
      by_cases hr : x ∈ Finset.range N
      · have he : s.rootOf (Finset.range N) x = x := by simp [CouplingGenealogy.rootOf, hr]
        rw [he]
      · obtain ⟨hp, hlt⟩ := hs.2 x hx hr
        rw [s.rootOf_parent hs hx hr]
        exact (ih (s.parent x) hlt hp).tail ⟨hx, hr, rfl⟩

noncomputable def finiteToTrajectoryEmbedding (N : ℕ) (T : ℕ → FiniteCouplingGenealogy) (j : ℕ) :
    RootedForest.Embedding (finiteGenealogyForest N (T j).1) (trajectoryForest N T) where
  map := id
  mapsTo := fun x hx ↦ (trajectoryForest_vertex N T x).mpr ⟨j, hx⟩
  injOn := fun _ _ _ _ he ↦ he
  map_root := fun _ ↦ rfl
  map_edge := fun x y he ↦ (trajectoryForest_edge N T x y).mpr ⟨j, he⟩

theorem trajectoryForest_wellRooted (N : ℕ) (T : ℕ → FiniteCouplingGenealogy)
    (hmono : ∀ i j, i ≤ j → (T i).1.TreeLE (T j).1)
    (hv : ∀ j, (T j).1.Valid (Finset.range N)) : RootedForest.WellRooted (trajectoryForest N T) := by
  constructor
  · exact trajectoryForest_root_mem N T hv
  · intro i j he
    exact Fin.ext he
  · exact trajectoryForest_edge_vertices N T hv
  · intro x i he
    obtain ⟨j, _, hn, _⟩ := (trajectoryForest_edge N T x i.val).mp he
    exact hn (Finset.mem_range.mpr i.isLt)
  · intro x hx hxr
    obtain ⟨j, hxj⟩ := (trajectoryForest_vertex N T x).mp hx
    have hxN : x ∉ Finset.range N := by
      intro hxN
      exact hxr ⟨x, Finset.mem_range.mp hxN⟩ rfl
    refine ⟨(T j).1.parent x, (trajectoryForest_edge N T _ x).mpr ⟨j, hxj, hxN, rfl⟩, ?_⟩
    intro q hq
    obtain ⟨k, hxk, _, hp⟩ := (trajectoryForest_edge N T q x).mp hq
    have hj := hmono j (max j k) (le_max_left _ _)
    have hk := hmono k (max j k) (le_max_right _ _)
    exact hp.symm.trans ((hk.2 x hxk).trans (hj.2 x hxj).symm)
  · intro x hx
    obtain ⟨j, hxj⟩ := (trajectoryForest_vertex N T x).mp hx
    let i : Fin N := ⟨(T j).1.rootOf (Finset.range N) x,
      Finset.mem_range.mp ((T j).1.rootOf_mem_roots (hv j) hxj)⟩
    have hp : Relation.ReflTransGen (finiteGenealogyForest N (T j).1).edge
        ((finiteGenealogyForest N (T j).1).root i) x := (T j).1.root_path N (hv j) hxj
    exact ⟨i, ((finiteToTrajectoryEmbedding N T j).mapsTo_component i ⟨hxj, hp⟩).2⟩
  · have hedge (x y : ℕ) (he : (trajectoryForest N T).edge x y) : x < y := by
      obtain ⟨j, hy, hyN, hp⟩ := (trajectoryForest_edge N T x y).mp he
      have hlt := ((hv j).2 y hy hyN).2
      rwa [hp] at hlt
    have htrans (x y : ℕ) (h : Relation.TransGen (trajectoryForest N T).edge x y) : x < y := by
      induction h with
      | single he => exact hedge _ _ he
      | tail hxy hyz ih => exact ih.trans (hedge _ _ hyz)
    intro x hx
    exact (Nat.lt_irrefl x) (htrans x x hx)

theorem correctedMiddleLimitCode_wellRooted
    (N : ℕ) {p q : ℝ} (hpq : p ≤ q) (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ)
    (hu : ∀ k, ∃ j, k < correctedCouplingClock (Finset.range N) p q r w j) :
    RootedForest.WellRooted (forestOfCode N (correctedMiddleLimitCode N p q r w)) := by
  let T := physicalMiddleTrajectory (Finset.range N) p q r w
  let σ := couplingLogicalTime (Finset.range N) p q r w
  have hmono := physicalMiddleTrajectory_chronoLE (Finset.range N) p q r w
  have hv := physicalMiddleTrajectory_valid N hpq r w
  have hcofinal (j : ℕ) : ∃ k, j ≤ σ k := ⟨j, couplingLogicalTime_ge (Finset.range N) p q r w hu j⟩
  have hA := trajectoryForest_wellRooted N T (fun i j hij ↦ (hmono i j hij).1) hv
  exact hA.of_embedding (cofinalChronologicalEmbedding N T hmono hv σ hcofinal)
    (globalChronologicalLabel_surjOn_cofinal N T hmono σ)
    (trajectoryForest_edge_vertices N _ (fun k ↦ CouplingGenealogy.chronological_valid _ N (hv (σ k))))
    (cofinalChronological_edge_reflects N T hmono hv σ)

theorem correctedMiddleLimitCode_ae_wellRooted
    (N : ℕ) (hN : 0 < N) {p q : ℝ} (hp : 1 / 2 < p) (hpq : p ≤ q) (hq1 : q ≤ 1)
    (r : List Bool → ℝ) :
    ∀ᵐ w ∂pairedUniformLaw, RootedForest.WellRooted (forestOfCode N (correctedMiddleLimitCode N p q r w)) := by
  filter_upwards [correctedCouplingClock_ae_unbounded N hN hp (hpq.trans hq1) q r] with w hw
  exact correctedMiddleLimitCode_wellRooted N hpq r w hw

theorem FiniteCouplingGenealogy.sourceStep_treeLE (s : FiniteCouplingGenealogy)
    (hs : s.1.Dense) (b : Bool) (u : ℝ) : s.1.TreeLE (s.sourceStep b u).1 := by
  by_cases hA : s.1.carrier.active.Nonempty
  · have hf : s.1.carrier.vertices.card ∉ s.1.carrier.vertices := by rw [hs]; simp
    simpa only [FiniteCouplingGenealogy.sourceStep, dite_eq_left hA, FiniteCouplingGenealogy.update] using
      s.1.treeLE_update (selectFinite s.1.carrier.active hA u) s.1.carrier.vertices.card hf b
  · simp only [FiniteCouplingGenealogy.sourceStep, dite_eq_right hA]
    exact s.1.treeLE_refl

theorem sourceForestTrajectory_treeLE (N : ℕ) (x : ℕ → Bool) (u : ℕ → ℝ)
    (i j : ℕ) (hij : i ≤ j) :
    (sourceForestTrajectory N x u i).1.TreeLE (sourceForestTrajectory N x u j).1 := by
  induction j, hij using Nat.le_induction with
  | base => exact CouplingGenealogy.treeLE_refl _
  | succ j _ ih =>
      exact CouplingGenealogy.treeLE_trans ih
        ((sourceForestTrajectory N x u j).sourceStep_treeLE (sourceForestTrajectory_dense N x u j) _ _)

theorem sourceForestLimit_wellRooted (N : ℕ) (x : ℕ → Bool) (u : ℕ → ℝ) :
    RootedForest.WellRooted (trajectoryForest N (sourceForestTrajectory N x u)) :=
  trajectoryForest_wellRooted N _ (sourceForestTrajectory_treeLE N x u) (sourceForestTrajectory_valid N x u)

end HeightPaper.CountCoupling
