module

public import HeightPaper.Probability.CorrectedCouplingRanks
public import HeightPaper.Probability.CorrectedCouplingSourceProduct

/-!
# The source uniform-attachment forest for arbitrary root count

All vertices have dense chronological labels. At each event a fresh uniform
chooses an active vertex; recovery freezes it, birth adds the next label, and
empty active sets are absorbing. This is Algorithm 1 for all `N`, not only its
one-root specialization.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

def CouplingGenealogy.Dense (s : CouplingGenealogy) : Prop :=
  s.carrier.vertices = Finset.range s.carrier.vertices.card

theorem CouplingGenealogy.chronological_dense (s : CouplingGenealogy) : s.chronological.Dense := by
  simp [CouplingGenealogy.Dense, CouplingGenealogy.chronological]

noncomputable def FiniteCouplingGenealogy.sourceStep (s : FiniteCouplingGenealogy)
    (b : Bool) (u : ℝ) : FiniteCouplingGenealogy :=
  if h : s.1.carrier.active.Nonempty then
    s.update (selectFinite s.1.carrier.active h u) s.1.carrier.vertices.card b
  else s

theorem FiniteCouplingGenealogy.sourceStep_of_empty (s : FiniteCouplingGenealogy)
    (hs : s.1.carrier.active = ∅) (b : Bool) (u : ℝ) : s.sourceStep b u = s := by
  simp [FiniteCouplingGenealogy.sourceStep, hs]

theorem FiniteCouplingGenealogy.sourceStep_dense (s : FiniteCouplingGenealogy)
    (hs : s.1.Dense) (b : Bool) (u : ℝ) : (s.sourceStep b u).1.Dense := by
  by_cases h : s.1.carrier.active.Nonempty
  · have hv : selectFinite s.1.carrier.active h u ∈ s.1.carrier.active := selectFinite_mem _ h u
    have hf : s.1.carrier.vertices.card ∉ s.1.carrier.vertices := by rw [hs]; simp
    cases b
    · simpa [FiniteCouplingGenealogy.sourceStep, h, FiniteCouplingGenealogy.update,
        CouplingGenealogy.update, CouplingCarrier.update, hv, CouplingGenealogy.Dense] using hs
    · change (s.sourceStep true u).1.carrier.vertices =
        Finset.range (s.sourceStep true u).1.carrier.vertices.card
      simp only [FiniteCouplingGenealogy.sourceStep, dite_eq_left h,
        FiniteCouplingGenealogy.update, CouplingGenealogy.update, CouplingCarrier.update,
        hv, ↓reduceIte, Finset.card_insert_of_notMem hf]
      rw [Finset.range_add_one]
      exact congrArg (insert s.1.carrier.vertices.card) hs
  · simpa [FiniteCouplingGenealogy.sourceStep, h] using hs

theorem FiniteCouplingGenealogy.sourceStep_valid (s : FiniteCouplingGenealogy)
    (N : ℕ) (hs : s.1.Valid (Finset.range N)) (hd : s.1.Dense) (b : Bool) (u : ℝ) :
    (s.sourceStep b u).1.Valid (Finset.range N) := by
  by_cases h : s.1.carrier.active.Nonempty
  · have hgt : ∀ x ∈ s.1.carrier.vertices, x < s.1.carrier.vertices.card := by
      intro x hx
      rw [hd] at hx
      exact Finset.mem_range.mp hx
    simpa only [FiniteCouplingGenealogy.sourceStep, dite_eq_left h,
      FiniteCouplingGenealogy.update] using s.1.valid_update hs
        (selectFinite s.1.carrier.active h u) s.1.carrier.vertices.card hgt b
  · simpa [FiniteCouplingGenealogy.sourceStep, h] using hs

theorem FiniteCouplingGenealogy.measurable_sourceStep (s : FiniteCouplingGenealogy) :
    Measurable (fun z : Bool × ℝ ↦ s.sourceStep z.1 z.2) := by
  by_cases h : s.1.carrier.active.Nonempty
  · have hsel := (measurable_selectFinite s.1.carrier.active h).comp
      (measurable_snd : Measurable (Prod.snd : Bool × ℝ → ℝ))
    simpa only [FiniteCouplingGenealogy.sourceStep, dite_eq_left h, Function.comp_def] using
      (measurable_of_countable (fun d : Bool × ℕ ↦
        s.update d.2 s.1.carrier.vertices.card d.1)).comp (measurable_fst.prodMk hsel)
  · simp [FiniteCouplingGenealogy.sourceStep, h]

noncomputable def sourceForestTrajectory (N : ℕ) (x : ℕ → Bool) (u : ℕ → ℝ) :
    ℕ → FiniteCouplingGenealogy
  | 0 => FiniteCouplingGenealogy.initial (Finset.range N)
  | k + 1 => (sourceForestTrajectory N x u k).sourceStep (x k) (u k)

theorem sourceForestTrajectory_dense (N : ℕ) (x : ℕ → Bool) (u : ℕ → ℝ) (k : ℕ) :
    (sourceForestTrajectory N x u k).1.Dense := by
  induction k with
  | zero => simp [sourceForestTrajectory, FiniteCouplingGenealogy.initial,
      CouplingGenealogy.initial, CouplingGenealogy.Dense]
  | succ k ih => exact FiniteCouplingGenealogy.sourceStep_dense _ ih _ _

theorem sourceForestTrajectory_valid (N : ℕ) (x : ℕ → Bool) (u : ℕ → ℝ) (k : ℕ) :
    (sourceForestTrajectory N x u k).1.Valid (Finset.range N) := by
  induction k with
  | zero => exact CouplingGenealogy.initial_valid _
  | succ k ih =>
      exact FiniteCouplingGenealogy.sourceStep_valid _ N ih
        (sourceForestTrajectory_dense N x u k) _ _

theorem measurable_sourceForestTrajectory (N : ℕ) :
    Measurable (fun z : (ℕ → Bool) × (ℕ → ℝ) ↦ sourceForestTrajectory N z.1 z.2) := by
  have hstep : Measurable (fun z : FiniteCouplingGenealogy × (Bool × ℝ) ↦
      z.1.sourceStep z.2.1 z.2.2) :=
    measurable_from_prod_countable_right (fun s ↦ s.measurable_sourceStep)
  apply measurable_pi_iff.mpr
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      exact hstep.comp (ih.prodMk
        (((measurable_pi_apply k).comp measurable_fst).prodMk
          ((measurable_pi_apply k).comp measurable_snd)))

/-- The arbitrary source word with independent parents gives exactly the
same joint forest law as its adaptive-uniform realization, for every `N`. -/
theorem adaptiveSourceForestTrajectory_law
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (r : List Bool → ℝ) (hr : ∀ a, 0 ≤ r a ∧ r a ≤ 1)
    (hfactor : ∀ (k : ℕ) (a : List Bool) (b : Bool), a.length = k →
      μ {x | sourceCouplingPrefix x (k + 1) = a ++ [b]} =
        μ {x | sourceCouplingPrefix x k = a} * adaptiveStepMass (r a) b)
    (N : ℕ) :
    birthParentLaw.map (fun z ↦ (adaptiveCouplingProcess r z.1,
      sourceForestTrajectory N (adaptiveCouplingProcess r z.1) z.2)) =
    (μ.prod uniformLaw).map (fun z ↦ (z.1, sourceForestTrajectory N z.1 z.2)) := by
  let F : ((ℕ → Bool) × (ℕ → ℝ)) → (ℕ → Bool) × (ℕ → FiniteCouplingGenealogy) :=
    fun z ↦ (z.1, sourceForestTrajectory N z.1 z.2)
  have hF : Measurable F := measurable_fst.prodMk (measurable_sourceForestTrajectory N)
  have hP : Measurable (Prod.map (adaptiveCouplingProcess r) id :
      ((ℕ → ℝ) × (ℕ → ℝ)) → ((ℕ → Bool) × (ℕ → ℝ))) :=
    (measurable_adaptiveCouplingProcess r).prodMap measurable_id
  change birthParentLaw.map (F ∘ Prod.map (adaptiveCouplingProcess r) id) =
    (μ.prod uniformLaw).map F
  rw [← Measure.map_map hF hP, ← adaptiveSourceParentLaw_eq_prod μ r hr hfactor]
  rfl

end HeightPaper.CountCoupling
