module

public import HeightPaper.Probability.CorrectedCouplingPastUpper

/-!
# The full joint measure of accepted labels and recovery draws

Rectangle mass identities determine a subprobability measure on the pair.
Consequently any measurable update of the accepted pair can be transported
without redoing the rejection proof for each target state.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace HeightPaper.CountCoupling

theorem measure_eq_of_singleton_sections
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] (μ ν : Measure (α × β))
    (h : ∀ a (D : Set β), MeasurableSet D → μ ({a} ×ˢ D) = ν ({a} ×ˢ D)) : μ = ν := by
  ext S hS
  let D : α → Set β := fun a ↦ (fun b ↦ (a, b)) ⁻¹' S
  have hD (a : α) : MeasurableSet (D a) := hS.preimage (measurable_const.prodMk measurable_id)
  have hset : S = ⋃ a, ({a} ×ˢ D a) := by
    ext z
    simp [D]
  have hdisj : Pairwise (Disjoint on fun a ↦ ({a} ×ˢ D a)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    rintro z ⟨ha, _⟩ ⟨hb, _⟩
    exact hab (ha.symm.trans hb)
  rw [hset, measure_iUnion hdisj (fun a ↦ (measurableSet_singleton a).prod (hD a)),
    measure_iUnion hdisj (fun a ↦ (measurableSet_singleton a).prod (hD a))]
  exact tsum_congr (fun a ↦ h a (D a) (hD a))

noncomputable def acceptedPairMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : ℕ → Set Ω) (V : ℕ → Ω → ℕ) (R : ℕ → Ω → ℝ) : Measure (ℕ × ℝ) :=
  Measure.sum (fun n ↦ (μ.restrict (E n)).map (fun ω ↦ (V n ω, R n ω)))

theorem acceptedPairMeasure_singleton_section
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet (E n))
    (V : ℕ → Ω → ℕ) (R : ℕ → Ω → ℝ)
    (hV : ∀ n, Measurable (V n)) (hR : ∀ n, Measurable (R n))
    (hdisj : Pairwise (Disjoint on E)) (v : ℕ) (D : Set ℝ) (hD : MeasurableSet D) :
    acceptedPairMeasure μ E V R ({v} ×ˢ D) =
      μ (⋃ n, {ω | ω ∈ E n ∧ V n ω = v ∧ R n ω ∈ D}) := by
  let F := fun n ↦ {ω | ω ∈ E n ∧ V n ω = v ∧ R n ω ∈ D}
  have hF (n : ℕ) : MeasurableSet (F n) :=
    (hE n).inter (((hV n) (measurableSet_singleton v)).inter ((hR n) hD))
  have hp : Pairwise (Disjoint on F) := by
    intro i j hij
    exact (hdisj hij).mono (fun _ h ↦ h.1) (fun _ h ↦ h.1)
  rw [acceptedPairMeasure, Measure.sum_apply _ ((measurableSet_singleton v).prod hD),
    measure_iUnion hp hF]
  apply tsum_congr
  intro n
  rw [Measure.map_apply ((hV n).prodMk (hR n)) ((measurableSet_singleton v).prod hD),
    Measure.restrict_apply (((measurableSet_singleton v).prod hD).preimage ((hV n).prodMk (hR n)))]
  congr 1
  ext ω
  simp [F, and_comm, and_left_comm]

theorem acceptedPairMeasure_eq_prod_of_masses
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet (E n))
    (V : ℕ → Ω → ℕ) (R : ℕ → Ω → ℝ)
    (hV : ∀ n, Measurable (V n)) (hR : ∀ n, Measurable (R n))
    (hdisj : Pairwise (Disjoint on E)) (A : Finset ℕ) (c : ℝ≥0∞)
    (hsupport : ∀ n ω, ω ∈ E n → V n ω ∈ A)
    (hmass : ∀ v ∈ A, ∀ D : Set ℝ, MeasurableSet D →
      μ (⋃ n, {ω | ω ∈ E n ∧ V n ω = v ∧ R n ω ∈ D}) =
        (A.card : ℝ≥0∞)⁻¹ * c * unitUniform D) :
    acceptedPairMeasure μ E V R = c • (Measure.uniformOfFinset A).prod unitUniform := by
  apply measure_eq_of_singleton_sections
  intro v D hD
  rw [acceptedPairMeasure_singleton_section μ E hE V R hV hR hdisj v D hD,
    Measure.smul_apply, smul_eq_mul, Measure.prod_prod,
    Measure.uniformOfFinset_apply_singleton]
  by_cases hv : v ∈ A
  · rw [ite_eq_left hv, hmass v hv D hD]
    ac_rfl
  · rw [ite_eq_right hv]
    have heq : (⋃ n, {ω | ω ∈ E n ∧ V n ω = v ∧ R n ω ∈ D}) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      obtain ⟨n, hn, he, _⟩ := Set.mem_iUnion.mp hω
      exact hv (he ▸ hsupport n ω hn)
    rw [heq]
    simp only [measure_empty, zero_mul, mul_zero]

/-- Full accepted-pair law for the concrete upper forest, starting on any
causal past event. This is a measure identity, not merely marginal laws. -/
theorem upperPast_acceptedPairMeasure_eq_prod
    (N : ℕ) (hN : 0 < N) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (j : ℕ) (H : Set ((Fin 2 × ℕ) → ℝ)) (hH : MeasurableSet H)
    (hcausal : ∀ w z, (∀ i, i.2 < j → w i = z i) → (w ∈ H ↔ z ∈ H))
    (A : Finset ℕ) (hA : A.Nonempty)
    (hinit : ∀ w ∈ H, A ⊆ (upperCarrier (Finset.range N) p w j).active) :
    let V : ℕ → ((Fin 2 × ℕ) → ℝ) → ℕ := fun n w ↦ selectFinite ((upperCarrier (Finset.range N) p w (j + n)).active ∪ A)
      (hA.mono Finset.subset_union_right) (w (0, j + n))
    let E : ℕ → Set ((Fin 2 × ℕ) → ℝ) := fun n ↦ {w | upperPastPending A (Finset.range N) hA p j H w n = true ∧ V n w ∈ A}
    acceptedPairMeasure pairedUniformLaw E V (fun n w ↦ w (1, j + n)) =
      pairedUniformLaw H • (Measure.uniformOfFinset A).prod unitUniform := by
  let roots := Finset.range N
  let V : ℕ → ((Fin 2 × ℕ) → ℝ) → ℕ := fun n w ↦ selectFinite ((upperCarrier roots p w (j + n)).active ∪ A)
    (hA.mono Finset.subset_union_right) (w (0, j + n))
  let E : ℕ → Set ((Fin 2 × ℕ) → ℝ) := fun n ↦ {w | upperPastPending A roots hA p j H w n = true ∧ V n w ∈ A}
  have hV (n : ℕ) : Measurable (V n) := by
    have hsel : Measurable (fun z : CouplingCarrier × ℝ ↦
        selectFinite (z.1.active ∪ A) (hA.mono Finset.subset_union_right) z.2) :=
      measurable_from_prod_countable_right (fun s ↦
        measurable_selectFinite (s.active ∪ A) (hA.mono Finset.subset_union_right))
    have harg : Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦
        (upperCarrier roots p w (j + n), w (0, j + n))) :=
      (measurable_upperCarrier roots p (j + n)).prodMk (measurable_pi_apply (0, j + n))
    simpa only [Function.comp_def, V] using hsel.comp harg
  have hE (n : ℕ) : MeasurableSet (E n) :=
    ((measurable_upperPastPending A roots hA p j H hH n) (measurableSet_singleton true)).inter
      ((hV n) A.measurableSet)
  let C : ℕ → ((Fin 2 × ℕ) → ℝ) → Finset ℕ × Bool := fun n w ↦
    ((upperCarrier roots p w (j + n)).active, upperPastPending A roots hA p j H w n)
  have hdisj : Pairwise (Disjoint on E) :=
    coded_first_acceptance_pairwise A hA C (fun n w ↦ w (0, j + n))
      (fun n w ↦ upperPastPending_succ A roots hA p j H w n)
  apply acceptedPairMeasure_eq_prod_of_masses pairedUniformLaw E hE V
    (fun n w ↦ w (1, j + n)) hV (fun n ↦ measurable_pi_apply (1, j + n)) hdisj A
    (pairedUniformLaw H) (fun _ _ h ↦ h.2)
  intro v hv D hD
  have heq : (⋃ n, {w | w ∈ E n ∧ V n w = v ∧ w (1, j + n) ∈ D}) =
      ⋃ n, {w | upperPastPending A roots hA p j H w n = true ∧ V n w = v ∧ w (1, j + n) ∈ D} := by
    ext w
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, ⟨hn, _⟩, he, hd⟩
      exact ⟨n, hn, he, hd⟩
    · rintro ⟨n, hn, he, hd⟩
      exact ⟨n, ⟨hn, he ▸ hv⟩, he, hd⟩
  rw [heq]
  exact upperPast_first_accepted_joint_law N hN hp hp1 j H hH hcausal A hA hinit hv D hD

end HeightPaper.CountCoupling
