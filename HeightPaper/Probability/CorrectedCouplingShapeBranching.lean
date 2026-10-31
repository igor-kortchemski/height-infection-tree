module

public import HeightPaper.Probability.CorrectedCouplingShapeLaw
public import HeightPaper.Combinatorics.FiniteShapeGeometry
public import HeightPaper.Combinatorics.PlaneGeometricBienayme

/-!
# Genuine geometric Bienaymé laws of the finite component shapes

The atom formula and first-child decomposition prove a measure fixed point.
The full conditional joint law of all child trees, and identification with
the concrete iid offspring construction, follow from the branching library.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HeightPaper.CountCoupling

open PlaneForward PlaneTree
open scoped Classical

theorem shapeAtomWeight_graft (a : ℝ) (A B : FiniteShape) :
    a ^ (graftShapes A B).size * (1 - a) ^ ((graftShapes A B).size - 1) =
      (1 - a) * (a ^ A.size * (1 - a) ^ (A.size - 1)) *
        (a ^ B.size * (1 - a) ^ (B.size - 1)) := by
  obtain ⟨m, hm⟩ : ∃ m, A.size = m + 1 := ⟨A.size - 1, by have := A.size_pos; omega⟩
  obtain ⟨n, hn⟩ : ∃ n, B.size = n + 1 := ⟨B.size - 1, by have := B.size_pos; omega⟩
  rw [graftShapes_size, hm, hn]
  have hsum : m + 1 + (n + 1) - 1 = m + n + 1 := by omega
  simp only [Nat.add_sub_cancel, hsum, pow_add, pow_one]
  ring

theorem graftShapes_ne_leaf (A B : FiniteShape) : graftShapes A B ≠ leafShape := by
  intro he
  have hd := congrArg (fun t : FiniteShape ↦ degree t.tree) he
  rw [graftShapes_tree, degree_graft, leafShape_tree, degree_leaf] at hd
  omega

theorem oneRootShapeLaw_fixedPoint {a : ℝ} (ha : 1 / 2 < a) (ha1 : a ≤ 1) :
    oneRootShapeLaw a = ENNReal.ofReal a • Measure.dirac leafShape +
      ENNReal.ofReal (1 - a) • ((oneRootShapeLaw a).prod (oneRootShapeLaw a)).map
        (fun z ↦ graftShapes z.1 z.2) := by
  have ha0 : 0 ≤ a := by linarith
  have hq0 : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hG : Measurable (fun z : FiniteShape × FiniteShape ↦ graftShapes z.1 z.2) := measurable_of_countable _
  apply Measure.ext_of_singleton
  intro t
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton t), Measure.map_apply hG (measurableSet_singleton t)]
  rcases finiteShape_split t with he | ⟨A, B, he⟩
  · subst t
    have hpre : (fun z : FiniteShape × FiniteShape ↦ graftShapes z.1 z.2) ⁻¹' {leafShape} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact graftShapes_ne_leaf z.1 z.2 hz
    rw [hpre, measure_empty, oneRootShapeLaw_atom ha ha1, leafShape_size]
    simp
  · have hpre : (fun z : FiniteShape × FiniteShape ↦ graftShapes z.1 z.2) ⁻¹' {t} = {A} ×ˢ {B} := by
      ext z
      change graftShapes z.1 z.2 = t ↔ z.1 = A ∧ z.2 = B
      constructor
      · intro hz
        have h : z = (A, B) := graftShapes_injective (hz.trans he.symm)
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      · rintro ⟨ha, hb⟩
        rw [ha, hb, he]
    have hleaf : leafShape ∉ ({t} : Set FiniteShape) := by
      intro ht
      exact graftShapes_ne_leaf A B (he.trans ht.symm)
    rw [Set.indicator_of_notMem hleaf, mul_zero, zero_add, hpre, Measure.prod_prod,
      oneRootShapeLaw_atom ha ha1 A, oneRootShapeLaw_atom ha ha1 B, ← he,
      oneRootShapeLaw_atom ha ha1, shapeAtomWeight_graft,
      ENNReal.ofReal_mul (mul_nonneg hq0 (mul_nonneg (pow_nonneg ha0 _) (pow_nonneg hq0 _))),
      ENNReal.ofReal_mul hq0]
    ring

noncomputable def oneRootPlaneLaw (a : ℝ) : Measure Tree :=
  (oneRootShapeLaw a).map FiniteShape.tree

theorem measurable_finiteShape_tree : Measurable FiniteShape.tree := measurable_of_countable _

instance (a : ℝ) : IsProbabilityMeasure (oneRootPlaneLaw a) := by
  unfold oneRootPlaneLaw
  infer_instance

theorem oneRootPlaneLaw_fixedPoint {a : ℝ} (ha : 1 / 2 < a) (ha1 : a ≤ 1) :
    oneRootPlaneLaw a = ENNReal.ofReal a • Measure.dirac leaf +
      ENNReal.ofReal (1 - a) • ((oneRootPlaneLaw a).prod (oneRootPlaneLaw a)).map
        (fun z ↦ graft z.1 z.2) := by
  let G : FiniteShape × FiniteShape → FiniteShape := fun z ↦ graftShapes z.1 z.2
  have hG : Measurable G := measurable_of_countable _
  have hcomp : FiniteShape.tree ∘ G = (fun z : Tree × Tree ↦ graft z.1 z.2) ∘
      Prod.map FiniteShape.tree FiniteShape.tree := by
    funext z
    exact graftShapes_tree z.1 z.2
  unfold oneRootPlaneLaw
  conv_lhs => rw [oneRootShapeLaw_fixedPoint ha ha1, Measure.map_add _ _ measurable_finiteShape_tree,
    Measure.map_smul _ measurable_finiteShape_tree.aemeasurable,
    Measure.map_smul _ measurable_finiteShape_tree.aemeasurable]
  rw [Measure.map_dirac' measurable_finiteShape_tree leafShape, leafShape_tree,
    Measure.map_map measurable_finiteShape_tree hG, hcomp,
    ← Measure.map_map continuous_graft.measurable
      (measurable_finiteShape_tree.prodMap measurable_finiteShape_tree),
    ← Measure.map_prod_map _ _ measurable_finiteShape_tree measurable_finiteShape_tree]

theorem oneRootPlaneLaw_isBienayme (a : unitInterval) (ha : 1 / 2 < (a : ℝ)) :
    IsBienayme (oneRootPlaneLaw a) (geometricMeasure a) := by
  let b := unitInterval.symm a
  have hb : (b : ℝ) < 1 := by change 1 - (a : ℝ) < 1; linarith
  have hf := oneRootPlaneLaw_fixedPoint ha a.2.2
  have hfix : oneRootPlaneLaw a = ENNReal.ofReal (1 - (b : ℝ)) • Measure.dirac leaf +
      ENNReal.ofReal (b : ℝ) • ((oneRootPlaneLaw a).prod (oneRootPlaneLaw a)).map
        (fun z ↦ graft z.1 z.2) := by
    change oneRootPlaneLaw a = ENNReal.ofReal (1 - (1 - (a : ℝ))) • Measure.dirac leaf + _
    rw [sub_sub_cancel]
    exact hf
  have hsym : unitInterval.symm b = a := by
    apply Subtype.ext
    change 1 - (1 - (a : ℝ)) = (a : ℝ)
    ring
  simpa only [hsym] using isBienayme_geometric_of_fixedPoint b hb (oneRootPlaneLaw a) hfix

theorem oneRootPlaneLaw_eq_bienaymeLaw (a : unitInterval) (ha : 1 / 2 < (a : ℝ)) :
    oneRootPlaneLaw a = bienaymeLaw (geometricMeasure a) :=
  (oneRootPlaneLaw_isBienayme a ha).eq_bienaymeLaw

end HeightPaper.CountCoupling
