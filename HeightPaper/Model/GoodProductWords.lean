module

public import HeightPaper.Model.GlobalNormalizerBounds
public import HeightPaper.Probability.GoodEventWords

/-!
# Prefix-closed count and product control

The good-word class contains exactly the positive counts and uniform product
inequalities used by the finite moment bootstrap. Its constants depend only
on the fixed count tolerances and the fixed initial cutoff, never on the word
or terminal time. Actual epidemic good-count events imply this class.
-/

public section

namespace HeightPaper.Model

structure GoodProductWord (lowerSlope upperSlope c : ℝ) (A B : ℝ → ℝ)
    (K N : ℕ) (events : ℕ → Bool) : Prop where
  positive : ∀ k ≤ N, 0 < prescribedWalk events 1 k
  count : ∀ k ∈ Finset.Icc K N, c * k ≤ (prescribedWalk events 1 k : ℝ)
  lower : ∀ w ≥ (1 : ℝ), ∀ k ∈ Finset.Icc K N,
    A w * (k : ℝ) ^ ((w - 1) * lowerSlope) ≤ realNormalizer w events 1 k
  upper : ∀ w ≥ (1 : ℝ), ∀ k ∈ Finset.Icc K N,
    realNormalizer w events 1 k ≤ B w * (k : ℝ) ^ ((w - 1) * upperSlope)

theorem GoodProductWord.prefix {lowerSlope upperSlope c : ℝ} {A B : ℝ → ℝ}
    {K N j : ℕ} {events : ℕ → Bool}
    (h : GoodProductWord lowerSlope upperSlope c A B K N events) (hj : j ≤ N) :
    GoodProductWord lowerSlope upperSlope c A B K j events where
  positive k hk := h.positive k (hk.trans hj)
  count k hk := h.count k (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans hj⟩)
  lower w hw k hk := h.lower w hw k (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans hj⟩)
  upper w hw k hk := h.upper w hw k (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans hj⟩)

/-- The whole family of product constants can be selected before the event
word or its terminal horizon is chosen. -/
theorem exists_goodProductWord_constants {lo hi c a L : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi) (ha : 0 < a) (K : ℕ) (hK : 1 ≤ K) :
    ∃ A B : ℝ → ℝ, (∀ w ≥ (1 : ℝ), 0 < A w ∧ 0 < B w) ∧
      ∀ (events : ℕ → Bool) (E N : ℕ), K ≤ E → E ≤ N → a * (N : ℝ) ≤ E →
        (∀ k ≤ N, 0 < prescribedWalk events 1 k) →
        GoodCountWord lo hi c L K E N events →
        GoodProductWord ((1 + 1 / hi) / 2) ((1 + 1 / lo) / 2) c A B K N events := by
  classical
  choose A B hA hB hbound using fun w : ℝ ↦
    exists_global_normalizer_constants (w := max 1 w) (L := L) hlo hhi (le_max_left _ _) ha K hK
  refine ⟨A, B, fun w _ ↦ ⟨hA w, hB w⟩, ?_⟩
  intro events E N hKE hEN hscale hpos hgood
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro k hk
    exact hgood.2.1 k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
  · intro w hw k hk
    have hb := hbound w events E N hKE hEN hscale hpos
      (fun i hi ↦ (hgood.1 i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2).1)
      (fun i hi ↦ (hgood.1 i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2).2)
      hgood.2.2 k hk
    simpa only [max_eq_right hw] using hb.1
  · intro w hw k hk
    have hb := hbound w events E N hKE hEN hscale hpos
      (fun i hi ↦ (hgood.1 i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2).1)
      (fun i hi ↦ (hgood.1 i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2).2)
      hgood.2.2 k hk
    simpa only [max_eq_right hw] using hb.2

end HeightPaper.Model
