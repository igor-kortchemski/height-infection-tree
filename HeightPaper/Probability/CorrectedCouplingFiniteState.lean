module

public import HeightPaper.Probability.CorrectedCouplingConstruction

/-!
# Countable codes for the actual finite coupled states

Only genealogies whose parent map is zero off their finite vertex set are
encoded. The unrestricted type of parent functions is not countable.
The coded recursion decodes exactly to `correctedCouplingStage`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

def CouplingGenealogy.Normalized (s : CouplingGenealogy) : Prop :=
  ∀ x, x ∉ s.carrier.vertices → s.parent x = 0

theorem CouplingGenealogy.normalized_initial (roots : Finset ℕ) :
    (CouplingGenealogy.initial roots).Normalized := by
  intro x _
  rfl

theorem CouplingGenealogy.normalized_update
    {s : CouplingGenealogy} (hs : s.Normalized)
    (v fresh : ℕ) (birth : Bool) : (s.update v fresh birth).Normalized := by
  by_cases hv : v ∈ s.carrier.active
  · cases birth
    · simpa [CouplingGenealogy.Normalized, CouplingGenealogy.update,
        CouplingCarrier.update, hv] using hs
    · intro x hx
      have hx' : x ∉ insert fresh s.carrier.vertices := by
        simpa [CouplingGenealogy.update, CouplingCarrier.update, hv] using hx
      have hxf : x ≠ fresh := fun h ↦ hx' (h ▸ Finset.mem_insert_self _ _)
      have hxs : x ∉ s.carrier.vertices :=
        fun h ↦ hx' (Finset.mem_insert_of_mem h)
      simpa [CouplingGenealogy.update, hv, Function.update_of_ne hxf] using hs x hxs
  · simpa [CouplingGenealogy.Normalized, CouplingGenealogy.update,
      CouplingCarrier.update, hv] using hs

abbrev FiniteCouplingGenealogy := {s : CouplingGenealogy // s.Normalized}

theorem CouplingGenealogy.ext_carrier_parent
    {a b : CouplingGenealogy} (hc : a.carrier = b.carrier)
    (hp : a.parent = b.parent) : a = b := by
  cases a
  cases b
  cases hc
  cases hp
  rfl

instance : Countable FiniteCouplingGenealogy := by
  let code (s : FiniteCouplingGenealogy) : CouplingCarrier × Finset (ℕ × ℕ) :=
    (s.1.carrier, s.1.carrier.vertices.image (fun x ↦ (x, s.1.parent x)))
  have hinj : Function.Injective code := by
    intro a b h
    have hc : a.1.carrier = b.1.carrier := congrArg Prod.fst h
    have hg : a.1.carrier.vertices.image (fun x ↦ (x, a.1.parent x)) =
        b.1.carrier.vertices.image (fun x ↦ (x, b.1.parent x)) := congrArg Prod.snd h
    have hp : a.1.parent = b.1.parent := by
      funext x
      by_cases hx : x ∈ a.1.carrier.vertices
      · have hm : (x, a.1.parent x) ∈
            b.1.carrier.vertices.image (fun y ↦ (y, b.1.parent y)) := by
          rw [← hg]
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
        obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hm
        have hyx : y = x := congrArg Prod.fst hy
        simpa [hyx] using (congrArg Prod.snd hy).symm
      · have hx' : x ∉ b.1.carrier.vertices := by simpa [← hc] using hx
        rw [a.2 x hx, b.2 x hx']
    exact Subtype.ext (CouplingGenealogy.ext_carrier_parent hc hp)
  exact hinj.countable

instance : MeasurableSpace FiniteCouplingGenealogy := ⊤

def FiniteCouplingGenealogy.initial (roots : Finset ℕ) : FiniteCouplingGenealogy :=
  ⟨CouplingGenealogy.initial roots, CouplingGenealogy.normalized_initial roots⟩

def FiniteCouplingGenealogy.update (s : FiniteCouplingGenealogy)
    (v fresh : ℕ) (birth : Bool) : FiniteCouplingGenealogy :=
  ⟨s.1.update v fresh birth, s.1.normalized_update s.2 v fresh birth⟩

structure FiniteCouplingState where
  lower : FiniteCouplingGenealogy
  middle : FiniteCouplingGenealogy
  upper : FiniteCouplingGenealogy
  word : List Bool
  faithful : Bool

instance : Countable FiniteCouplingState := by
  have hinj : Function.Injective (fun s : FiniteCouplingState ↦
      ((s.lower, s.middle, s.upper), s.word, s.faithful)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨⟨hl, hm, hu⟩, hw, hf⟩
    cases a
    cases b
    cases hl
    cases hm
    cases hu
    cases hw
    cases hf
    rfl
  exact hinj.countable

instance : MeasurableSpace FiniteCouplingState := ⊤

def FiniteCouplingState.toState (s : FiniteCouplingState) : CorrectedCouplingState :=
  { trees := ⟨s.lower.1, s.middle.1, s.upper.1⟩
    word := s.word
    faithful := s.faithful }

def FiniteCouplingState.initial (roots : Finset ℕ) : FiniteCouplingState :=
  { lower := FiniteCouplingGenealogy.initial roots
    middle := FiniteCouplingGenealogy.initial roots
    upper := FiniteCouplingGenealogy.initial roots
    word := []
    faithful := true }

/-- The five countable choices through which a physical update factors. -/
abbrev CouplingChoiceCode := (ℕ × ℕ) × (Bool × Bool × Bool)

noncomputable def CouplingGenealogy.totalSelected (s : CouplingGenealogy)
    (u : ℝ) : ℕ :=
  if h : s.carrier.active.Nonempty then s.selectedActive h u else 0

theorem CouplingGenealogy.measurable_totalSelected (s : CouplingGenealogy) :
    Measurable s.totalSelected := by
  change Measurable (fun u : ℝ ↦
    if h : s.carrier.active.Nonempty then s.selectedActive h u else 0)
  by_cases h : s.carrier.active.Nonempty
  · simpa [CouplingGenealogy.totalSelected, h] using s.measurable_selectedActive h
  · simp [h]

noncomputable def FiniteCouplingState.choices
    (s : FiniteCouplingState) (p q : ℝ) (r : List Bool → ℝ)
    (u recovery : ℝ) : CouplingChoiceCode :=
  ((s.upper.1.totalSelected u, s.middle.1.totalSelected u),
    recoveryThresholdBirth q recovery,
    recoveryThresholdBirth (r s.word) recovery,
    recoveryThresholdBirth p recovery)

noncomputable def FiniteCouplingState.discreteStep
    (s : FiniteCouplingState) (p q : ℝ) (r : List Bool → ℝ)
    (d : CouplingChoiceCode) : FiniteCouplingState :=
  if s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q then
    if s.upper.1.carrier.active.Nonempty then
      { lower := s.lower.update d.1.1 s.upper.1.fresh d.2.1
        middle := s.middle.update d.1.1 s.upper.1.fresh d.2.2.1
        upper := s.upper.update d.1.1 s.upper.1.fresh d.2.2.2
        word := if d.1.1 ∈ s.middle.1.carrier.active then
            s.word ++ [d.2.2.1] else s.word
        faithful := true }
    else { s with word := s.word ++ [d.2.2.1], faithful := true }
  else
    { lower := s.lower.update d.1.1 s.upper.1.fresh d.2.1
      middle := s.middle.update d.1.2 s.middle.1.fresh d.2.2.1
      upper := s.upper.update d.1.1 s.upper.1.fresh d.2.2.2
      word := s.word ++ [d.2.2.1]
      faithful := false }

noncomputable def FiniteCouplingState.step
    (s : FiniteCouplingState) (p q : ℝ) (r : List Bool → ℝ)
    (u recovery : ℝ) : FiniteCouplingState :=
  s.discreteStep p q r (s.choices p q r u recovery)

theorem FiniteCouplingState.toState_step
    (s : FiniteCouplingState) (p q : ℝ) (r : List Bool → ℝ)
    (u recovery : ℝ) :
    (s.step p q r u recovery).toState = s.toState.step p q r u recovery := by
  by_cases hg : s.faithful = true ∧ p ≤ r s.word ∧ r s.word ≤ q
  · by_cases hu : s.upper.1.carrier.active.Nonempty
    · simp [FiniteCouplingState.step, FiniteCouplingState.discreteStep,
        FiniteCouplingState.choices, FiniteCouplingState.toState,
        CorrectedCouplingState.step, hg, hu, CouplingGenealogy.totalSelected,
        FiniteCouplingGenealogy.update, CouplingTriple.step]
    · simp [FiniteCouplingState.step, FiniteCouplingState.discreteStep,
        FiniteCouplingState.choices, FiniteCouplingState.toState,
        CorrectedCouplingState.step, hg, hu]
  · simp [FiniteCouplingState.step, FiniteCouplingState.discreteStep,
      FiniteCouplingState.choices, FiniteCouplingState.toState,
      CorrectedCouplingState.step, hg, CouplingGenealogy.totalSelected,
      FiniteCouplingGenealogy.update]
    exact ⟨rfl, rfl, rfl⟩

theorem FiniteCouplingState.measurable_step
    (s : FiniteCouplingState) (p q : ℝ) (r : List Bool → ℝ) :
    Measurable (fun z : ℝ × ℝ ↦ s.step p q r z.1 z.2) := by
  have hU := s.upper.1.measurable_totalSelected.comp
    (measurable_fst : Measurable (Prod.fst : ℝ × ℝ → ℝ))
  have hM := s.middle.1.measurable_totalSelected.comp
    (measurable_fst : Measurable (Prod.fst : ℝ × ℝ → ℝ))
  have hq := (measurable_recoveryThresholdBirth q).comp
    (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ))
  have hr := (measurable_recoveryThresholdBirth (r s.word)).comp
    (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ))
  have hp := (measurable_recoveryThresholdBirth p).comp
    (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ))
  exact (measurable_of_countable (s.discreteStep p q r)).comp
    ((hU.prodMk hM).prodMk (hq.prodMk (hr.prodMk hp)))

noncomputable def finiteCouplingStage (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) : ℕ → FiniteCouplingState
  | 0 => FiniteCouplingState.initial roots
  | k + 1 => (finiteCouplingStage roots p q r w k).step p q r (w (0, k)) (w (1, k))

theorem finiteCouplingStage_toState (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (w : (Fin 2 × ℕ) → ℝ) (k : ℕ) :
    (finiteCouplingStage roots p q r w k).toState =
      correctedCouplingStage roots p q r w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [finiteCouplingStage, FiniteCouplingState.toState_step, ih]
      rfl

theorem measurable_finiteCouplingStage (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (k : ℕ) :
    Measurable (fun w : (Fin 2 × ℕ) → ℝ ↦ finiteCouplingStage roots p q r w k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      have hs : Measurable (fun z : FiniteCouplingState × (ℝ × ℝ) ↦
          z.1.step p q r z.2.1 z.2.2) :=
        measurable_from_prod_countable_right
          (fun s ↦ s.measurable_step p q r)
      exact hs.comp (ih.prodMk
        ((measurable_pi_apply (0, k)).prodMk (measurable_pi_apply (1, k))))

theorem finiteCouplingStage_congr_prefix (roots : Finset ℕ) (p q : ℝ)
    (r : List Bool → ℝ) (k : ℕ) {w z : (Fin 2 × ℕ) → ℝ}
    (h : ∀ i, i.2 < k → w i = z i) :
    finiteCouplingStage roots p q r w k = finiteCouplingStage roots p q r z k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [finiteCouplingStage, finiteCouplingStage,
        ih (fun i hi ↦ h i (by omega)), h (0, k) (by simp), h (1, k) (by simp)]

end HeightPaper.CountCoupling
