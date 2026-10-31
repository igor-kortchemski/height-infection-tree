module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Positivity

/-!
# Finite infection trees and the embedded SIR epidemic

Vertices are numbered in infection order, with patient zero numbered `0`.
Every attachment records its actual parent, rather than only its depth.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace HeightPaper.Model

/-- A rooted tree whose vertices carry their infection-order labels. -/
inductive Tree : ℕ → Type
  | root : Tree 1
  | attach {n : ℕ} (tree : Tree n) (parent : Fin n) : Tree (n + 1)

namespace Tree

/-- Distance from patient zero, calculated by following the attachment history. -/
def depth {n : ℕ} : Tree n → Fin n → ℕ
  | .root, _ => 0
  | @Tree.attach n t p, v =>
      if h : v.val < n then depth t ⟨v.val, h⟩ else depth t p + 1

/-- Parent label. The root is its own parent. -/
def parent {n : ℕ} : Tree n → Fin n → Fin n
  | .root, _ => 0
  | @Tree.attach n t p, v =>
      if h : v.val < n then (parent t ⟨v.val, h⟩).castSucc else p.castSucc

/-- The height is the maximum distance from the root over all vertices. -/
def height {n : ℕ} (t : Tree n) : ℕ := Finset.univ.sup (depth t)

 theorem size_pos {n : ℕ} (t : Tree n) : 0 < n := by
  cases t <;> omega

@[simp] theorem depth_root (v : Fin 1) : depth .root v = 0 := rfl

@[simp] theorem depth_attach_old {n : ℕ} (t : Tree n) (p v : Fin n) :
    depth (.attach t p) v.castSucc = depth t v := by
  simp [depth]

@[simp] theorem depth_attach_new {n : ℕ} (t : Tree n) (p : Fin n) :
    depth (.attach t p) (Fin.last n) = depth t p + 1 := by
  simp [depth]

 theorem depth_lt_size {n : ℕ} (t : Tree n) (v : Fin n) : depth t v < n := by
  induction t with
  | root => simp [depth]
  | @attach n t p ih =>
      simp only [depth]
      split_ifs with h
      · exact lt_trans (ih _) (Nat.lt_succ_self n)
      · have := ih p; omega

 theorem parent_lt {n : ℕ} (t : Tree n) (v : Fin n) (hv : v.val ≠ 0) :
    (parent t v).val < v.val := by
  induction t with
  | root => have := v.isLt; omega
  | @attach n t p ih =>
      simp only [parent]
      split_ifs with h
      · exact ih ⟨v.val, h⟩ hv
      · have := p.isLt; have := v.isLt; simp only [Fin.val_castSucc]; omega

 theorem depth_parent {n : ℕ} (t : Tree n) (v : Fin n) (hv : v.val ≠ 0) :
    depth t v = depth t (parent t v) + 1 := by
  induction t with
  | root => have := v.isLt; omega
  | @attach n t p ih =>
      by_cases h : v.val < n
      · simp only [depth, parent, h, dite_true, Fin.val_castSucc, (parent t ⟨v.val, h⟩).isLt]
        exact ih ⟨v.val, h⟩ hv
      · simp [depth, parent, h, p.isLt]

@[simp] theorem height_root : height .root = 0 := by simp [height, depth]

 theorem depth_le_height {n : ℕ} (t : Tree n) (v : Fin n) : depth t v ≤ height t :=
  Finset.le_sup (f := depth t) (Finset.mem_univ v)

 theorem height_lt_size {n : ℕ} (t : Tree n) : height t < n := by
  rw [height]
  exact Finset.sup_lt_iff (size_pos t) |>.mpr (fun v _ => depth_lt_size t v)

/-- The height update when an infection attaches a new vertex. -/
theorem height_attach {n : ℕ} (t : Tree n) (p : Fin n) :
    height (.attach t p) = max (height t) (depth t p + 1) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro v _
    by_cases hv : v.val < n
    · simp only [depth, hv, dite_eq_left]
      exact (depth_le_height t ⟨v.val, hv⟩).trans (le_max_left _ _)
    · simp only [depth, hv]
      exact le_max_right _ _
  · apply max_le
    · apply Finset.sup_le
      intro v _
      simpa using depth_le_height (.attach t p) v.castSucc
    · simpa using depth_le_height (.attach t p) (Fin.last n)

/-- Patient zero has depth zero. -/
theorem depth_zero {n : ℕ} (t : Tree n) : depth t ⟨0, size_pos t⟩ = 0 := by
  induction t with
  | root => rfl
  | attach t p ih => simpa [depth, size_pos t] using ih

/-- Every other vertex lies strictly above depth zero. -/
theorem depth_pos {n : ℕ} (t : Tree n) (v : Fin n) (hv : v.val ≠ 0) :
    0 < depth t v := by
  rw [depth_parent t v hv]
  exact Nat.succ_pos _

end Tree

/-- A state of the epidemic after an integer number of infection/recovery events. -/
structure State where
  vertices : ℕ
  tree : Tree vertices
  active : Finset (Fin vertices)
  susceptible : ℕ

/-- The number of infectious individuals. -/
def infectious (s : State) : ℕ := s.active.card

/-- The tree height, including both infectious and recovered individuals. -/
def height (s : State) : ℕ := s.tree.height

/-- Initially only patient zero is infected and `n` individuals are susceptible. -/
def initial (n : ℕ) : State where
  vertices := 1
  tree := .root
  active := {0}
  susceptible := n

/-- Recovery freezes one active vertex and leaves the tree intact. -/
def recover (s : State) (v : Fin s.vertices) : State :=
  { s with active := s.active.erase v }

/-- An infection attaches a new vertex to its infector. The transition kernel
only uses this operation when there is a susceptible individual. -/
def infect (s : State) (v : Fin s.vertices) : State where
  vertices := s.vertices + 1
  tree := .attach s.tree v
  active := insert (Fin.last s.vertices) (s.active.map Fin.castSuccEmb)
  susceptible := s.susceptible - 1

@[simp] theorem infectious_initial (n : ℕ) : infectious (initial n) = 1 := by
  simp [infectious, initial]

@[simp] theorem height_initial (n : ℕ) : height (initial n) = 0 := by
  simp [height, initial]

@[simp] theorem infectious_recover {s : State} {v : Fin s.vertices} (hv : v ∈ s.active) :
    infectious (recover s v) = infectious s - 1 := by
  exact Finset.card_erase_of_mem hv

@[simp] theorem infectious_infect (s : State) (v : Fin s.vertices) :
    infectious (infect s v) = infectious s + 1 := by
  have hnew : Fin.last s.vertices ∉ s.active.map Fin.castSuccEmb := by
    simp only [Finset.mem_map, not_exists, not_and]
    intro w _ hw
    have hval := congrArg Fin.val hw
    change w.val = s.vertices at hval
    have := w.isLt
    omega
  exact (Finset.card_insert_of_notMem hnew).trans (by simp [infectious])

@[simp] theorem height_recover (s : State) (v : Fin s.vertices) :
    height (recover s v) = height s := rfl

/-- Remaining infection/recovery potential. Each nonabsorbed transition reduces
it by one; its initial value is `2 * n + 1`. -/
def potential (s : State) : ℕ := 2 * s.susceptible + infectious s

@[simp] theorem potential_initial (n : ℕ) : potential (initial n) = 2 * n + 1 := by
  simp [potential, initial, infectious]

 theorem potential_recover {s : State} {v : Fin s.vertices} (hv : v ∈ s.active) :
    potential (recover s v) + 1 = potential s := by
  have hpos : 0 < infectious s := Finset.card_pos.mpr ⟨v, hv⟩
  simp only [potential, recover, infectious, Finset.card_erase_of_mem hv]
  simp only [infectious] at hpos
  omega

 theorem potential_infect {s : State} (v : Fin s.vertices) (h : 0 < s.susceptible) :
    potential (infect s v) + 1 = potential s := by
  change 2 * (s.susceptible - 1) + infectious (infect s v) + 1 =
    2 * s.susceptible + infectious s
  rw [infectious_infect]
  omega

noncomputable section

/-- Uniform selection among currently infectious vertices. -/
def uniformActive (s : State) (h : s.active.Nonempty) : PMF (Fin s.vertices) :=
  PMF.ofFinset (fun v => if v ∈ s.active then (s.active.card : ℝ≥0∞)⁻¹ else 0)
    s.active (by
      simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast h.card_pos.ne') (ENNReal.natCast_ne_top _))
    (by intro v hv; simp [hv])

@[simp] theorem uniformActive_apply (s : State) (h : s.active.Nonempty)
    (v : Fin s.vertices) :
    uniformActive s h v = if v ∈ s.active then (s.active.card : ℝ≥0∞)⁻¹ else 0 := rfl

 theorem mem_support_uniformActive {s : State} (h : s.active.Nonempty)
    (v : Fin s.vertices) : v ∈ (uniformActive s h).support ↔ v ∈ s.active := by
  simp [PMF.mem_support_iff, uniformActive_apply]

/-- Infection probability in the embedded event chain, equation (transitions). -/
def infectionProbability (rate : ℝ≥0) (susceptible : ℕ) : ℝ≥0 :=
  rate * susceptible / (1 + rate * susceptible)

 theorem infectionProbability_le_one (rate : ℝ≥0) (susceptible : ℕ) :
    infectionProbability rate susceptible ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ≥0) < 1 + rate * susceptible)).mpr
  simp

@[simp] theorem infectionProbability_zero (rate : ℝ≥0) :
    infectionProbability rate 0 = 0 := by simp [infectionProbability]

/-- `true` selects infection; `false` selects recovery. -/
def eventChoice (rate : ℝ≥0) (susceptible : ℕ) : PMF Bool :=
  PMF.ofFintype (fun b => cond b (infectionProbability rate susceptible : ℝ≥0∞)
    (1 - (infectionProbability rate susceptible : ℝ≥0∞)))
    ((Fintype.sum_bool _).trans
      (add_tsub_cancel_of_le
        (ENNReal.coe_le_coe.mpr (infectionProbability_le_one rate susceptible))))

@[simp] theorem eventChoice_true (rate : ℝ≥0) (susceptible : ℕ) :
    eventChoice rate susceptible true = (infectionProbability rate susceptible : ℝ≥0∞) := rfl

@[simp] theorem eventChoice_false (rate : ℝ≥0) (susceptible : ℕ) :
    eventChoice rate susceptible false = 1 - (infectionProbability rate susceptible : ℝ≥0∞) := rfl

/-- The recovery branch has exactly the probability in equation (transitions). -/
theorem eventChoice_false_eq (rate : ℝ≥0) (susceptible : ℕ) :
    eventChoice rate susceptible false =
      ((1 / (1 + rate * susceptible) : ℝ≥0) : ℝ≥0∞) := by
  have hden : (1 + rate * susceptible : ℝ≥0) ≠ 0 := by positivity
  have hsub : (1 : ℝ≥0) - infectionProbability rate susceptible =
      1 / (1 + rate * susceptible) := by
    change 1 - rate * susceptible / (1 + rate * susceptible) = _
    calc
      1 - rate * susceptible / (1 + rate * susceptible) =
          (1 + rate * susceptible) / (1 + rate * susceptible) -
            rate * susceptible / (1 + rate * susceptible) := by rw [div_self hden]
      _ = ((1 + rate * susceptible) - rate * susceptible) /
          (1 + rate * susceptible) := (tsub_div _ _ _).symm
      _ = 1 / (1 + rate * susceptible) := by rw [add_tsub_cancel_right]
  change ((1 : ℝ≥0) : ℝ≥0∞) - (infectionProbability rate susceptible : ℝ≥0∞) = _
  rw [← ENNReal.coe_sub, hsub]

/-- A single infection/recovery step. An epidemic with no infectious vertices
is absorbed. A nonexistent infection at zero susceptible count is explicitly
sent to recovery (its infection-choice probability is zero). -/
def step (rate : ℝ≥0) (s : State) : PMF State :=
  if h : s.active.Nonempty then
    (uniformActive s h).bind fun v =>
      (eventChoice rate s.susceptible).map fun infection =>
        if infection = true ∧ 0 < s.susceptible then infect s v else recover s v
  else PMF.pure s

/-- State law after the specified number of events. -/
def evolve (rate : ℝ≥0) (n : ℕ) : ℕ → PMF State
  | 0 => PMF.pure (initial n)
  | k + 1 => (evolve rate n k).bind (step rate)

/-- The law of the final tree height; the absorbing bound is `2 * n + 1`. -/
def heightLaw (rate : ℝ≥0) (n : ℕ) : PMF ℕ :=
  (evolve rate n (2 * n + 1)).map height

@[simp] theorem step_absorbed (rate : ℝ≥0) {s : State} (h : s.active = ∅) :
    step rate s = PMF.pure s := by
  simp [step, h]

/-- Every supported step is either an absorbing self-loop, recovery of an
infectious vertex, or infection from an infectious vertex while susceptibles
remain. -/
theorem step_support_cases {rate : ℝ≥0} {s t : State}
    (ht : t ∈ (step rate s).support) :
    (s.active = ∅ ∧ t = s) ∨
      ∃ v ∈ s.active, t = recover s v ∨ (0 < s.susceptible ∧ t = infect s v) := by
  by_cases h : s.active.Nonempty
  · rw [step, dite_eq_left h] at ht
    obtain ⟨v, hv, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
    have hv' := (mem_support_uniformActive h v).mp hv
    obtain ⟨b, _, hb⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
    refine Or.inr ⟨v, hv', ?_⟩
    split_ifs at hb with hbirth
    · exact Or.inr ⟨hbirth.2, hb.symm⟩
    · exact Or.inl hb.symm
  · rw [step, dite_eq_right h, PMF.mem_support_pure_iff] at ht
    exact Or.inl ⟨Finset.not_nonempty_iff_eq_empty.mp h, ht⟩

/-- Each supported finite path preserves the population size, counting all
previously infected vertices (infectious or recovered) and susceptible people. -/
theorem evolve_population {rate : ℝ≥0} {n k : ℕ} {t : State}
    (ht : t ∈ (evolve rate n k).support) : t.vertices + t.susceptible = n + 1 := by
  induction k generalizing t with
  | zero =>
      have heq : t = initial n := by simpa [evolve] using ht
      subst t
      simp [initial, Nat.add_comm]
  | succ k ih =>
      obtain ⟨s, hs, hstep⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
      have hpop := ih hs
      rcases step_support_cases hstep with ⟨_, rfl⟩ | ⟨v, _, hrec | ⟨hpos, hinf⟩⟩
      · exact hpop
      · simpa [hrec, recover] using hpop
      · rw [hinf]
        simp only [infect]
        omega

/-- Until absorption, the remaining event potential plus the elapsed event
count is at most the initial bound. -/
theorem evolve_potential_or_absorbed {rate : ℝ≥0} {n k : ℕ} {t : State}
    (ht : t ∈ (evolve rate n k).support) :
    potential t + k ≤ 2 * n + 1 ∨ t.active = ∅ := by
  induction k generalizing t with
  | zero =>
      have heq : t = initial n := by simpa [evolve] using ht
      subst t
      exact Or.inl (by simp)
  | succ k ih =>
      obtain ⟨s, hs, hstep⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
      rcases ih hs with hbound | habs
      · rcases step_support_cases hstep with ⟨hs0, rfl⟩ | ⟨v, hv, hrec | ⟨hpos, hinf⟩⟩
        · exact Or.inr hs0
        · have hd := potential_recover hv
          rw [hrec]
          exact Or.inl (by omega)
        · have hd := potential_infect v hpos
          rw [hinf]
          exact Or.inl (by omega)
      · rw [step_absorbed rate habs, PMF.mem_support_pure_iff] at hstep
        exact Or.inr (hstep ▸ habs)

/-- No epidemic on `n + 1` people can have more than `2 * n + 1`
infection/recovery events before absorption. -/
theorem evolve_absorbed {rate : ℝ≥0} {n k : ℕ} (hk : 2 * n + 1 ≤ k) {t : State}
    (ht : t ∈ (evolve rate n k).support) : t.active = ∅ := by
  rcases evolve_potential_or_absorbed ht with hb | ha
  · apply Finset.card_eq_zero.mp
    simp only [potential, infectious] at hb
    omega
  · exact ha

/-- The final-height law is supported on heights at most the initial number
of susceptible individuals. -/
theorem heightLaw_support_le {rate : ℝ≥0} {n h : ℕ}
    (hh : h ∈ (heightLaw rate n).support) : h ≤ n := by
  obtain ⟨s, hs, hheight⟩ := (PMF.mem_support_map_iff _ _ _).mp hh
  have hpop := evolve_population hs
  have hsize := Tree.height_lt_size s.tree
  change height s < s.vertices at hsize
  omega

/-- The state distribution stays fixed once the deterministic absorption bound
has elapsed. Thus the chosen finite time defines the full epidemic tree law. -/
theorem evolve_stable {rate : ℝ≥0} {n k : ℕ} (hk : 2 * n + 1 ≤ k) :
    evolve rate n (k + 1) = evolve rate n k := by
  change (evolve rate n k).bind (step rate) = evolve rate n k
  calc
    (evolve rate n k).bind (step rate) = (evolve rate n k).bind PMF.pure := by
      ext t
      simp only [PMF.bind_apply]
      apply tsum_congr
      intro s
      by_cases hs : s ∈ (evolve rate n k).support
      · rw [step_absorbed rate (evolve_absorbed hk hs)]
      · have hz : evolve rate n k s = 0 := by simpa [PMF.mem_support_iff] using hs
        simp [hz]
    _ = evolve rate n k := PMF.bind_pure _

/-- Taking extra event steps does not change the terminal law. -/
theorem evolve_terminal_add (rate : ℝ≥0) (n j : ℕ) :
    evolve rate n (2 * n + 1 + j) = evolve rate n (2 * n + 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Nat.add_succ, evolve_stable (by omega)]
      exact ih

/-- Susceptible and infectious counts, in the order used in the paper. -/
def counts (s : State) : ℕ × ℕ := (s.susceptible, infectious s)

private theorem bind_congr_on_support {α β : Type*} (p : PMF α)
    (f g : α → PMF β) (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa [PMF.mem_support_iff] using ha
    simp [hz]

/-- Marginalizing over the uniformly chosen active parent recovers exactly
 the susceptible/infectious transition in equation (transitions). -/
theorem step_counts (rate : ℝ≥0) (s : State) (h : s.active.Nonempty) :
    (step rate s).map counts =
      (eventChoice rate s.susceptible).map (fun b =>
        if b = true ∧ 0 < s.susceptible then
          (s.susceptible - 1, infectious s + 1)
        else (s.susceptible, infectious s - 1)) := by
  have hpoint (v : Fin s.vertices) (hv : v ∈ s.active) (b : Bool) :
      counts (if b = true ∧ 0 < s.susceptible then infect s v else recover s v) =
        if b = true ∧ 0 < s.susceptible then
          (s.susceptible - 1, infectious s + 1)
        else (s.susceptible, infectious s - 1) := by
    split_ifs
    · change (s.susceptible - 1, infectious (infect s v)) = _
      rw [infectious_infect]
    · change (s.susceptible, infectious (recover s v)) = _
      rw [infectious_recover hv]
  rw [step, dite_eq_left h, PMF.map_bind]
  calc
    (uniformActive s h).bind (fun v =>
        ((eventChoice rate s.susceptible).map (fun b =>
          if b = true ∧ 0 < s.susceptible then infect s v else recover s v)).map counts) =
      (uniformActive s h).bind (fun _ =>
        (eventChoice rate s.susceptible).map (fun b =>
          if b = true ∧ 0 < s.susceptible then
            (s.susceptible - 1, infectious s + 1)
          else (s.susceptible, infectious s - 1))) := by
      apply bind_congr_on_support
      intro v hv
      rw [PMF.map_comp]
      congr 1
      funext b
      exact hpoint v ((mem_support_uniformActive h v).mp hv) b
    _ = _ := PMF.bind_const _ _

end
end HeightPaper.Model
