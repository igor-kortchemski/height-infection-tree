module

public import HeightPaper.Model.Cutoff
public import HeightPaper.Model.PathMeasure

/-!
# The source survival event is determined by the cutoff tree

At the cutoff, an active state has event count equal to the cutoff, while an
already extinct state is absorbed.  This proves the measurability assertion
made just before `lem:dangling` in the manuscript.
-/

@[expose] public section

open scoped NNReal

namespace HeightPaper.Model

/-- Every active state in the genuine cutoff law satisfies the non-strict
source survival predicate. -/
theorem evolve_active_mem_sourceSurvivalEvent
    (rate : ℝ≥0) (n : ℕ) (l δ : ℝ) {s : State}
    (hs : s ∈ (evolve rate n (sourceCutoff l δ n)).support)
    (ha : s.active.Nonempty) :
    s ∈ sourceSurvivalEvent l δ n := by
  have hcount := evolve_eventCount_eq_of_active hs ha
  change sourceCutoff l δ n ≤ 2 * s.vertices - 1
  dsimp [eventCount, infectious] at hcount
  omega

/-- The source terminal survival event is exactly the same state predicate
evaluated on the cutoff tree, on every supported complete epidemic path. -/
theorem sourceSurvivalEvent_iff_cutoffState
    {rate : ℝ≥0} {n : ℕ} {l δ : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    {p : FinitePath (2 * n + 1)}
    (hp : SupportedPath rate n (2 * n + 1) p.eval) :
    p.last ∈ sourceSurvivalEvent l δ n ↔
      p.eval (sourceCutoff l δ n) ∈ sourceSurvivalEvent l δ n := by
  let H := sourceCutoff l δ n
  let N := 2 * n + 1
  let τ := 2 * p.last.vertices - 1
  let τ' := 2 * (p.eval (2 * n + 1)).vertices - 1
  have hHN : H ≤ N := sourceCutoff_le_steps hl hδ n
  have hfirst' : 0 < τ' ∧ τ' ≤ N ∧ (p.eval τ').active = ∅ ∧
      ∀ k < τ', (p.eval k).active.Nonempty := by
    simpa only [τ', N] using hp.first_extinction le_rfl
  have hτ' : τ' = τ := by simp [τ', τ, FinitePath.eval_last]
  have hfirst : 0 < τ ∧ τ ≤ N ∧ (p.eval τ).active = ∅ ∧
      ∀ k < τ, (p.eval k).active.Nonempty := by
    rcases hfirst' with ⟨hpos, hle, hab, hbefore⟩
    refine ⟨by simpa only [hτ'] using hpos,
      by simpa only [hτ'] using hle, ?_, ?_⟩
    · change (p.eval (2 * (p.eval (2 * n + 1)).vertices - 1)).active = ∅ at hab
      rw [FinitePath.eval_last] at hab
      exact hab
    · intro k hk
      exact hbefore k (by simpa only [hτ'] using hk)
  have hlast : p.eval τ = p.last := by
    have h := hp.absorbed_stable hfirst.2.1 le_rfl hfirst.2.2.1
    simpa only [N, FinitePath.eval_last] using h.symm
  constructor
  · intro hterminal
    have hτH : H ≤ τ := hterminal
    by_cases heq : H = τ
    · change H ≤ 2 * (p.eval H).vertices - 1
      rw [heq, hlast]
    · have hHτ : H < τ := lt_of_le_of_ne hτH heq
      have ha : (p.eval H).active.Nonempty := hfirst.2.2.2 H hHτ
      have hevent := evolve_eventCount_eq_of_active (hp.mem_evolve hHN) ha
      change H ≤ 2 * (p.eval H).vertices - 1
      dsimp [eventCount] at hevent
      omega
  · intro hcut
    change H ≤ τ
    by_contra hnot
    have hτH : τ < H := Nat.lt_of_not_ge hnot
    have hsame := hp.absorbed_stable hτH.le hHN hfirst.2.2.1
    have heq : p.eval H = p.last := hsame.trans hlast
    change H ≤ 2 * (p.eval H).vertices - 1 at hcut
    rw [heq] at hcut
    omega

end HeightPaper.Model
