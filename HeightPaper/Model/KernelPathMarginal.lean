module

public import HeightPaper.Model.KernelPath
public import HeightPaper.Probability.KernelIteration

/-! # Coordinate marginals of finite kernel histories -/

@[expose] public section

namespace HeightPaper.Model

/-- The terminal coordinate has exactly the recursively evolved kernel law. -/
theorem kernelPathLaw_map_last (K : ℕ → State → PMF State) (s₀ : State) (N : ℕ) :
    (kernelPathLaw K s₀ N).map FinitePath.last =
      FinitePMF.kernelEvolve (PMF.pure s₀) K N := by
  induction N with
  | zero => rw [kernelPathLaw, PMF.pure_map]; rfl
  | succ N ih =>
      rw [kernelPathLaw, PMF.map_bind]
      simp_rw [PMF.map_comp]
      have hf (p : FinitePath N) : FinitePath.last ∘ p.append = id := by
        funext s
        simp
      simp_rw [hf, PMF.map_id]
      change (kernelPathLaw K s₀ N).bind (K N ∘ FinitePath.last) = _
      rw [← PMF.bind_map, ih]
      rfl

/-- Every coordinate has the corresponding evolved marginal law. -/
theorem kernelPathLaw_map_eval (K : ℕ → State → PMF State) (s₀ : State)
    (N k : ℕ) (hk : k ≤ N) :
    (kernelPathLaw K s₀ N).map (fun p ↦ p.eval k) =
      FinitePMF.kernelEvolve (PMF.pure s₀) K k := by
  rw [← kernelPathLaw_map_last K s₀ k, ← kernelPathLaw_map_prefixAt K s₀ N k hk,
    PMF.map_comp]
  rfl

/-- The fixed-horizon path measure pushes forward to the iterated state law. -/
theorem kernelPathMeasure_map_eval (K : ℕ → State → PMF State) (s₀ : State)
    (N k : ℕ) (hk : k ≤ N) :
    (kernelPathMeasure K s₀ N).map (fun p ↦ p.eval k) =
      (FinitePMF.kernelEvolve (PMF.pure s₀) K k).toMeasure := by
  rw [kernelPathMeasure, PMF.toMeasure_map _ _ (FinitePath.measurable _),
    kernelPathLaw_map_eval K s₀ N k hk]

end HeightPaper.Model
