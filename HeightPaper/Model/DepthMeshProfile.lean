module

public import HeightPaper.Model.DepthMeshRoots

/-! # The finite depth mesh inherits every profile exponent from one Laplace input -/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology NNReal

noncomputable section

namespace HeightPaper.Model

def depthMeshCutoffs {J : ℕ} (l : ℝ) (x : Fin (J + 1) → ℝ) (n : ℕ) : Fin (J + 1) → ℝ :=
  fun i ↦ growthFactor l * Real.exp (x i) * Real.log n

def depthMeshExponent {J : ℕ} (l : ℝ) (x : Fin (J + 1) → ℝ) : DepthMeshBin J → ℝ
  | .low => 1
  | .middle i => profileExponent l (x i.castSucc)
  | .high => profileExponent l (x (Fin.last J))

theorem depthMeshExponent_pos {J : ℕ} {l : ℝ} (hl : 1 < l) (x : Fin (J + 1) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (0 : ℝ) (profileRoot l)) (b : DepthMeshBin J) :
    0 < depthMeshExponent l x b := by
  cases b with
  | low => exact zero_lt_one
  | middle i => exact profileExponent_pos hl (hx i.castSucc).1.le (hx i.castSucc).2
  | high => exact profileExponent_pos hl (hx (Fin.last J)).1.le (hx (Fin.last J)).2

/-- Low, finite middle, and infinite tail bins all satisfy the required
logarithmic root-count convergence from the same actual real-Laplace input. -/
theorem depthMeshRoots_profile_of_laplace
    (rates : ℕ → ℝ≥0) (horizon : ℕ → ℕ) {l T : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l))
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hhorizon : Tendsto (fun n ↦ (horizon n : ℝ) / n) atTop (𝓝 T))
    {J : ℕ} (x : Fin (J + 1) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (0 : ℝ) (profileRoot l))
    (hinc : ∀ i : Fin J, x i.castSucc < x i.succ)
    (hLap : ∀ t ∈ Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp t) s) / Real.log n -
          (1 + growthFactor l * (Real.exp t - 1))|}) atTop (𝓝 0)) :
    ∀ b : DepthMeshBin J, ∀ ε > (0 : ℝ), Tendsto
      (fun n ↦ (evolve (rates n) n (horizon n)).toMeasure.real {s | s.active.Nonempty ∧
        ε ≤ |Real.log (selectedRootCount s (depthMeshRoots (depthMeshCutoffs l x n) b s)) /
          Real.log n - depthMeshExponent l x b|}) atTop (𝓝 0) := by
  intro b ε hε
  cases b with
  | low =>
      simpa only [selectedRootCount_depthMeshRoots_low, depthMeshCutoffs, depthMeshExponent] using
        activeLowBinCount_log_convergence_of_laplace rates horizon hl hT (hx 0) hrates hhorizon hLap ε hε
  | middle i =>
      simpa only [selectedRootCount_depthMeshRoots_middle, depthMeshCutoffs, depthMeshExponent] using
        activeBinCount_log_convergence_of_laplace rates horizon hl (hx i.castSucc) (hinc i) hLap ε hε
  | high =>
      simpa only [selectedRootCount_depthMeshRoots_high, depthMeshCutoffs, depthMeshExponent] using
        activeTailCount_log_convergence_of_laplace rates horizon hl (hx (Fin.last J)) hLap ε hε

end HeightPaper.Model
