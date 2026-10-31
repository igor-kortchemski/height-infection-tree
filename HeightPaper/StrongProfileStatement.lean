module

public import HeightPaper.Model.ProfileFourier
public import HeightPaper.Model.Cutoff
public import HeightPaper.Model.PathMeasure

/-!
# The exact strong-profile target

These definitions state the remaining `thm:profil` obligation. They do not
assert that it has been proved. Zero profile mass is explicitly a bad event,
so the totalized real logarithm cannot hide the source's value minus infinity.
The lattice condition is an equality, with no rounding of the height.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper

open Model

noncomputable def strongProfileLogScale (l : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (profileExponent l x - 1) * Real.log n - (1 / 2 : ℝ) * Real.log (Real.log n)

def strongProfileStateBad (l : ℝ) (K : Set ℝ) (n : ℕ) (R : ℝ) : Set State :=
  {s | ∃ x ∈ K, ∃ k : ℕ, (k : ℝ) = growthFactor l * Real.exp x * Real.log n ∧
    (normalizedActiveProfile s k = 0 ∨
      R < |Real.log (normalizedActiveProfile s k) - strongProfileLogScale l n x|)}

/-- The paper's exact non-strict survival event, observed on the full finite
epidemic history, together with a zero mass or an excessive local log error. -/
def strongProfileBad (l T : ℝ) (K : Set ℝ) (n : ℕ) (R : ℝ) :
    Set (FinitePath (2 * n + 1)) :=
  {q | ⌊T * n⌋₊ ≤ 2 * (q.eval (2 * n + 1)).vertices - 1 ∧
    q.eval ⌊T * n⌋₊ ∈ strongProfileStateBad l K n R}

theorem measurableSet_strongProfileBad (l T : ℝ) (K : Set ℝ) (n : ℕ) (R : ℝ) :
    MeasurableSet (strongProfileBad l T K n R) := trivial

/-- The fixed-parameter source theorem, including uniformity over the compact
set of admissible lattice tilts and the full `-(1/2) log log n` correction. -/
def StrongProfileStatement : Prop :=
  ∀ l : ℝ≥0, 1 < (l : ℝ) → ∀ T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l),
    ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (0 : ℝ) (profileRoot l) →
      ∀ ε > (0 : ℝ), ∃ R ≥ (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
        (pathMeasure (l / n) n (2 * n + 1)).real (strongProfileBad l T K n R) < ε

/-- The additional weak parameter uniformity stated immediately after
`thm:profil`. All constants precede the individual parameter and population. -/
def UniformStrongProfileStatement : Prop :=
  ∀ I : Set ℝ≥0, IsCompact I → ∀ T > (0 : ℝ), ∀ K : Set ℝ, IsCompact K →
    (∀ l ∈ I, 1 < (l : ℝ) ∧ T < fluidExtinctionTime l ∧
      K ⊆ Ioo (0 : ℝ) (profileRoot l)) →
      ∀ ε > (0 : ℝ), ∃ R ≥ (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ l ∈ I,
        (pathMeasure (l / n) n (2 * n + 1)).real (strongProfileBad l T K n R) < ε

theorem strongProfileStatement_of_uniform
    (h : UniformStrongProfileStatement) : StrongProfileStatement := by
  intro l hl T hT K hK hKsub ε hε
  obtain ⟨R, hR, N, hN⟩ := h {l} isCompact_singleton T hT.1 K hK
    (by intro a ha; simpa only [mem_singleton_iff.mp ha] using And.intro hl ⟨hT.2, hKsub⟩)
    ε hε
  exact ⟨R, hR, N, fun n hn ↦ hN n hn l (mem_singleton l)⟩

/-- The finite log-error formulation is exactly a positive multiplicative
envelope; this identifies the treatment of zero masses in the source target. -/
theorem positive_log_error_iff_exp_envelope (q c R : ℝ) :
    (0 < q ∧ |Real.log q - c| ≤ R) ↔
      Real.exp (c - R) ≤ q ∧ q ≤ Real.exp (c + R) := by
  constructor
  · rintro ⟨hq, hb⟩
    obtain ⟨hlo, hhi⟩ := abs_le.mp hb
    constructor
    · calc
        Real.exp (c - R) ≤ Real.exp (Real.log q) := Real.exp_le_exp.mpr (by linarith)
        _ = q := Real.exp_log hq
    · calc
        q = Real.exp (Real.log q) := (Real.exp_log hq).symm
        _ ≤ Real.exp (c + R) := Real.exp_le_exp.mpr (by linarith)
  · rintro ⟨hlo, hhi⟩
    have hq : 0 < q := (Real.exp_pos _).trans_le hlo
    refine ⟨hq, abs_le.mpr ⟨?_, ?_⟩⟩
    · have h := Real.log_le_log (Real.exp_pos _) hlo
      rw [Real.log_exp] at h
      linarith
    · have h := Real.log_le_log hq hhi
      rw [Real.log_exp] at h
      linarith

end HeightPaper
