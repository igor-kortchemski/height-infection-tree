module

public import HeightPaper.Probability.FiniteStrongProfileUniformCoupled
public import HeightPaper.Probability.StrongProfileTreeTransfer

/-! # The compact-parameter strengthening of the strong profile theorem -/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace HeightPaper

open CountCoupling

/-- The source's weak parameter-uniform strengthening following `thm:profil`.
The profile envelope and population threshold are chosen before both the
epidemic parameter and the exact lattice tilt. -/
theorem uniformStrongProfileTheorem : UniformStrongProfileStatement := by
  apply uniformStrongProfileStatement_of_coupled
  intro I hI T hT K hK hparams ε hε
  by_cases hIne : I.Nonempty
  swap
  · refine ⟨0, le_rfl, 0, ?_⟩
    intro n hn l hl
    exact False.elim (hIne ⟨l, hl⟩)
  by_cases hKne : K.Nonempty
  swap
  · refine ⟨0, le_rfl, 0, ?_⟩
    intro n hn l hl
    have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    simp [strongProfileStateBad, he, hε]
  exact finiteStrongProfile_uniform_coupled_tight hI hIne hT hK hKne
    hparams hε

end HeightPaper
