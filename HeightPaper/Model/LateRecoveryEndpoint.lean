module

public import HeightPaper.Model.SourceCutoffState
public import HeightPaper.Probability.LatePressure
public import HeightPaper.Model.HeightPotentialBounds

/-!
# The late recovery event depends only on cutoff and terminal states

The susceptible count decreases, so recovery probability increases.  The
paper's all-late-times event can therefore be read from its two endpoints.
-/

@[expose] public section

open scoped NNReal

namespace HeightPaper.Model

def lateRecoveryEndpoints (rate : ℝ≥0) (l η : ℝ) (s t : State) : Prop :=
  1 / (1 + offspringMean l + η) ≤
      1 - (infectionProbability rate s.susceptible : ℝ) ∧
    1 - (infectionProbability rate t.susceptible : ℝ) ≤
      1 / (1 + offspringMean l - η)

/-- The manuscript's unrestricted positive-η statement cannot hold: when
η exceeds the upper denominator, its demanded upper bound is negative while
every recovery probability is nonnegative. -/
theorem not_lateRecoveryEndpoints_of_large_eta
    (rate : ℝ≥0) (l η : ℝ) (s t : State)
    (hη : 1 + offspringMean l < η) :
    ¬ lateRecoveryEndpoints rate l η s t := by
  intro h
  have hden : 1 + offspringMean l - η < 0 := by linarith
  have hneg : 1 / (1 + offspringMean l - η) < 0 :=
    div_neg_of_pos_of_neg (by norm_num) hden
  have hprob : (infectionProbability rate t.susceptible : ℝ) ≤ 1 := by
    exact_mod_cast infectionProbability_le_one rate t.susceptible
  dsimp [lateRecoveryEndpoints] at h
  linarith [h.2]

/-- The event controlling every late recovery probability is exactly a
two-state event on supported epidemic paths. -/
theorem lateRecoveryEvent_iff_endpoints
    {rate : ℝ≥0} {n : ℕ} {l δ η : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    {p : FinitePath (2 * n + 1)}
    (hp : SupportedPath rate n (2 * n + 1) p.eval) :
    p ∈ lateRecoveryEvent rate l δ η n ↔
      lateRecoveryEndpoints rate l η (p.eval (sourceCutoff l δ n)) p.last := by
  let H := sourceCutoff l δ n
  let N := 2 * n + 1
  have hHN : H ≤ N := sourceCutoff_le_steps hl hδ n
  constructor
  · intro h
    have hH := h H le_rfl hHN
    have hN := h N hHN le_rfl
    change _ ∧ _
    rw [recoveryProbability_real, recoveryProbability_real]
    simpa only [N, FinitePath.eval_last] using And.intro hH.1 hN.2
  · rintro ⟨hstart, hfinal⟩
    intro k hHk hkN
    have hSkH : (p.eval k).susceptible ≤ (p.eval H).susceptible :=
      hp.susceptible_antitone hHk hkN
    have hSNk : p.last.susceptible ≤ (p.eval k).susceptible := by
      simpa only [N, FinitePath.eval_last] using
        hp.susceptible_antitone hkN le_rfl
    have hleft := recoveryProbability_antitone rate hSkH
    have hright := recoveryProbability_antitone rate hSNk
    change _ ∧ _
    rw [← recoveryProbability_real]
    exact ⟨hstart.trans hleft, hright.trans hfinal⟩

/-- For large η the source event is impossible on every supported path. -/
theorem not_lateRecoveryEvent_of_large_eta
    {rate : ℝ≥0} {n : ℕ} {l δ η : ℝ} (hl : 1 < l)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hη : 1 + offspringMean l < η)
    {p : FinitePath (2 * n + 1)}
    (hp : SupportedPath rate n (2 * n + 1) p.eval) :
    p ∉ lateRecoveryEvent rate l δ η n := by
  rw [lateRecoveryEvent_iff_endpoints hl hδ hp]
  exact not_lateRecoveryEndpoints_of_large_eta rate l η _ _ hη

end HeightPaper.Model
