module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
meta import all Lean.Meta.Match.Match
public meta import Lean.Elab.Command

/-!
# Height and active profile of the infection tree

Statement interface for `thm:main` and `thm:profil` of *The height of the
infection tree* by Emmanuel Kammerer, Igor Kortchemski and Delphin Sénizergues.
The third compared declaration is the parameter-uniform strengthening stated
immediately after `thm:profil`.

This Challenge has three deliberate theorem proof holes, confined to its last
three declarations. `Solution` supplies the existing proved declarations with
exactly the same names. No implementation module imports this Challenge.
All mathematical definitions below are concrete and have no holes.

The model is the embedded SIR event chain: one initial infectious root, `n`
susceptibles, uniform active-parent choice, and infection probability
`rate * susceptible / (1 + rate * susceptible)`. The finite time `2*n+1`
is an absorbing bound; recovered vertices remain in the tree. The external
continuous-time Poisson/exponential representation is not constructed here.

The height limit retains arbitrary nonnegative rates asymptotic to lambda/n
and the full Bernoulli mixture. The profile statement uses exact lattice
heights, the minus one-half log-log correction, zero mass as failure, and
non-strict survival at the observation horizon. Its uniform version places
all thresholds before the individual rate and lattice tilt.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology Asymptotics

namespace HeightPaper.Model
/-- Rooted infection-order tree; an attachment records its parent. -/

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

noncomputable section
/-- Uniform selection among currently infectious vertices. -/
def uniformActive (s : State) (h : s.active.Nonempty) : PMF (Fin s.vertices) :=
  PMF.ofFinset (fun v => if v ∈ s.active then (s.active.card : ℝ≥0∞)⁻¹ else 0)
    s.active (by
      simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast h.card_pos.ne') (ENNReal.natCast_ne_top _))
    (by intro v hv; simp [hv])
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

end
end HeightPaper.Model

/- Reproduce PathMeasure's fresh, nonserialized compiler caches. -/
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}

namespace HeightPaper.Model
/-- A history of the initial state and a specified number of event steps. -/
structure FinitePath (steps : ℕ) where
  state : Fin (steps + 1) → State
namespace FinitePath
instance (steps : ℕ) : MeasurableSpace (FinitePath steps) := ⊤
instance (steps : ℕ) : MeasurableSingletonClass (FinitePath steps) where
  measurableSet_singleton _ := trivial
/-- Evaluate beyond the recorded horizon by keeping the terminal state fixed. -/
def eval {steps : ℕ} (p : FinitePath steps) (k : ℕ) : State :=
  p.state ⟨min k steps, Nat.lt_succ_of_le (Nat.min_le_right k steps)⟩

def last {steps : ℕ} (p : FinitePath steps) : State := p.state (Fin.last steps)

def append {steps : ℕ} (p : FinitePath steps) (s : State) : FinitePath (steps + 1) :=
  ⟨Fin.lastCases s p.state⟩

end FinitePath
/-- Joint law of the finite epidemic history. -/
noncomputable def pathLaw (rate : ℝ≥0) (n : ℕ) : (steps : ℕ) → PMF (FinitePath steps)
  | 0 => PMF.pure ⟨fun _ ↦ initial n⟩
  | steps + 1 => (pathLaw rate n steps).bind fun p ↦ (step rate p.last).map p.append

/-- Probability measure on all the states of the finite history. -/
noncomputable def pathMeasure (rate : ℝ≥0) (n steps : ℕ) : Measure (FinitePath steps) :=
  (pathLaw rate n steps).toMeasure

/-- Number of currently infectious vertices at a specified height. -/
def activeProfile (s : State) (h : ℕ) : ℕ :=
  (s.active.filter fun v => s.tree.depth v = h).card

/-- The normalized active profile, with value zero when the active count is zero. -/
noncomputable def normalizedActiveProfile (s : State) (k : ℕ) : ℝ :=
  (activeProfile s k : ℝ) / (infectious s : ℝ)

end HeightPaper.Model

noncomputable section
namespace HeightPaper
/-- The logarithmic height scale factor gamma. -/
def growthFactor (l : ℝ) : ℝ := l / (l - 1)
/-- The source profile exponent f_lambda. -/
def profileExponent (l z : ℝ) : ℝ :=
  1 + growthFactor l * (Real.exp z - 1 - z * Real.exp z)
/-- Positive root z_lambda, defined by the paper's infimum. -/
def profileRoot (l : ℝ) : ℝ := sInf {z : ℝ | 0 < z ∧ profileExponent l z = 0}
/-- The function x exp(-x) defining the Lambert inverse relation. -/
def meanEquation (x : ℝ) : ℝ := x * Real.exp (-x)
/-- The subcritical principal-branch root m_lambda, selected in (0,1). -/
def offspringMean (l : ℝ) : ℝ :=
  sInf {m : ℝ | m ∈ Ioo (0 : ℝ) 1 ∧ meanEquation m = meanEquation l}
/-- Minus the logarithm of the subcritical offspring mean. -/
def outgrowthRate (l : ℝ) : ℝ := -Real.log (offspringMean l)
/-- The critical rate, defined by the source crossing equation. -/
def criticalParameter : ℝ :=
  sInf {l : ℝ | 1 < l ∧ offspringMean l = Real.exp (-profileRoot l)}

/-- The piecewise constant in the statement of `thm:main`. Both branches agree
at `criticalParameter`, as shown by the variational characterization. -/
def mainCoefficient (l : ℝ) : ℝ :=
  if l ≤ criticalParameter then
    l / ((l - 1) * offspringMean l) +
      profileExponent l (outgrowthRate l) / outgrowthRate l
  else growthFactor l * Real.exp (profileRoot l)

/-- The final susceptible fraction `m_l / l`. -/
def finalSusceptibleFraction (l : ℝ) : ℝ := offspringMean l / l

/-- The positive extinction time of the deterministic fluid curve. -/
def fluidExtinctionTime (l : ℝ) : ℝ := 2 - 2 * finalSusceptibleFraction l

/-- The survival parameter `1 - 1/l`, valid for the supercritical regime. -/
noncomputable def survivalParameter (l : ℝ) (hl : 1 < l) : unitInterval :=
  ⟨1 - 1 / l, by
    have hlpos : 0 < l := lt_trans zero_lt_one hl
    constructor
    · have : 1 / l < 1 := (div_lt_one hlpos).mpr hl
      linarith
    · have : 0 ≤ 1 / l := div_nonneg zero_le_one hlpos.le
      linarith⟩

/-- The limiting law with mass `1/l` at zero and mass `1 - 1/l` at `κ`. -/
noncomputable def heightLimitLaw (l : ℝ) (hl : 1 < l) (κ : ℝ) : ProbabilityMeasure ℝ :=
  ⟨bernoulliMeasure κ 0 (survivalParameter l hl), inferInstance⟩

/-- The actual terminal infection-tree height, normalized as in `thm:main`.
The values at `n = 0` and `n = 1` use Lean's total real division and are irrelevant
to the limit at infinity. -/
noncomputable def normalizedHeightLaw (rate : ℝ≥0) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨(Model.heightLaw rate n).toMeasure.map (fun h : ℕ ↦ (h : ℝ) / Real.log n), inferInstance⟩

/-- The source main theorem, retaining every asymptotically scaled rate sequence
and the full Bernoulli mixture. Its proof is `HeightPaper.mainTheorem`
in the downstream `MainTheorem` module. -/
def MainTheoremStatement : Prop :=
  ∀ (l : ℝ) (hl : 1 < l) (rates : ℕ → ℝ≥0),
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (rates n : ℝ)) atTop (𝓝 l) →
    Tendsto (fun n ↦ normalizedHeightLaw (rates n) n) atTop
      (𝓝 (heightLimitLaw l hl (mainCoefficient l)))

/- Reproduce the original StrongProfileStatement module boundary. The auxiliary
proof cache is not serialized across imports; clearing it preserves the names
of generated numeral proofs in the copied definitions, without changing them. -/
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

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

/-- The full terminal-height distribution limit, source `thm:main`. -/
theorem mainTheorem : MainTheoremStatement := by sorry

/-- Exact lattice strong-profile asymptotics, source `thm:profil`. -/
theorem strongProfileTheorem : StrongProfileStatement := by sorry

/-- The parameter-uniform strengthening immediately following `thm:profil`. -/
theorem uniformStrongProfileTheorem : UniformStrongProfileStatement := by sorry

end HeightPaper
