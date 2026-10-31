module

public import HeightPaper.Model.HeightPotentialKernel
public import HeightPaper.Model.OutgrowthPath
public import HeightPaper.Probability.GeometricForest

/-!
# Geometric CDF bounds for actual fresh epidemic outgrowths

The upper CDF estimate kills the bounded potential once the susceptible count
falls below a fixed barrier. Its error is consequently one terminal barrier
probability, without a union bound over event times.
-/

@[expose] public section

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace HeightPaper.Model

theorem step_susceptible_le {rate : ℝ≥0} {s t : State}
    (ht : t ∈ (step rate s).support) : t.susceptible ≤ s.susceptible := by
  rcases step_support_cases ht with ⟨_, rfl⟩ | ⟨v, _, rfl | ⟨_, rfl⟩⟩
  · exact le_rfl
  · exact le_rfl
  · exact Nat.sub_le _ _

theorem recoveryProbability_real (rate : ℝ≥0) (n : ℕ) :
    1 - (infectionProbability rate n : ℝ) = 1 / (1 + (rate : ℝ) * n) := by
  have hd : (1 + (rate : ℝ) * n) ≠ 0 := by positivity
  simp only [infectionProbability, NNReal.coe_div, NNReal.coe_add, NNReal.coe_one,
    NNReal.coe_mul, NNReal.coe_natCast]
  field_simp
  ring

theorem recoveryProbability_antitone (rate : ℝ≥0) {m n : ℕ} (hmn : m ≤ n) :
    1 - (infectionProbability rate n : ℝ) ≤ 1 - (infectionProbability rate m : ℝ) := by
  rw [recoveryProbability_real, recoveryProbability_real]
  apply one_div_le_one_div_of_le (by positivity)
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  simpa only [add_comm] using
    add_le_add_left (mul_le_mul_of_nonneg_left hmn' rate.coe_nonneg) 1

/-- Continue the actual epidemic from an arbitrary already explored state. -/
def continuationLaw (rate : ℝ≥0) (s₀ : State) (k : ℕ) : PMF State :=
  FinitePMF.kernelEvolve (PMF.pure s₀) (fun _ ↦ step rate) k

@[simp] theorem continuationLaw_zero (rate : ℝ≥0) (s₀ : State) :
    continuationLaw rate s₀ 0 = PMF.pure s₀ := rfl

theorem continuationLaw_succ (rate : ℝ≥0) (s₀ : State) (k : ℕ) :
    continuationLaw rate s₀ (k + 1) = (continuationLaw rate s₀ k).bind (step rate) := rfl

theorem continuationLaw_initial (rate : ℝ≥0) (n k : ℕ) :
    continuationLaw rate (initial n) k = evolve rate n k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [continuationLaw_succ, ih]; rfl

/-- The Markov continuation identity, for later averaging over a random cutoff
state. The selected-root tail estimates may be applied inside this bind. -/
theorem continuationLaw_add (rate : ℝ≥0) (s₀ : State) (j k : ℕ) :
    continuationLaw rate s₀ (j + k) =
      (continuationLaw rate s₀ j).bind (fun s ↦ continuationLaw rate s k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, continuationLaw_succ, ih, PMF.bind_bind]
      rfl

theorem evolve_add_continuation (rate : ℝ≥0) (n j k : ℕ) :
    evolve rate n (j + k) = (evolve rate n j).bind (fun s ↦ continuationLaw rate s k) := by
  rw [← continuationLaw_initial, continuationLaw_add, continuationLaw_initial]

theorem continuationLaw_support_finite (rate : ℝ≥0) (s₀ : State) (k : ℕ) :
    (continuationLaw rate s₀ k).support.Finite :=
  FinitePMF.kernelEvolve_support_finite _ _ (by simp) (fun _ s ↦ finite_support_step rate s) k

theorem continuationLaw_integrable (rate : ℝ≥0) (s₀ : State) (k : ℕ) (f : State → ℝ) :
    Integrable f (continuationLaw rate s₀ k).toMeasure :=
  FinitePMF.integrable_of_finite_support _ (continuationLaw_support_finite rate s₀ k) f

theorem continuationLaw_integral_succ (rate : ℝ≥0) (s₀ : State) (k : ℕ) (f : State → ℝ) :
    (∫ s, f s ∂(continuationLaw rate s₀ (k + 1)).toMeasure) =
      ∫ s, (∫ t, f t ∂(step rate s).toMeasure) ∂(continuationLaw rate s₀ k).toMeasure :=
  FinitePMF.kernelEvolve_integral_succ _ _ (by simp)
    (fun _ s ↦ finite_support_step rate s) (fun _ ↦ measurable_state _) k f

/-- Birth labels grow and the susceptible count decreases under continuation. -/
theorem continuationLaw_support_bounds (rate : ℝ≥0) (s₀ : State) {k : ℕ} {s : State}
    (hs : s ∈ (continuationLaw rate s₀ k).support) :
    s₀.vertices ≤ s.vertices ∧ s.susceptible ≤ s₀.susceptible := by
  induction k generalizing s with
  | zero =>
      have heq : s = s₀ := by simpa using hs
      subst s
      exact ⟨le_rfl, le_rfl⟩
  | succ k ih =>
      obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
      exact ⟨(ih ht).1.trans (vertices_step_mono hs), (step_susceptible_le hs).trans (ih ht).2⟩

theorem continuationLaw_potential_or_absorbed (rate : ℝ≥0) (s₀ : State)
    {k : ℕ} {s : State} (hs : s ∈ (continuationLaw rate s₀ k).support) :
    potential s + k ≤ potential s₀ ∨ s.active = ∅ := by
  induction k generalizing s with
  | zero =>
      have heq : s = s₀ := by simpa using hs
      subst s
      exact Or.inl (by omega)
  | succ k ih =>
      obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
      rcases ih ht with hb | ha
      · rcases step_support_cases hs with ⟨ht0, rfl⟩ | ⟨v, hv, rfl | ⟨hpos, rfl⟩⟩
        · exact Or.inr ht0
        · have hd := potential_recover hv
          exact Or.inl (by omega)
        · have hd := potential_infect v hpos
          exact Or.inl (by omega)
      · change s ∈ (step rate t).support at hs
        rw [step_absorbed rate ha, PMF.mem_support_pure_iff] at hs
        exact Or.inr (hs ▸ ha)

theorem continuationLaw_absorbed (rate : ℝ≥0) (s₀ : State) {k : ℕ}
    (hk : potential s₀ ≤ k) {s : State} (hs : s ∈ (continuationLaw rate s₀ k).support) :
    s.active = ∅ := by
  rcases continuationLaw_potential_or_absorbed rate s₀ hs with hb | ha
  · apply Finset.card_eq_zero.mp
    simp only [potential, infectious] at hb hk
    omega
  · exact ha

/-- Iterating supported superharmonicity uses exact finite iterated expectation. -/
theorem continuationLaw_integral_le (rate : ℝ≥0) (s₀ : State) (f : State → ℝ)
    (hf : ∀ s, s₀.vertices ≤ s.vertices → s.susceptible ≤ s₀.susceptible →
      (∫ t, f t ∂(step rate s).toMeasure) ≤ f s) (k : ℕ) :
    (∫ s, f s ∂(continuationLaw rate s₀ k).toMeasure) ≤ f s₀ := by
  induction k with
  | zero => simp [PMF.toMeasure_pure]
  | succ k ih =>
      rw [continuationLaw_integral_succ]
      apply le_trans ?_ ih
      apply integral_mono_ae (continuationLaw_integrable _ _ _ _)
        (continuationLaw_integrable _ _ _ _)
      exact FinitePMF.ae_of_forall_mem_support _ fun s hs ↦
        hf s (continuationLaw_support_bounds rate s₀ hs).1
          (continuationLaw_support_bounds rate s₀ hs).2

theorem le_continuationLaw_integral (rate : ℝ≥0) (s₀ : State) (f : State → ℝ)
    (hf : ∀ s, s₀.vertices ≤ s.vertices → s.susceptible ≤ s₀.susceptible →
      f s ≤ ∫ t, f t ∂(step rate s).toMeasure) (k : ℕ) :
    f s₀ ≤ ∫ s, f s ∂(continuationLaw rate s₀ k).toMeasure := by
  have he := continuationLaw_integral_le rate s₀ (fun s ↦ -f s)
    (fun s hv hS ↦ by simpa only [integral_neg, neg_le_neg_iff] using hf s hv hS) k
  simpa only [integral_neg, neg_le_neg_iff] using he

/-- The upper-comparison potential is killed below the susceptible barrier. -/
def killedFreshHeightPotential (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h threshold : ℕ) (s : State) : ℝ :=
  if threshold ≤ s.susceptible then freshHeightPotential p cutoff hcutoff roots h s else 0

theorem killedFreshHeightPotential_le (p : unitInterval) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (roots : Finset ℕ) (h threshold : ℕ) (s : State) :
    killedFreshHeightPotential p cutoff hcutoff roots h threshold s ≤
      freshHeightPotential p cutoff hcutoff roots h s := by
  unfold killedFreshHeightPotential
  split_ifs
  · exact le_rfl
  · exact (freshHeightPotential_bounds _ _ _ _ _ _).1

theorem killedFreshHeightPotential_step_superharmonic (p : unitInterval) (hp : 0 < (p : ℝ))
    (rate : ℝ≥0) (cutoff : ℕ) (hcutoff : 0 < cutoff) (roots : Finset ℕ)
    (h threshold : ℕ) (s : State) (hcut : cutoff ≤ s.vertices)
    (hrp : 1 - (infectionProbability rate threshold : ℝ) ≤ (p : ℝ)) :
    (∫ t, killedFreshHeightPotential p cutoff hcutoff roots h threshold t
      ∂(step rate s).toMeasure) ≤ killedFreshHeightPotential p cutoff hcutoff roots h threshold s := by
  by_cases hS : threshold ≤ s.susceptible
  · rw [killedFreshHeightPotential, ite_eq_left hS]
    apply le_trans (integral_mono
      (FinitePMF.integrable_of_finite_support _ (finite_support_step rate s) _)
      (FinitePMF.integrable_of_finite_support _ (finite_support_step rate s) _)
      (killedFreshHeightPotential_le p cutoff hcutoff roots h threshold))
    exact freshHeightPotential_step_superharmonic p hp rate cutoff hcutoff roots h s hcut
      ((recoveryProbability_antitone rate hS).trans hrp)
  · rw [killedFreshHeightPotential, ite_eq_right hS]
    apply le_of_eq
    apply integral_eq_zero_of_ae
    apply FinitePMF.ae_of_forall_mem_support
    intro t ht
    have htS : ¬threshold ≤ t.susceptible := by
      intro htS
      exact hS (htS.trans (step_susceptible_le ht))
    simp [killedFreshHeightPotential, htS]

/-- At a deterministic extinction horizon, the expected potential is the
actual selected-outgrowth height CDF. -/
theorem freshHeightPotential_terminal_integral (p : unitInterval) (rate : ℝ≥0)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (roots : Finset ℕ) (h : ℕ)
    (s₀ : State) {k : ℕ} (hk : potential s₀ ≤ k) :
    (∫ s, freshHeightPotential p cutoff hcutoff roots h s
      ∂(continuationLaw rate s₀ k).toMeasure) =
        (continuationLaw rate s₀ k).toMeasure.real
          {s | belowFreshHeight cutoff hcutoff roots h s} := by
  calc
    _ = ∫ s, ({s | belowFreshHeight cutoff hcutoff roots h s} : Set State).indicator
        1 s ∂(continuationLaw rate s₀ k).toMeasure := by
      apply integral_congr_ae
      apply FinitePMF.ae_of_forall_mem_support
      intro s hs
      exact freshHeightPotential_terminal p cutoff hcutoff roots h s
        (continuationLaw_absorbed rate s₀ hk hs)
    _ = _ := integral_indicator_one (by trivial)

theorem killedFreshHeightPotential_terminal_integral (p : unitInterval) (rate : ℝ≥0)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (roots : Finset ℕ) (h threshold : ℕ)
    (s₀ : State) {k : ℕ} (hk : potential s₀ ≤ k) :
    (∫ s, killedFreshHeightPotential p cutoff hcutoff roots h threshold s
      ∂(continuationLaw rate s₀ k).toMeasure) =
        (continuationLaw rate s₀ k).toMeasure.real
          {s | belowFreshHeight cutoff hcutoff roots h s ∧ threshold ≤ s.susceptible} := by
  calc
    _ = ∫ s, ({s | belowFreshHeight cutoff hcutoff roots h s ∧ threshold ≤ s.susceptible} :
        Set State).indicator 1 s ∂(continuationLaw rate s₀ k).toMeasure := by
      apply integral_congr_ae
      apply FinitePMF.ae_of_forall_mem_support
      intro s hs
      rw [killedFreshHeightPotential,
        freshHeightPotential_terminal _ _ _ _ _ _ (continuationLaw_absorbed rate s₀ hk hs)]
      by_cases hS : threshold ≤ s.susceptible <;>
        simp [Set.indicator, hS]
    _ = _ := integral_indicator_one (by trivial)

/-- The actual height CDF dominates the independent geometric-forest CDF
whenever the reference recovery probability is below its initial actual value.
The inequality remains valid thereafter because susceptibles decrease. -/
theorem continuation_freshHeight_cdf_lower (p : unitInterval) (hp : 0 < (p : ℝ))
    (rate : ℝ≥0) (s₀ : State) (roots : Finset ℕ) {h : ℕ} (hh : 0 < h)
    (hpr : (p : ℝ) ≤ 1 - (infectionProbability rate s₀.susceptible : ℝ))
    {k : ℕ} (hk : potential s₀ ≤ k) :
    Branching.extinctionProbability p h ^ (s₀.active.filter (fun v ↦ v.val ∈ roots)).card ≤
      (continuationLaw rate s₀ k).toMeasure.real
        {s | belowFreshHeight s₀.vertices s₀.tree.size_pos roots h s} := by
  rw [← freshHeightPotential_terminal_integral p rate _ _ _ _ s₀ hk,
    ← freshHeightPotential_at_cutoff p roots hh s₀]
  apply le_continuationLaw_integral
  intro s hv hS
  exact freshHeightPotential_step_subharmonic p hp rate _ _ _ _ s hv
    (hpr.trans (recoveryProbability_antitone rate hS))

/-- The upper geometric CDF bound is exact on the event that the susceptible
barrier is never crossed. Keeping this event explicit is useful for early
outbreaks, where its probability tends to one on the extinct branch. -/
theorem continuation_freshHeight_cdf_upper_on_barrier (p : unitInterval)
    (hp : 0 < (p : ℝ)) (rate : ℝ≥0) (s₀ : State) (roots : Finset ℕ)
    {h : ℕ} (hh : 0 < h) (threshold : ℕ)
    (hrp : 1 - (infectionProbability rate threshold : ℝ) ≤ (p : ℝ))
    {k : ℕ} (hk : potential s₀ ≤ k) :
    (continuationLaw rate s₀ k).toMeasure.real
        {s | belowFreshHeight s₀.vertices s₀.tree.size_pos roots h s ∧
          threshold ≤ s.susceptible} ≤
      Branching.extinctionProbability p h ^
        (s₀.active.filter (fun v ↦ v.val ∈ roots)).card := by
  have hkill := continuationLaw_integral_le rate s₀
    (killedFreshHeightPotential p s₀.vertices s₀.tree.size_pos roots h threshold)
    (fun s hv _ ↦ killedFreshHeightPotential_step_superharmonic p hp rate _ _ _ _ _ s hv hrp) k
  rw [killedFreshHeightPotential_terminal_integral _ _ _ _ _ _ _ _ hk] at hkill
  apply hkill.trans
  rw [← freshHeightPotential_at_cutoff p roots hh s₀]
  exact killedFreshHeightPotential_le _ _ _ _ _ _ _

/-- The opposite CDF comparison has one explicit susceptible-barrier error.
This is a theorem about the actual epidemic law, with no coupling assumption. -/
theorem continuation_freshHeight_cdf_upper (p : unitInterval) (hp : 0 < (p : ℝ))
    (rate : ℝ≥0) (s₀ : State) (roots : Finset ℕ) {h : ℕ} (hh : 0 < h)
    (threshold : ℕ) (hrp : 1 - (infectionProbability rate threshold : ℝ) ≤ (p : ℝ))
    {k : ℕ} (hk : potential s₀ ≤ k) :
    (continuationLaw rate s₀ k).toMeasure.real
        {s | belowFreshHeight s₀.vertices s₀.tree.size_pos roots h s} ≤
      Branching.extinctionProbability p h ^ (s₀.active.filter (fun v ↦ v.val ∈ roots)).card +
        (continuationLaw rate s₀ k).toMeasure.real {s | s.susceptible < threshold} := by
  have hkill := continuationLaw_integral_le rate s₀
    (killedFreshHeightPotential p s₀.vertices s₀.tree.size_pos roots h threshold)
    (fun s hv _ ↦ killedFreshHeightPotential_step_superharmonic p hp rate _ _ _ _ _ s hv hrp) k
  rw [killedFreshHeightPotential_terminal_integral _ _ _ _ _ _ _ _ hk] at hkill
  have hinit : killedFreshHeightPotential p s₀.vertices s₀.tree.size_pos roots h threshold s₀ ≤
      Branching.extinctionProbability p h ^ (s₀.active.filter (fun v ↦ v.val ∈ roots)).card := by
    rw [← freshHeightPotential_at_cutoff p roots hh s₀]
    exact killedFreshHeightPotential_le _ _ _ _ _ _ _
  calc
    _ ≤ (continuationLaw rate s₀ k).toMeasure.real
        ({s | belowFreshHeight s₀.vertices s₀.tree.size_pos roots h s ∧
          threshold ≤ s.susceptible} ∪ {s | s.susceptible < threshold}) := by
      apply measureReal_mono ?_ (measure_ne_top _ _)
      intro s hs
      by_cases hS : threshold ≤ s.susceptible
      · exact Or.inl ⟨hs, hS⟩
      · exact Or.inr (Nat.lt_of_not_ge hS)
    _ ≤ _ := (measureReal_union_le _ _).trans (add_le_add (hkill.trans hinit) le_rfl)

/-- Actual upper tail for the maximum selected fresh height, with the
independent-forest geometric union estimate fully discharged. -/
theorem continuation_freshHeight_tail_le_geometric {p : unitInterval}
    (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (rate : ℝ≥0) (s₀ : State) (roots : Finset ℕ) {h : ℕ} (hh : 0 < h)
    (hpr : (p : ℝ) ≤ 1 - (infectionProbability rate s₀.susceptible : ℝ))
    {k : ℕ} (hk : potential s₀ ≤ k) :
    (continuationLaw rate s₀ k).toMeasure.real
        {s | ¬belowFreshHeight s₀.vertices s₀.tree.size_pos roots h s} ≤
      ((s₀.active.filter (fun v ↦ v.val ∈ roots)).card : ℝ) * Branching.geometricMean p ^ h := by
  have hp0 : 0 < (p : ℝ) := by linarith
  have hcdf := continuation_freshHeight_cdf_lower p hp0 rate s₀ roots hh hpr hk
  calc
    _ = 1 - (continuationLaw rate s₀ k).toMeasure.real
        {s | belowFreshHeight s₀.vertices s₀.tree.size_pos roots h s} := by
      change (continuationLaw rate s₀ k).toMeasure.real
        ({s | belowFreshHeight s₀.vertices s₀.tree.size_pos roots h s}ᶜ) = _
      rw [measureReal_compl (by trivial), probReal_univ]
    _ ≤ 1 - Branching.extinctionProbability p h ^
        (s₀.active.filter (fun v ↦ v.val ∈ roots)).card := sub_le_sub_left hcdf 1
    _ = Branching.forestHeightTail p (s₀.active.filter (fun v ↦ v.val ∈ roots)).card h := by
      rw [Branching.forestHeightTail_eq, Branching.heightTail_eq_one_sub, sub_sub_cancel]
    _ ≤ _ := Branching.forestHeightTail_le_geometric hp hp1 _ _

/-- Actual lower-tail estimate for the maximum selected fresh height: an
exponentially small geometric-forest term and one susceptible-barrier error. -/
theorem continuation_freshHeight_cdf_le_geometric_exp {p : unitInterval}
    (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (rate : ℝ≥0) (s₀ : State) (roots : Finset ℕ) {h : ℕ} (hh : 0 < h)
    (threshold : ℕ) (hrp : 1 - (infectionProbability rate threshold : ℝ) ≤ (p : ℝ))
    {k : ℕ} (hk : potential s₀ ≤ k) :
    (continuationLaw rate s₀ k).toMeasure.real
        {s | belowFreshHeight s₀.vertices s₀.tree.size_pos roots h s} ≤
      Real.exp (-((s₀.active.filter (fun v ↦ v.val ∈ roots)).card : ℝ) *
        ((1 - Branching.geometricMean p) * Branching.geometricMean p ^ h)) +
        (continuationLaw rate s₀ k).toMeasure.real {s | s.susceptible < threshold} := by
  have hp0 : 0 < (p : ℝ) := by linarith
  apply (continuation_freshHeight_cdf_upper p hp0 rate s₀ roots hh threshold hrp hk).trans
  apply add_le_add _ le_rfl
  rw [← Branching.forestExtinctionProbability_eq]
  exact Branching.forestExtinctionProbability_le_geometric_exp hp hp1 _ _

end HeightPaper.Model
