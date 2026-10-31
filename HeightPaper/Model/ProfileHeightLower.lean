module

public import HeightPaper.Model.HeightMeshLimits
public import HeightPaper.Model.OutgrowthBins

/-! # A full-height lower bound from one interior profile exponent -/

public section

open Filter Set MeasureTheory
open scoped Topology NNReal

namespace HeightPaper.Model

/-- Every interior profile point gives its base-depth plus fresh-height lower
bound for the actual infection tree. The fresh tail is proved from the profile
input and the finite susceptible barrier estimate. -/
theorem normalized_fullHeight_lower_of_laplace
    (rates : ℕ → ℝ≥0) (j K L : ℕ → ℕ) {l x a t : ℝ} (hl : 1 < l)
    (hx : x ∈ Ioo (0 : ℝ) (profileRoot l)) (ha : 0 < a)
    (ht : t < growthFactor l * Real.exp x + a)
    (hLap : ∀ v ∈ Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (evolve (rates n) n (j n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp v) s) / Real.log n -
          (1 + growthFactor l * (Real.exp v - 1))|}) atTop (𝓝 0))
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hgap : 0 < profileExponent l x + a * Real.log (Branching.geometricMean p))
    (hK : ∀ᶠ n in atTop, ∀ s ∈ (evolve (rates n) n (j n)).support,
      s.active.Nonempty → potential s ≤ K n)
    (hpressure : ∀ᶠ n in atTop, 1 - (infectionProbability (rates n) (L n) : ℝ) ≤ (p : ℝ))
    (hbarrier : Tendsto (fun n ↦
      (continuationSampleLaw (evolve (rates n) n (j n)) (rates n) (K n)).toMeasure.real
        {s | s.cutoff.active.Nonempty ∧ s.final.susceptible < L n}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (continuationSampleLaw (evolve (rates n) n (j n)) (rates n) (K n)).toMeasure.real
      {s | s.cutoff.active.Nonempty ∧ (height s.final : ℝ) / Real.log n ≤ t}) atTop (𝓝 0) := by
  let β := growthFactor l * Real.exp x
  have hβ : 0 < β := mul_pos (growthFactor_pos hl) (Real.exp_pos x)
  let d : ℕ → ℕ := fun n ↦ ⌊β * Real.log n⌋₊
  let H : ℕ → ℕ := fun n ↦ ⌈a * Real.log n⌉₊
  let roots : ℕ → State → Finset ℕ := fun n s ↦ activeTailRoots s (β * Real.log n)
  let A : ℕ → Set State := fun _ ↦ {s | s.active.Nonempty}
  have hprofile : ∀ ε > (0 : ℝ), Tendsto (fun n ↦
      (evolve (rates n) n (j n)).toMeasure.real {s | s ∈ A n ∧
        ε ≤ |Real.log (selectedRootCount s (roots n s)) / Real.log n - profileExponent l x|}) atTop (𝓝 0) := by
    intro ε hε
    simpa only [roots, A, β, selectedRootCount_activeTailRoots, Set.mem_ofPred_eq] using
      activeTailCount_log_convergence_of_laplace rates j hl hx hLap ε hε
  have hgeom : ∀ᶠ n in atTop, ∀ s ∈ (evolve (rates n) n (j n)).support, s ∈ A n →
      roots n s ⊆ activeLabels s ∧
        ∀ v : Fin s.vertices, v.val ∈ roots n s → d n ≤ s.tree.depth v := by
    apply Eventually.of_forall
    intro n s _ _
    constructor
    · intro r hr
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_image.mpr ⟨v, (Finset.mem_filter.mp hv).1, rfl⟩
    · intro v hv
      have hh := ((mem_activeTailRoots s _ v).mp hv).2
      simpa only [d, Nat.floor_natCast] using Nat.floor_mono hh
  have hfull := fullHeight_lower_bin_of_profile rates j K d H L roots A hp hp1
    (profileExponent_pos hl hx.1.le hx.2) ha hprofile (tendsto_ceil_log_ratio ha.le)
    hK hpressure hbarrier hgap hgeom
  have hd : Tendsto (fun n ↦ (d n : ℝ) / Real.log n) atTop (𝓝 β) :=
    (tendsto_nat_floor_mul_div_atTop hβ.le).comp tendsto_log_nat_atTop
  have hs : Tendsto (fun n ↦ ((d n + H n : ℕ) : ℝ) / Real.log n) atTop (𝓝 (β + a)) := by
    simpa only [Nat.cast_add, add_div] using hd.add (tendsto_ceil_log_ratio ha.le)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hfull
  filter_upwards [hs.eventually (lt_mem_nhds ht), eventually_ge_atTop 2] with n hn hn2
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  apply measureReal_mono _ (measure_ne_top _ _)
  intro s hs
  refine ⟨hs.1, ?_⟩
  have hh : (height s.final : ℝ) / Real.log n < (d n + H n : ℕ) / Real.log n := hs.2.trans_lt hn
  exact_mod_cast (div_lt_div_iff_of_pos_right hlog).mp hh

end HeightPaper.Model
