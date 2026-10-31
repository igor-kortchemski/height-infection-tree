module

public import HeightPaper.Model.HeightMeshLimits
public import HeightPaper.Model.DepthMeshProfile

/-! # Full-tree height bounds from one actual Laplace profile input -/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology NNReal BigOperators

namespace HeightPaper.Model

def depthMeshBase {J : ℕ} (l : ℝ) (x : Fin (J + 1) → ℝ) (pre : ℝ) : DepthMeshBin J → ℝ
  | .low => growthFactor l * Real.exp (x 0)
  | .middle i => growthFactor l * Real.exp (x i.succ)
  | .high => pre

theorem evolve_active_potential_le_remaining {rate : ℝ≥0} {n j : ℕ} {s : State}
    (hs : s ∈ (evolve rate n j).support) (ha : s.active.Nonempty) :
    potential s ≤ 2 * n + 1 - j := by
  rcases evolve_potential_or_absorbed hs with hb | hb
  · omega
  · exact False.elim (ha.ne_empty hb)

theorem tendsto_depthMeshUpper_ratio {J : ℕ} {l pre : ℝ} (hl : 1 < l) (hpre : 0 ≤ pre)
    (x : Fin (J + 1) → ℝ) (b : DepthMeshBin J) :
    Tendsto (fun n : ℕ ↦
      (depthMeshUpper (depthMeshCutoffs l x n) ⌈pre * Real.log n⌉₊ b : ℝ) / Real.log n)
      atTop (𝓝 (depthMeshBase l x pre b)) := by
  cases b with
  | low => exact tendsto_ceil_log_ratio (mul_nonneg (growthFactor_pos hl).le (Real.exp_pos _).le)
  | middle i => exact tendsto_ceil_log_ratio (mul_nonneg (growthFactor_pos hl).le (Real.exp_pos _).le)
  | high => exact tendsto_ceil_log_ratio hpre

private theorem eventually_nat_le_of_ratio {F G : ℕ → ℕ} {f g : ℝ}
    (hF : Tendsto (fun n ↦ (F n : ℝ) / Real.log n) atTop (𝓝 f))
    (hG : Tendsto (fun n ↦ (G n : ℝ) / Real.log n) atTop (𝓝 g)) (hfg : f < g) :
    ∀ᶠ n in atTop, F n ≤ G n := by
  have hneg : f - g < 0 := sub_neg.mpr hfg
  filter_upwards [(hF.sub hG).eventually (gt_mem_nhds hneg), eventually_ge_atTop 2] with n hn hn2
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hcmp : (F n : ℝ) / Real.log n < (G n : ℝ) / Real.log n := by linarith
  exact_mod_cast ((div_lt_div_iff_of_pos_right hlog).mp hcmp).le

/-- The finite covering mesh converts the single real-Laplace input into an
actual upper bound for normalized full-tree height. Only the pre-cutoff height
and pressure estimates remain as probabilistic inputs. -/
theorem normalized_fullHeight_upper_of_laplace
    (rates : ℕ → ℝ≥0) (j K : ℕ → ℕ) {l T pre t u : ℝ} (hl : 1 < l)
    (hT : T ∈ Ioo (0 : ℝ) (fluidExtinctionTime l)) (hpre : 0 < pre) (ht : 0 < t) (htu : t < u)
    (hrates : Tendsto (fun n ↦ (rates n : ℝ) * n) atTop (𝓝 l))
    (hj : Tendsto (fun n ↦ (j n : ℝ) / n) atTop (𝓝 T))
    {J : ℕ} (x : Fin (J + 1) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (0 : ℝ) (profileRoot l))
    (hinc : ∀ i : Fin J, x i.castSucc < x i.succ)
    (hLap : ∀ v ∈ Ioo (0 : ℝ) (profileRoot l), ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ (evolve (rates n) n (j n)).toMeasure.real {s |
        s.active.Nonempty ∧ ε ≤ |Real.log (activeWeight (Real.exp v) s) / Real.log n -
          (1 + growthFactor l * (Real.exp v - 1))|}) atTop (𝓝 0))
    {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (a : DepthMeshBin J → ℝ) (ha : ∀ b, 0 < a b)
    (hgap : ∀ b, depthMeshExponent l x b + a b * Real.log (Branching.geometricMean p) < 0)
    (hmesh : ∀ b, depthMeshBase l x pre b + a b < t)
    (hK : ∀ᶠ n in atTop, ∀ s ∈ (evolve (rates n) n (j n)).support,
      s.active.Nonempty → potential s ≤ K n)
    (hpressure : Tendsto (fun n ↦ (evolve (rates n) n (j n)).toMeasure.real {s |
      s.active.Nonempty ∧ 1 - (infectionProbability (rates n) s.susceptible : ℝ) < (p : ℝ)})
      atTop (𝓝 0))
    (hpreHeight : Tendsto (fun n ↦ (evolve (rates n) n (j n)).toMeasure.real {s |
      s.active.Nonempty ∧ pre < (height s : ℝ) / Real.log n}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (continuationSampleLaw (evolve (rates n) n (j n)) (rates n) (K n)).toMeasure.real
      {s | s.cutoff.active.Nonempty ∧ u ≤ (height s.final : ℝ) / Real.log n}) atTop (𝓝 0) := by
  classical
  let A : ℕ → Set State := fun _ ↦ {s | s.active.Nonempty}
  let G : ℕ → Set State := fun n ↦ {s | height s ≤ ⌈pre * Real.log n⌉₊}
  let D : DepthMeshBin J → ℕ → ℕ := fun b n ↦
    depthMeshUpper (depthMeshCutoffs l x n) ⌈pre * Real.log n⌉₊ b
  let H : DepthMeshBin J → ℕ → ℕ := fun b n ↦ ⌈a b * Real.log n⌉₊
  let level : ℕ → ℕ := fun n ↦ ⌈t * Real.log n⌉₊
  have hlevel := tendsto_ceil_log_ratio ht.le
  have hprelt : pre < t := by have hh := hmesh .high; change pre + a .high < t at hh; linarith [ha .high]
  have hbudget : ∀ᶠ n in atTop, ∀ b ∈ (Finset.univ : Finset (DepthMeshBin J)), D b n + H b n ≤ level n := by
    apply (eventually_all_finset _).mpr
    intro b _
    apply eventually_nat_le_of_ratio _ hlevel (hmesh b)
    convert (tendsto_depthMeshUpper_ratio hl hpre.le x b).add (tendsto_ceil_log_ratio (ha b).le) using 1
    simp only [D, H, Nat.cast_add, add_div]
  have hprebudget : ∀ᶠ n : ℕ in atTop, ⌈pre * Real.log n⌉₊ ≤ level n :=
    eventually_nat_le_of_ratio (tendsto_ceil_log_ratio hpre.le) hlevel hprelt
  have hgeom : ∀ᶠ n in atTop,
      (∀ b ∈ (Finset.univ : Finset (DepthMeshBin J)), D b n + H b n ≤ level n) ∧
      ∀ s ∈ (evolve (rates n) n (j n)).support, s ∈ A n → s ∈ G n →
        height s ≤ level n ∧
        (∀ b ∈ (Finset.univ : Finset (DepthMeshBin J)), depthMeshRoots (depthMeshCutoffs l x n) b s ⊆ activeLabels s) ∧
        (∀ v ∈ s.active, ∃ b ∈ (Finset.univ : Finset (DepthMeshBin J)),
          v.val ∈ depthMeshRoots (depthMeshCutoffs l x n) b s) ∧
        (∀ b ∈ (Finset.univ : Finset (DepthMeshBin J)), ∀ v : Fin s.vertices,
          v.val ∈ depthMeshRoots (depthMeshCutoffs l x n) b s → s.tree.depth v ≤ D b n) := by
    filter_upwards [hbudget, hprebudget] with n hn hpn
    refine ⟨hn, fun s _ _ hs ↦ ⟨hs.trans hpn, ?_, ?_, ?_⟩⟩
    · exact fun b _ ↦ depthMeshRoots_subset_activeLabels _ b s
    · intro v hv
      obtain ⟨b, hb⟩ := depthMeshRoots_cover (depthMeshCutoffs l x n) s v hv
      exact ⟨b, Finset.mem_univ _, hb⟩
    · exact fun b _ v hv ↦ depth_le_depthMeshUpper _ _ b s hs v hv
  have hbad : Tendsto (fun n ↦ (evolve (rates n) n (j n)).toMeasure.real (A n \ G n)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hpreHeight
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    apply measureReal_mono _ (measure_ne_top _ _)
    intro s hs
    simp only [A, G, Set.mem_sdiff, Set.mem_ofPred_eq, not_le] at hs ⊢
    exact ⟨hs.1, (lt_div_iff₀ hlog).mpr ((Nat.le_ceil _).trans_lt (by exact_mod_cast hs.2))⟩
  have hfull := fullHeight_upper_mesh_of_profiles rates j K level Finset.univ
    (fun b n ↦ depthMeshRoots (depthMeshCutoffs l x n) b) D H A G hp hp1
    (depthMeshExponent l x) a (fun b _ ↦ depthMeshExponent_pos hl x hx b) (fun b _ ↦ ha b)
    (fun b _ ↦ depthMeshRoots_profile_of_laplace rates j hl hT hrates hj x hx hinc hLap b)
    (fun b _ ↦ tendsto_ceil_log_ratio (ha b).le) hK hpressure (fun b _ ↦ hgap b) hgeom hbad
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hfull
  filter_upwards [hlevel.eventually (gt_mem_nhds htu), eventually_ge_atTop 2] with n hn hn2
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  apply measureReal_mono _ (measure_ne_top _ _)
  intro s hs
  refine ⟨hs.1, ?_⟩
  have hh : (level n : ℝ) / Real.log n < (height s.final : ℝ) / Real.log n := hn.trans_le hs.2
  exact_mod_cast (div_lt_div_iff_of_pos_right hlog).mp hh

end HeightPaper.Model
