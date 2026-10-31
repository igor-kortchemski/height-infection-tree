module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-!
# Finite approximation of the variational height constant

The final proof of `thm:main` approximates a continuous function on a compact
interval by finitely many values. The lemmas here isolate the deterministic
approximation argument; they make no probabilistic assertion about the tree.
-/

public section

open Set Filter
open scoped Topology

namespace HeightPaper.Analysis

/-- A finite mesh maximum stays below any upper bound for the entire interval. -/
theorem meshMaximum_le {f : ℝ → ℝ} {z M : ℝ} {s : Finset ℝ}
    (hs : s.Nonempty) (hsub : ∀ x ∈ s, x ∈ Icc 0 z)
    (hbound : ∀ x ∈ Icc 0 z, f x ≤ M) : s.sup' hs f ≤ M := by
  exact Finset.sup'_le hs f fun x hx ↦ hbound x (hsub x hx)

/-- A mesh that approximates every point within a modulus of continuity
approximates the supremum with the same error. -/
theorem sSup_le_meshMaximum_add {f : ℝ → ℝ} {z ε δ : ℝ} {s : Finset ℝ}
    (hz : 0 ≤ z) (hs : s.Nonempty)
    (hsub : ∀ x ∈ s, x ∈ Icc 0 z)
    (hcover : ∀ x ∈ Icc 0 z, ∃ y ∈ s, dist x y < δ)
    (hmod : ∀ x ∈ Icc 0 z, ∀ y ∈ Icc 0 z, dist x y < δ → dist (f x) (f y) < ε) :
    sSup (f '' Icc 0 z) ≤ s.sup' hs f + ε := by
  apply csSup_le ((nonempty_Icc.mpr hz).image f)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hcover x hx
  have hclose := hmod x hx y (hsub y hy) hxy
  have hupper := Finset.le_sup' f hy
  rw [Real.dist_eq] at hclose
  have := (abs_lt.mp hclose).2
  linarith

/-- Finite meshes whose covering radius tends to zero recover the supremum
of a continuous function on a compact interval. -/
theorem tendsto_meshMaximum {f : ℝ → ℝ} {z : ℝ} (hz : 0 ≤ z)
    (hf : ContinuousOn f (Icc 0 z)) (s : ℕ → Finset ℝ)
    (hs : ∀ n, (s n).Nonempty)
    (hsub : ∀ n x, x ∈ s n → x ∈ Icc 0 z)
    (hcover : ∀ δ > 0, ∀ᶠ n in atTop, ∀ x ∈ Icc 0 z, ∃ y ∈ s n, dist x y < δ) :
    Tendsto (fun n ↦ (s n).sup' (hs n) f) atTop (𝓝 (sSup (f '' Icc 0 z))) := by
  have hbdd : BddAbove (f '' Icc 0 z) := isCompact_Icc.bddAbove_image hf
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcover δ hδ)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hlo := sSup_le_meshMaximum_add hz (hs n) (hsub n) (hN n hn) hmod
  have hhi : (s n).sup' (hs n) f ≤ sSup (f '' Icc 0 z) :=
    meshMaximum_le (hs n) (hsub n) fun x hx ↦ le_csSup hbdd ⟨x, hx, rfl⟩
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hhi)]
  linarith

/-- The regular mesh with `n + 1` intervals, including both endpoints. -/
@[expose] noncomputable def regularGrid (z : ℝ) (n : ℕ) : Finset ℝ :=
  (Finset.range (n + 2)).image fun (i : ℕ) ↦ z * (i : ℝ) / (n + 1 : ℕ)

theorem regularGrid_nonempty (z : ℝ) (n : ℕ) : (regularGrid z n).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨0, Finset.mem_range.mpr (by omega), by simp⟩

theorem regularGrid_subset {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    ∀ x ∈ regularGrid z n, x ∈ Icc 0 z := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hi' : (i : ℝ) ≤ (n + 1 : ℕ) := by
    exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hd : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  refine ⟨by positivity, (div_le_iff₀ hd).mpr ?_⟩
  exact mul_le_mul_of_nonneg_left hi' hz

theorem regularGrid_covers {z : ℝ} (hz : 0 < z) (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc 0 z) :
    ∃ y ∈ regularGrid z n, dist x y < z / (n + 1 : ℕ) := by
  let d : ℝ := (n + 1 : ℕ)
  have hd : 0 < d := by dsimp [d]; positivity
  let i : ℕ := ⌊d * x / z⌋₊
  have hq : 0 ≤ d * x / z := div_nonneg (mul_nonneg hd.le hx.1) hz.le
  have hi : i ≤ n + 1 := by
    apply Nat.floor_le_of_le
    change d * x / z ≤ d
    rw [div_le_iff₀ hz]
    exact mul_le_mul_of_nonneg_left hx.2 hd.le
  have hlo : (i : ℝ) ≤ d * x / z := Nat.floor_le hq
  have hhi : d * x / z < (i : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨z * (i : ℝ) / d, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  · rw [Real.dist_eq, abs_of_nonneg]
    · apply (lt_div_iff₀ hd).mpr
      have hhi' := (div_lt_iff₀ hz).mp hhi
      have heq : (x - z * (i : ℝ) / d) * d = d * x - z * (i : ℝ) := by
        field_simp
      rw [heq]
      nlinarith
    · apply sub_nonneg.mpr
      apply (div_le_iff₀ hd).mpr
      have hlo' := (le_div_iff₀ hz).mp hlo
      nlinarith

/-- Maxima on explicit equally spaced grids converge to the variational
supremum, with no differentiability assumption. -/
theorem tendsto_regularGridMaximum {f : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hf : ContinuousOn f (Icc 0 z)) :
    Tendsto (fun n ↦ (regularGrid z n).sup' (regularGrid_nonempty z n) f)
      atTop (𝓝 (sSup (f '' Icc 0 z))) := by
  apply tendsto_meshMaximum hz.le hf (regularGrid z) (regularGrid_nonempty z)
    (regularGrid_subset hz.le)
  intro δ hδ
  have hlim : Tendsto (fun n : ℕ ↦ z / (n + 1 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn
  intro x hx
  obtain ⟨y, hy, hxy⟩ := regularGrid_covers hz n hx
  exact ⟨y, hy, hxy.trans hn⟩

/-- Taking a finite maximum does not increase a uniform perturbation bound. -/
theorem dist_meshMaximum_le {s : Finset ℝ} (hs : s.Nonempty)
    (f g : ℝ → ℝ) {ε : ℝ} (hclose : ∀ x ∈ s, dist (f x) (g x) ≤ ε) :
    dist (s.sup' hs f) (s.sup' hs g) ≤ ε := by
  have hfg : s.sup' hs f ≤ s.sup' hs g + ε := by
    apply Finset.sup'_le
    intro x hx
    have hxclose := (abs_le.mp (show |f x - g x| ≤ ε from hclose x hx)).2
    have hmax := Finset.le_sup' g hx
    linarith
  have hgf : s.sup' hs g ≤ s.sup' hs f + ε := by
    apply Finset.sup'_le
    intro x hx
    have hxclose := (abs_le.mp (show |f x - g x| ≤ ε from hclose x hx)).1
    have hmax := Finset.le_sup' f hx
    linarith
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-- The upper sums in the final height proof also converge to the same
supremum: evaluate the first summand at the next mesh point (capped at `z`),
and the second at the current point. -/
theorem tendsto_shiftedRegularGridMaximum {a b : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (ha : ContinuousOn a (Icc 0 z)) (hb : ContinuousOn b (Icc 0 z)) :
    Tendsto
      (fun n ↦ (regularGrid z n).sup' (regularGrid_nonempty z n)
        (fun x ↦ a (min (x + z / (n + 1 : ℕ)) z) + b x))
      atTop (𝓝 (sSup ((fun x ↦ a x + b x) '' Icc 0 z))) := by
  have hbase := tendsto_regularGridMaximum hz (ha.add hb)
  apply hbase.congr_dist
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous ha
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (by linarith)
  have hlim : Tendsto (fun n : ℕ ↦ z / (n + 1 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn ↦ ?_⟩
  have hmax : dist
      ((regularGrid z n).sup' (regularGrid_nonempty z n) (fun x ↦ a x + b x))
      ((regularGrid z n).sup' (regularGrid_nonempty z n)
        (fun x ↦ a (min (x + z / (n + 1 : ℕ)) z) + b x)) ≤ ε / 2 := by
    apply dist_meshMaximum_le
    intro x hx
    have hxI := regularGrid_subset hz.le n x hx
    have hstep : 0 ≤ z / (n + 1 : ℕ) := by positivity
    have hnext : min (x + z / (n + 1 : ℕ)) z ∈ Icc 0 z := by
      exact ⟨le_min (by linarith [hxI.1]) hz.le, min_le_right _ _⟩
    have hxnext : x ≤ min (x + z / (n + 1 : ℕ)) z :=
      le_min (by linarith) hxI.2
    have hdist : dist x (min (x + z / (n + 1 : ℕ)) z) < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxnext)]
      have := min_le_left (x + z / (n + 1 : ℕ)) z
      linarith [hN n hn]
    have haClose := hmod x hxI _ hnext hdist
    simpa only [Real.dist_eq, add_sub_add_right_eq_sub] using haClose.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
  exact lt_of_le_of_lt hmax (by linarith)

/-- Contract a grid point slightly towards the interval's midpoint, so every
sample lies strictly inside the domain where the paper's profile estimates hold. -/
@[expose] noncomputable def interiorShift (z : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((n + 1 : ℕ) * x + z) / (n + 3 : ℕ)

theorem interiorShift_mem_Ioo {z x : ℝ} (hz : 0 < z) (n : ℕ)
    (hx : x ∈ Icc 0 z) : interiorShift z n x ∈ Ioo 0 z := by
  have hd : (0 : ℝ) < (n + 3 : ℕ) := by positivity
  have hcoef : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  unfold interiorShift
  constructor
  · exact div_pos (by nlinarith [mul_nonneg hcoef.le hx.1]) hd
  · apply (div_lt_iff₀ hd).mpr
    have hmul := mul_le_mul_of_nonneg_left hx.2 hcoef.le
    push_cast at *
    nlinarith

theorem dist_interiorShift_le {z x : ℝ} (n : ℕ)
    (hx : x ∈ Icc 0 z) : dist x (interiorShift z n x) ≤ z / (n + 3 : ℕ) := by
  have hd : (0 : ℝ) < (n + 3 : ℕ) := by positivity
  rw [Real.dist_eq, abs_le]
  unfold interiorShift
  constructor
  · apply (neg_le_sub_iff_le_add).mpr
    have heq : ((n + 1 : ℕ) * x + z) / (n + 3 : ℕ) ≤ x + z / (n + 3 : ℕ) := by
      apply (div_le_iff₀ hd).mpr
      have hid : (x + z / (n + 3 : ℕ)) * (n + 3 : ℕ) = x * (n + 3 : ℕ) + z := by
        field_simp
      rw [hid]
      push_cast
      nlinarith [hx.1]
    exact heq
  · apply (sub_le_iff_le_add).mpr
    rw [← add_div]
    apply (le_div_iff₀ hd).mpr
    push_cast
    nlinarith [hx.2]

/-- An explicit finite mesh contained in the open interval `(0,z)`. -/
@[expose] noncomputable def interiorGrid (z : ℝ) (n : ℕ) : Finset ℝ :=
  (regularGrid z n).image (interiorShift z n)

theorem interiorGrid_nonempty (z : ℝ) (n : ℕ) : (interiorGrid z n).Nonempty :=
  (regularGrid_nonempty z n).image _

theorem interiorGrid_subset {z : ℝ} (hz : 0 < z) (n : ℕ) :
    ∀ x ∈ interiorGrid z n, x ∈ Ioo 0 z := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact interiorShift_mem_Ioo hz n (regularGrid_subset hz.le n y hy)

/-- Interior grid maxima recover the same supremum. This form avoids applying
strict-domain profile estimates at either endpoint. -/
theorem tendsto_interiorGridMaximum {f : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hf : ContinuousOn f (Icc 0 z)) :
    Tendsto (fun n ↦ (interiorGrid z n).sup' (interiorGrid_nonempty z n) f)
      atTop (𝓝 (sSup (f '' Icc 0 z))) := by
  apply tendsto_meshMaximum hz.le hf (interiorGrid z) (interiorGrid_nonempty z)
    (fun n x hx ↦ Ioo_subset_Icc_self (interiorGrid_subset hz n x hx))
  intro δ hδ
  have hlim (k : ℕ) : Tendsto (fun n : ℕ ↦ z / (n + k : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat k)
  filter_upwards [(hlim 1).eventually (gt_mem_nhds (show 0 < δ / 2 by linarith)),
    (hlim 3).eventually (gt_mem_nhds (show 0 < δ / 2 by linarith))] with n hn₁ hn₃
  intro x hx
  obtain ⟨y, hy, hxy⟩ := regularGrid_covers hz n hx
  refine ⟨interiorShift z n y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
  have hyShift := dist_interiorShift_le n (regularGrid_subset hz.le n y hy)
  have htri := dist_triangle x y (interiorShift z n y)
  linarith

end HeightPaper.Analysis
