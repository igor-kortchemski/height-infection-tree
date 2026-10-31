module

public import HeightPaper.Model.DepthMeshHeight
public import HeightPaper.Analysis.HeightMeshChoice

/-! # Strict numerical margins for the probabilistic height mesh -/

public section

open Filter Set
open scoped Topology

namespace HeightPaper.Model

/-- A comparison mean strictly above the limiting offspring mean and a finite
interior mesh suffice for every strict upper-height tolerance. -/
theorem exists_upper_height_parameters {l ε : ℝ} (hl : 1 < l) (hε : 0 < ε) :
    ∃ (J : ℕ) (x : Fin (J + 1) → ℝ) (m pre t : ℝ) (a : DepthMeshBin J → ℝ),
      (∀ i, x i ∈ Ioo (0 : ℝ) (profileRoot l)) ∧
      (∀ i : Fin J, x i.castSucc < x i.succ) ∧
      offspringMean l < m ∧ m < 1 ∧
      growthFactor l * Real.exp (profileRoot l) < pre ∧ 0 < pre ∧
      0 < t ∧ t < heightCoefficient l + ε ∧
      (∀ b, 0 < a b) ∧
      (∀ b, depthMeshExponent l x b + a b * Real.log m < 0) ∧
      (∀ b, depthMeshBase l x pre b + a b < t) := by
  classical
  have hε8 : 0 < ε / 8 := by positivity
  obtain ⟨J, hlo, hmid, hhi⟩ := Analysis.exists_height_upper_mesh hl hε8
  let x := Analysis.heightMeshCutpoints (profileRoot l) J
  let pre := growthFactor l * Real.exp (profileRoot l) + ε / 8
  let t := heightCoefficient l + ε / 2
  have hx : ∀ i, x i ∈ Ioo (0 : ℝ) (profileRoot l) :=
    Analysis.heightMeshCutpoints_mem (profileRoot_pos hl) J
  have hpre : 0 < pre := add_pos (mul_pos (growthFactor_pos hl) (Real.exp_pos _)) hε8
  have hbase : ∀ b : DepthMeshBin J,
      depthMeshBase l x pre b + depthMeshExponent l x b / outgrowthRate l + ε / 8 < t := by
    intro b
    cases b with
    | low => change growthFactor l * Real.exp (x 0) + 1 / outgrowthRate l + ε / 8 < t; dsimp [t, x]; linarith
    | middle i =>
        change growthFactor l * Real.exp (x i.succ) +
          profileExponent l (x i.castSucc) / outgrowthRate l + ε / 8 < t
        have hh := hmid i
        dsimp [t, x]
        linarith
    | high =>
        change pre + profileExponent l (x (Fin.last J)) / outgrowthRate l + ε / 8 < t
        dsimp [pre, t, x]
        linarith
  let mseq : ℕ → ℝ := fun n ↦ offspringMean l + (1 - offspringMean l) / (n + 2 : ℕ)
  have hm0 := offspringMean_pos hl
  have hm1 := offspringMean_lt_one hl
  have hmseq : ∀ n, offspringMean l < mseq n ∧ mseq n < 1 := by
    intro n
    have hd : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    have hd2 : (2 : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast (show 2 ≤ n + 2 by omega)
    have hpos : 0 < (1 - offspringMean l) / (n + 2 : ℕ) := div_pos (sub_pos.mpr hm1) hd
    have hlt : (1 - offspringMean l) / (n + 2 : ℕ) < 1 - offspringMean l := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    dsimp [mseq]
    constructor <;> linarith
  have hmseq_lim : Tendsto mseq atTop (𝓝 (offspringMean l)) := by
    have hz : Tendsto (fun n : ℕ ↦ (1 - offspringMean l) / (n + 2 : ℕ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    simpa only [mseq, add_zero] using tendsto_const_nhds.add hz
  have hlog0 : -Real.log (offspringMean l) ≠ 0 := (outgrowthRate_pos hl).ne'
  have hclose : ∀ᶠ n in atTop, ∀ b ∈ (Finset.univ : Finset (DepthMeshBin J)),
      depthMeshBase l x pre b + depthMeshExponent l x b / (-Real.log (mseq n)) + ε / 8 < t := by
    apply (eventually_all_finset _).mpr
    intro b _
    have hlim : Tendsto (fun n ↦ depthMeshBase l x pre b +
        depthMeshExponent l x b / (-Real.log (mseq n))) atTop
        (𝓝 (depthMeshBase l x pre b + depthMeshExponent l x b / outgrowthRate l)) :=
      tendsto_const_nhds.add
        (tendsto_const_nhds.div (((Real.continuousAt_log hm0.ne').tendsto.comp hmseq_lim).neg) hlog0)
    exact (hlim.add_const (ε / 8)).eventually (gt_mem_nhds (hbase b))
  obtain ⟨n, hn⟩ := hclose.exists
  let m := mseq n
  have hm : 0 < m := hm0.trans (hmseq n).1
  have hm' : m < 1 := (hmseq n).2
  have hlog : Real.log m < 0 := Real.log_neg hm hm'
  let a : DepthMeshBin J → ℝ := fun b ↦ depthMeshExponent l x b / (-Real.log m) + ε / 8
  refine ⟨J, x, m, pre, t, a, hx,
    Analysis.heightMeshCutpoints_strict (profileRoot_pos hl) J,
    (hmseq n).1, hm', by dsimp [pre]; linarith, hpre,
    add_pos (heightCoefficient_pos hl) (half_pos hε), by dsimp [t]; linarith, ?_, ?_, ?_⟩
  · intro b
    exact add_pos (div_pos (depthMeshExponent_pos hl x hx b) (neg_pos.mpr hlog)) hε8
  · intro b
    have hmul := div_mul_cancel₀ (depthMeshExponent l x b) (neg_ne_zero.mpr hlog.ne)
    have hneg := mul_neg_of_pos_of_neg hε8 hlog
    dsimp [a]
    nlinarith
  · intro b
    have hh := hn b (Finset.mem_univ _)
    dsimp [a, m]
    linarith

/-- A comparison mean strictly below the limiting offspring mean and one
interior profile point suffice for every strict lower-height tolerance. -/
theorem exists_lower_height_parameters {l ε : ℝ} (hl : 1 < l) (hε : 0 < ε) :
    ∃ (x m a : ℝ), x ∈ Ioo (0 : ℝ) (profileRoot l) ∧
      0 < m ∧ m < offspringMean l ∧ 0 < a ∧
      heightCoefficient l - ε < growthFactor l * Real.exp x + a ∧
      0 < profileExponent l x + a * Real.log m := by
  obtain ⟨x, hx, hheight⟩ := Analysis.exists_height_lower_point hl (half_pos hε)
  have hf := profileExponent_pos hl hx.1.le hx.2
  have hR := outgrowthRate_pos hl
  have hq : 0 < profileExponent l x / outgrowthRate l := div_pos hf hR
  have hgap : heightCoefficient l - ε - growthFactor l * Real.exp x <
      profileExponent l x / outgrowthRate l := by
    change heightCoefficient l - ε / 2 < growthFactor l * Real.exp x +
      profileExponent l x / outgrowthRate l at hheight
    linarith
  obtain ⟨a, ha, haq⟩ := exists_between (max_lt hq hgap)
  have ha0 : 0 < a := (le_max_left _ _).trans_lt ha
  have htarget : heightCoefficient l - ε < growthFactor l * Real.exp x + a := by
    have hh := (le_max_right _ _).trans_lt ha
    linarith
  have hbase : 0 < profileExponent l x + a * Real.log (offspringMean l) := by
    have hh := (lt_div_iff₀ hR).mp haq
    change a * (-Real.log (offspringMean l)) < profileExponent l x at hh
    linarith
  let mseq : ℕ → ℝ := fun n ↦ offspringMean l - offspringMean l / (n + 2 : ℕ)
  have hm0 := offspringMean_pos hl
  have hmseq : ∀ n, 0 < mseq n ∧ mseq n < offspringMean l := by
    intro n
    have hd : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    have hd2 : (2 : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast (show 2 ≤ n + 2 by omega)
    have hpos : 0 < offspringMean l / (n + 2 : ℕ) := div_pos hm0 hd
    have hlt : offspringMean l / (n + 2 : ℕ) < offspringMean l := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    dsimp [mseq]
    constructor <;> linarith
  have hlim : Tendsto mseq atTop (𝓝 (offspringMean l)) := by
    have hz : Tendsto (fun n : ℕ ↦ offspringMean l / (n + 2 : ℕ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    simpa only [mseq, sub_zero] using tendsto_const_nhds.sub hz
  have hprofile : Tendsto (fun n ↦ profileExponent l x + a * Real.log (mseq n)) atTop
      (𝓝 (profileExponent l x + a * Real.log (offspringMean l))) :=
    tendsto_const_nhds.add
      (tendsto_const_nhds.mul ((Real.continuousAt_log hm0.ne').tendsto.comp hlim))
  obtain ⟨n, hn⟩ := (hprofile.eventually (lt_mem_nhds hbase)).exists
  exact ⟨x, mseq n, a, hx, (hmseq n).1, (hmseq n).2, ha0, htarget, hn⟩

end HeightPaper.Model
