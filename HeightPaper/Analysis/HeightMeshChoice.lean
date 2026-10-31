module

public import HeightPaper.Analysis.Parameters
public import HeightPaper.Analysis.Mesh

/-! # Choosing interior profile bins near the variational height constant -/

@[expose] public section

open Filter Set
open scoped Topology

noncomputable section

namespace HeightPaper.Analysis

/-- Equally spaced interior cutpoints; the two boundary intervals are kept
separate because their root-count estimates have different forms. -/
def heightMeshCutpoints (z : ℝ) (J : ℕ) (i : Fin (J + 1)) : ℝ :=
  z * (i.val + 1 : ℕ) / (J + 2 : ℕ)

theorem heightMeshCutpoints_mem {z : ℝ} (hz : 0 < z) (J : ℕ) (i : Fin (J + 1)) :
    heightMeshCutpoints z J i ∈ Ioo 0 z := by
  have hd : (0 : ℝ) < (J + 2 : ℕ) := by positivity
  have hi : (i.val + 1 : ℕ) < J + 2 := by omega
  have hic : ((i.val + 1 : ℕ) : ℝ) < (J + 2 : ℕ) := by exact_mod_cast hi
  constructor
  · exact div_pos (mul_pos hz (by positivity)) hd
  · exact (div_lt_iff₀ hd).mpr (mul_lt_mul_of_pos_left hic hz)

theorem heightMeshCutpoints_strict {z : ℝ} (hz : 0 < z) (J : ℕ) (i : Fin J) :
    heightMeshCutpoints z J i.castSucc < heightMeshCutpoints z J i.succ := by
  unfold heightMeshCutpoints
  apply div_lt_div_of_pos_right _ (by positivity)
  apply mul_lt_mul_of_pos_left _ hz
  exact_mod_cast (show i.val + 1 < i.val + 1 + 1 by omega)

/-- The mesh upper sums, including both exceptional endpoint bins, can be
chosen arbitrarily close to the paper's variational height coefficient. -/
theorem exists_height_upper_mesh {l ε : ℝ} (hl : 1 < l) (hε : 0 < ε) :
    ∃ J : ℕ,
      growthFactor l * Real.exp (heightMeshCutpoints (profileRoot l) J 0) +
          1 / outgrowthRate l < heightCoefficient l + ε ∧
      (∀ i : Fin J,
        growthFactor l * Real.exp (heightMeshCutpoints (profileRoot l) J i.succ) +
          profileExponent l (heightMeshCutpoints (profileRoot l) J i.castSucc) /
            outgrowthRate l < heightCoefficient l + ε) ∧
      growthFactor l * Real.exp (profileRoot l) +
          profileExponent l (heightMeshCutpoints (profileRoot l) J (Fin.last J)) /
            outgrowthRate l < heightCoefficient l + ε := by
  let z := profileRoot l
  have hz : 0 < z := profileRoot_pos hl
  let a : ℝ → ℝ := fun x ↦ growthFactor l * Real.exp x
  have ha : Continuous a := continuous_const.mul Real.continuous_exp
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous ha.continuousOn) ε hε
  have hstep : Tendsto (fun J : ℕ ↦ z / (J + 2 : ℕ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  obtain ⟨J, hJ⟩ := (hstep.eventually (gt_mem_nhds hδ)).exists
  have hd : (0 : ℝ) < (J + 2 : ℕ) := by positivity
  have hpiece {x y : ℝ} (hx : x ∈ Icc 0 z) (hy : y ∈ Icc 0 z)
      (hxy : dist x y < δ) :
      a y + profileExponent l x / outgrowthRate l < heightCoefficient l + ε := by
    have hc := hmod x hx y hy hxy
    rw [Real.dist_eq] at hc
    have hb := heightIntegrand_le_heightCoefficient hl hx.2
    change a x + profileExponent l x / outgrowthRate l ≤ heightCoefficient l at hb
    have hc' := (abs_lt.mp hc).1
    linarith
  refine ⟨J, ?_, ?_, ?_⟩
  · have hx := heightMeshCutpoints_mem hz J 0
    have he : heightMeshCutpoints z J 0 = z / (J + 2 : ℕ) := by
      simp [heightMeshCutpoints]
    have hc := hpiece (x := 0) ⟨le_rfl, hz.le⟩ (Ioo_subset_Icc_self hx) (by
      rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hx.1, he]
      exact hJ)
    simpa only [a, profileExponent_zero] using hc
  · intro i
    have hx := heightMeshCutpoints_mem hz J i.castSucc
    have hy := heightMeshCutpoints_mem hz J i.succ
    apply hpiece (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy)
    have he : heightMeshCutpoints z J i.succ - heightMeshCutpoints z J i.castSucc =
        z / (J + 2 : ℕ) := by
      unfold heightMeshCutpoints
      simp only [Fin.val_succ, Fin.val_castSucc]
      push_cast
      ring
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (heightMeshCutpoints_strict hz J i).le)]
    linarith
  · have hx := heightMeshCutpoints_mem hz J (Fin.last J)
    apply hpiece (Ioo_subset_Icc_self hx) ⟨hz.le, le_rfl⟩
    have he : z - heightMeshCutpoints z J (Fin.last J) = z / (J + 2 : ℕ) := by
      unfold heightMeshCutpoints
      simp only [Fin.val_last]
      push_cast
      field_simp
      ring
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.2.le)]
    linarith

/-- An interior profile bin suffices for the height lower bound, even when
the variational maximum occurs at an endpoint. -/
theorem exists_height_lower_point {l ε : ℝ} (hl : 1 < l) (hε : 0 < ε) :
    ∃ x ∈ Ioo (0 : ℝ) (profileRoot l),
      heightCoefficient l - ε < heightIntegrand l x := by
  have ht := tendsto_interiorGridMaximum (profileRoot_pos hl)
    (continuous_heightIntegrand l).continuousOn
  rw [← heightCoefficient_eq_sup hl] at ht
  obtain ⟨J, hJ⟩ := (ht.eventually (lt_mem_nhds (show heightCoefficient l - ε <
    heightCoefficient l by linarith))).exists
  obtain ⟨x, hx, he⟩ := Finset.exists_mem_eq_sup'
    (interiorGrid_nonempty (profileRoot l) J) (heightIntegrand l)
  exact ⟨x, interiorGrid_subset (profileRoot_pos hl) J x hx, he ▸ hJ⟩

end HeightPaper.Analysis
