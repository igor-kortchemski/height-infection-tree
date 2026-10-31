module

public import HeightPaper.Probability.CorrectedCouplingHeightTail

/-!
# Uniform height comparison for the actual coupled bounding trees

The constant is chosen before the root count, root index, source rates,
and height. Both natural and nonnegative real height thresholds are covered.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace HeightPaper.CountCoupling

theorem exists_bounding_height_tail_comparison
    (p q : unitInterval) (hp : 1 / 2 < (p : ℝ)) (hpq : p ≤ q) (hq1 : (q : ℝ) < 1) :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 0 < N → ∀ (r : List Bool → ℝ) (i : Fin N) (h : ℕ),
      (1 / C) * (1 / (q : ℝ) - 1) ^ h ≤
          pairedUniformLaw.real {w | h ≤ (terminalBoundShape N p q r false w i).height} ∧
      pairedUniformLaw.real {w | h ≤ (terminalBoundShape N p q r false w i).height} ≤
          pairedUniformLaw.real {w | h ≤ (terminalBoundShape N p q r true w i).height} ∧
      pairedUniformLaw.real {w | h ≤ (terminalBoundShape N p q r true w i).height} ≤
          C * (1 / (p : ℝ) - 1) ^ h := by
  obtain ⟨C, hC, htail⟩ := Branching.exists_uniform_tail_comparison hp
    (show (p : ℝ) ≤ (q : ℝ) from hpq) hq1
  refine ⟨C, hC, fun N hN r i h ↦ ?_⟩
  rw [terminalBoundShape_heightTail N hN p q hp hpq r false i h,
    terminalBoundShape_heightTail N hN p q hp hpq r true i h]
  exact htail h

theorem terminalBoundShape_real_threshold (N : ℕ) (p q : ℝ) (r : List Bool → ℝ)
    (upper : Bool) (i : Fin N) (h : ℝ) :
    pairedUniformLaw.real {w | h ≤ ((terminalBoundShape N p q r upper w i).height : ℝ)} =
      pairedUniformLaw.real {w | Nat.ceil h ≤ (terminalBoundShape N p q r upper w i).height} := by
  congr 1
  ext w
  exact (show Nat.ceil h ≤ (terminalBoundShape N p q r upper w i).height ↔
      h ≤ ((terminalBoundShape N p q r upper w i).height : ℝ) from Nat.ceil_le).symm

theorem exists_bounding_real_height_tail_comparison
    (p q : unitInterval) (hp : 1 / 2 < (p : ℝ)) (hpq : p ≤ q) (hq1 : (q : ℝ) < 1) :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 0 < N → ∀ (r : List Bool → ℝ) (i : Fin N) (h : ℝ), 0 ≤ h →
      (1 / C) * (1 / (q : ℝ) - 1) ^ h ≤
          pairedUniformLaw.real {w | h ≤ ((terminalBoundShape N p q r false w i).height : ℝ)} ∧
      pairedUniformLaw.real {w | h ≤ ((terminalBoundShape N p q r false w i).height : ℝ)} ≤
          pairedUniformLaw.real {w | h ≤ ((terminalBoundShape N p q r true w i).height : ℝ)} ∧
      pairedUniformLaw.real {w | h ≤ ((terminalBoundShape N p q r true w i).height : ℝ)} ≤
          C * (1 / (p : ℝ) - 1) ^ h := by
  obtain ⟨C, hC, htail⟩ := exists_bounding_height_tail_comparison p q hp hpq hq1
  have hp0 : 0 < (p : ℝ) := by linarith
  have hpqR : (p : ℝ) ≤ (q : ℝ) := hpq
  have hq0 : 0 < (q : ℝ) := by linarith
  have hp1 : (p : ℝ) < 1 := hpqR.trans_lt hq1
  let mp := 1 / (p : ℝ) - 1
  let mq := 1 / (q : ℝ) - 1
  have hmp0 : 0 < mp := by dsimp [mp]; exact sub_pos.mpr ((one_lt_div hp0).mpr hp1)
  have hmq0 : 0 < mq := by dsimp [mq]; exact sub_pos.mpr ((one_lt_div hq0).mpr hq1)
  have hmp1 : mp ≤ 1 := by
    dsimp [mp]
    have hx : 1 / (p : ℝ) < 2 := (div_lt_iff₀ hp0).mpr (by linarith)
    linarith
  have hmq1 : mq ≤ 1 := by
    dsimp [mq]
    have hx : 1 / (q : ℝ) < 2 := (div_lt_iff₀ hq0).mpr (by linarith)
    linarith
  have hCC : C ≤ C / mq := (le_div_iff₀ hmq0).mpr (mul_le_of_le_one_right hC.le hmq1)
  refine ⟨C / mq, div_pos hC hmq0, fun N hN r i h hh ↦ ?_⟩
  rw [terminalBoundShape_real_threshold, terminalBoundShape_real_threshold]
  obtain ⟨hlo, hmid, hhi⟩ := htail N hN r i (Nat.ceil h)
  have hqpow : mq ^ (h + 1) ≤ mq ^ (Nat.ceil h : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hmq0 hmq1 (Nat.ceil_lt_add_one hh).le
  have hppow : mp ^ (Nat.ceil h : ℝ) ≤ mp ^ h :=
    Real.rpow_le_rpow_of_exponent_ge hmp0 hmp1 (Nat.le_ceil h)
  rw [Real.rpow_natCast] at hqpow hppow
  refine ⟨?_, hmid, ?_⟩
  · calc
      (1 / (C / mq)) * mq ^ h = (1 / C) * mq ^ (h + 1) := by
        rw [Real.rpow_add hmq0, Real.rpow_one]
        field_simp
      _ ≤ (1 / C) * mq ^ (Nat.ceil h) := mul_le_mul_of_nonneg_left hqpow (one_div_nonneg.mpr hC.le)
      _ ≤ _ := hlo
  · calc
      _ ≤ C * mp ^ (Nat.ceil h) := hhi
      _ ≤ C * mp ^ h := mul_le_mul_of_nonneg_left hppow hC.le
      _ ≤ (C / mq) * mp ^ h := mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg hmp0.le h)

end HeightPaper.CountCoupling
