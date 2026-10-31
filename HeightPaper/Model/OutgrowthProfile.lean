module

public import HeightPaper.Model.Outgrowth
public import HeightPaper.Model.NormalizedProfile

/-!
# Exact profile decomposition over disjoint fresh outgrowths

The normalized identity includes each component's active-population fraction.
The cutoff roots can be ancestor and descendant: the first-old-ancestor
partition, rather than overlapping full descendant sets, is used throughout.
-/

@[expose] public section

open scoped BigOperators

namespace HeightPaper.Model

noncomputable def outgrowthActive (s : State) (cutoff : ℕ) (hc : 0 < cutoff)
    (r : Fin s.vertices) : Finset (Fin s.vertices) :=
  s.active.filter (fun v ↦ Tree.attachmentRoot s.tree cutoff hc v = r)

noncomputable def outgrowthActiveWeight (w : ℂ) (s : State) (cutoff : ℕ)
    (hc : 0 < cutoff) (r : Fin s.vertices) : ℂ :=
  ∑ v ∈ outgrowthActive s cutoff hc r, w ^ Tree.freshDepth s.tree cutoff hc v

noncomputable def normalizedOutgrowthActiveWeight (w : ℂ) (s : State) (cutoff : ℕ)
    (hc : 0 < cutoff) (r : Fin s.vertices) : ℂ :=
  outgrowthActiveWeight w s cutoff hc r / (outgrowthActive s cutoff hc r).card

theorem activeWeight_eq_sum_outgrowth (w : ℂ) (s : State) (cutoff : ℕ)
    (hc : 0 < cutoff) :
    activeWeight w s = ∑ r : Fin s.vertices,
      w ^ s.tree.depth r * outgrowthActiveWeight w s cutoff hc r := by
  unfold outgrowthActiveWeight outgrowthActive
  simp_rw [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← pow_add, Tree.depth_eq_root_add_freshDepth s.tree cutoff hc v]

theorem card_mul_normalizedOutgrowthActiveWeight (w : ℂ) (s : State)
    (cutoff : ℕ) (hc : 0 < cutoff) (r : Fin s.vertices) :
    ((outgrowthActive s cutoff hc r).card : ℂ) *
      normalizedOutgrowthActiveWeight w s cutoff hc r = outgrowthActiveWeight w s cutoff hc r := by
  by_cases hz : (outgrowthActive s cutoff hc r).card = 0
  · have he := Finset.card_eq_zero.mp hz
    simp [normalizedOutgrowthActiveWeight, outgrowthActiveWeight, he]
  · unfold normalizedOutgrowthActiveWeight
    have hC : ((outgrowthActive s cutoff hc r).card : ℂ) ≠ 0 := by exact_mod_cast hz
    exact mul_div_cancel₀ _ hC

/-- Population fractions are essential because both the global and component
profiles are normalized by their own numbers of active vertices. -/
theorem normalizedActiveWeight_eq_sum_outgrowth (w : ℂ) (s : State)
    (cutoff : ℕ) (hc : 0 < cutoff) :
    normalizedActiveWeight w s = ∑ r : Fin s.vertices,
      (((outgrowthActive s cutoff hc r).card : ℂ) / (infectious s : ℂ)) *
        w ^ s.tree.depth r * normalizedOutgrowthActiveWeight w s cutoff hc r := by
  rw [normalizedActiveWeight, activeWeight_eq_sum_outgrowth w s cutoff hc, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  rw [← card_mul_normalizedOutgrowthActiveWeight w s cutoff hc r]
  ring

/-- Corrected martingale decomposition, retaining population fractions and
the weight raised to the root depth. Set `w = exp z` for the paper's formula. -/
theorem shiftedProfile_eq_sum_outgrowth (w C : ℂ) (s : State) (cutoff : ℕ)
    (hc : 0 < cutoff) (D : Fin s.vertices → ℂ) (hD : ∀ r, D r ≠ 0) :
    normalizedActiveWeight w s / C = ∑ r : Fin s.vertices,
      (((outgrowthActive s cutoff hc r).card : ℂ) / (infectious s : ℂ)) *
        w ^ s.tree.depth r * (D r / C) *
          (normalizedOutgrowthActiveWeight w s cutoff hc r / D r) := by
  rw [normalizedActiveWeight_eq_sum_outgrowth w s cutoff hc, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  field_simp [hD r]

end HeightPaper.Model
