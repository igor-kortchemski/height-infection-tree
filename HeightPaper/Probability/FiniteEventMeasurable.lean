module

public import HeightPaper.Probability.FiniteSafeCutoff

/-! # Measurability of arbitrary observables of a finite epidemic event word -/

@[expose] public section

open MeasureTheory Set
open scoped Classical

namespace HeightPaper.CountCoupling

theorem finiteWalk_congr_birth_prefix {l : ℝ} {n H : ℕ} {u v : ℕ → ℝ}
    (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n v i)
    {k : ℕ} (hk : k ≤ H) : finiteWalk l n u k = finiteWalk l n v k := by
  unfold finiteWalk
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [he i ((Finset.mem_range.mp hi).trans_le hk)]

theorem finiteSafeCutoff_congr_birth_prefix {l : ℝ} {n H : ℕ} {u v : ℕ → ℝ}
    (he : ∀ i < H, finiteBirth l n u i = finiteBirth l n v i) :
    finiteSafeCutoff l n H u = finiteSafeCutoff l n H v := by
  unfold finiteSafeCutoff
  congr 1
  ext k
  by_cases hk : k ≤ H
  · simp only [mem_ofPred_eq, hk, true_and, finiteWalk_congr_birth_prefix he hk]
  · simp only [mem_ofPred_eq, hk, false_and]

/-- Every event determined by the first `H` epidemic birth/recovery choices
is measurable, including uncountable suprema over auxiliary parameters. -/
theorem measurableSet_of_finiteBirth_prefix (l : ℝ) (n H : ℕ) {E : Set (ℕ → ℝ)}
    (hE : ∀ u v, (∀ i < H, finiteBirth l n u i = finiteBirth l n v i) →
      (u ∈ E ↔ v ∈ E)) : MeasurableSet E := by
  let f : (ℕ → ℝ) → (Fin H → Bool) := fun u i ↦ finiteBirth l n u i
  have hf : Measurable f := Measurable.of_eval (fun i ↦ measurable_finiteBirth l n i)
  have himage : MeasurableSet (f '' E) := (Set.to_countable _).measurableSet
  have heq : f ⁻¹' (f '' E) = E := by
    ext u
    constructor
    · rintro ⟨v, hv, hvu⟩
      exact (hE v u (fun i hi ↦ congrFun hvu ⟨i, hi⟩)).mp hv
    · intro hu
      exact ⟨u, hu, rfl⟩
  rw [← heq]
  exact hf himage

/-- A finite-word observable may take values in any measurable space. -/
theorem measurable_of_finiteBirth_prefix {α : Type*} [MeasurableSpace α]
    (l : ℝ) (n H : ℕ) {F : (ℕ → ℝ) → α}
    (hF : ∀ u v, (∀ i < H, finiteBirth l n u i = finiteBirth l n v i) → F u = F v) :
    Measurable F := by
  intro E _hE
  apply measurableSet_of_finiteBirth_prefix l n H
  intro u v he
  change F u ∈ E ↔ F v ∈ E
  rw [hF u v he]

end HeightPaper.CountCoupling
