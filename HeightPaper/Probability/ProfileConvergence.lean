module

public import HeightPaper.Probability.ProfileAsymptotics

/-!
# Deterministic logarithmic profile convergence

A differentiable limiting Laplace exponent with strictly increasing derivative
identifies the logarithmic mass of a bin by its lower endpoint. The lower bound
uses narrower bins whose slopes approach that endpoint. This theorem transfers
assumed real Laplace convergence; it does not prove it for the epidemic model.
-/

public section

open Filter Set
open scoped Topology

namespace HeightPaper.Profile

variable {ι : Type*} {α : ι → Type*} {ℓ : Filter ι}

/-- Every exponent below the lower-endpoint Legendre exponent is an eventual
lower bound for the bin, when the limiting Laplace exponent has a continuous,
strictly increasing derivative locally. -/
theorem eventually_exp_le_binMass_of_convex_laplace
    (s : (n : ι) → Finset (α n)) (w d : (n : ι) → α n → ℝ)
    {L : ι → ℝ} (hL : Tendsto L ℓ atTop)
    (hw : ∀ n, ∀ i ∈ s n, 0 ≤ w n i)
    {ψ D : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hder : ∀ t ∈ U, HasDerivAt ψ (D t) t) (hD : StrictMonoOn D U)
    {x B r : ℝ} (hx : 0 ≤ x) (hxU : x ∈ U) (hDc : ContinuousAt D x)
    (hB : D x < B) (hr : r < ψ x - x * D x)
    (hZ : ∀ t ∈ U, ∀ᶠ n in ℓ, 0 < laplaceSum (s n) (w n) (d n) t)
    (hLap : ∀ t ∈ U, Tendsto
      (fun n ↦ Real.log (laplaceSum (s n) (w n) (d n) t) / L n) ℓ (𝓝 (ψ t))) :
    ∀ᶠ n in ℓ, Real.exp (r * L n) ≤
      binMass (s n) (w n) (d n) (D x * L n) (B * L n) := by
  have hshift : Tendsto (fun δ : ℝ ↦ x + δ) (𝓝 0) (𝓝 x) := by
    simpa only [add_zero, id_eq] using
      (tendsto_const_nhds.add (tendsto_id : Tendsto (fun δ : ℝ ↦ δ) (𝓝 0) (𝓝 0)))
  have hDlim : Tendsto (fun δ : ℝ ↦ D (x + δ)) (𝓝 0) (𝓝 (D x)) :=
    hDc.tendsto.comp hshift
  have hblim : Tendsto (fun δ : ℝ ↦ D (x + δ) + δ) (𝓝 0) (𝓝 (D x)) := by
    simpa only [add_zero, id_eq] using hDlim.add tendsto_id
  have hψlim : Tendsto (fun δ : ℝ ↦ ψ (x + δ)) (𝓝 0) (𝓝 (ψ x)) :=
    (hder x hxU).continuousAt.tendsto.comp hshift
  have hrlim : Tendsto (fun δ : ℝ ↦ ψ (x + δ) - (x + δ) * (D (x + δ) + δ))
      (𝓝 0) (𝓝 (ψ x - x * D x)) := hψlim.sub (hshift.mul hblim)
  have hevent : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ x + δ ∈ U ∧
      D (x + δ) + δ < B ∧ r < ψ (x + δ) - (x + δ) * (D (x + δ) + δ) := by
    filter_upwards [self_mem_nhdsWithin,
      (hshift.eventually (hU.mem_nhds hxU)).filter_mono nhdsWithin_le_nhds,
      (hblim.eventually_lt_const hB).filter_mono nhdsWithin_le_nhds,
      (hrlim.eventually_const_lt hr).filter_mono nhdsWithin_le_nhds] with δ hδ hδU hb hr'
    exact ⟨hδ, hδU, hb, hr'⟩
  obtain ⟨δ, hδ, htU, hb, hr'⟩ := hevent.exists
  have hDlt : D x < D (x + δ) := hD hxU htU (by linarith)
  obtain ⟨ε, hε, htm, htp, hm, hp⟩ := exists_nearby_laplace_gaps
    (hder (x + δ) htU) hDlt (show D (x + δ) < D (x + δ) + δ by linarith) hU htU
  exact eventually_exp_le_binMass_of_log_laplace s w d hL hw
    (show 0 ≤ x + δ by linarith) hε.le le_rfl hb.le hm hp hr'
    (hZ _ htU) (hZ _ htm) (hZ _ htp) (hLap _ htU) (hLap _ htm) (hLap _ htp)

/-- Local logarithmic Laplace limits determine the logarithmic bin mass. The
bin is eventually positive, so its logarithm is never justified by `log 0`. -/
theorem log_binMass_convergence_of_laplace
    (s : (n : ι) → Finset (α n)) (w d : (n : ι) → α n → ℝ)
    {L : ι → ℝ} (hL : Tendsto L ℓ atTop)
    (hw : ∀ n, ∀ i ∈ s n, 0 ≤ w n i)
    {ψ D : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hder : ∀ t ∈ U, HasDerivAt ψ (D t) t) (hD : StrictMonoOn D U)
    {x B : ℝ} (hx : 0 ≤ x) (hxU : x ∈ U) (hDc : ContinuousAt D x) (hB : D x < B)
    (hZ : ∀ t ∈ U, ∀ᶠ n in ℓ, 0 < laplaceSum (s n) (w n) (d n) t)
    (hLap : ∀ t ∈ U, Tendsto
      (fun n ↦ Real.log (laplaceSum (s n) (w n) (d n) t) / L n) ℓ (𝓝 (ψ t))) :
    (∀ᶠ n in ℓ, 0 < binMass (s n) (w n) (d n) (D x * L n) (B * L n)) ∧
    Tendsto (fun n ↦ Real.log (binMass (s n) (w n) (d n) (D x * L n) (B * L n)) / L n)
      ℓ (𝓝 (ψ x - x * D x)) := by
  let c := ψ x - x * D x
  have hlower : ∀ r < c, ∀ᶠ n in ℓ, Real.exp (r * L n) ≤
      binMass (s n) (w n) (d n) (D x * L n) (B * L n) := by
    intro r hr
    exact eventually_exp_le_binMass_of_convex_laplace s w d hL hw hU hder hD
      hx hxU hDc hB hr hZ hLap
  have hupper : ∀ r > c, ∀ᶠ n in ℓ,
      binMass (s n) (w n) (d n) (D x * L n) (B * L n) ≤ Real.exp (r * L n) := by
    intro r hr
    exact eventually_binMass_le_exp_of_log_laplace s w d hL hw hx hr (hZ x hxU) (hLap x hxU)
  have hlbase := hlower (c - 1) (by linarith)
  have hubase := hupper (c + 1) (by linarith)
  constructor
  · exact hlbase.mono fun n hn ↦ (Real.exp_pos _).trans_le hn
  · apply tendsto_order.mpr
    constructor
    · intro r hr
      obtain ⟨q, hrq, hqc⟩ := exists_between hr
      have hh := eventually_log_bounds_of_exp_bounds hL (hlower q hqc) hubase
      exact hh.mono fun _ hn ↦ hrq.trans_le hn.2.1
    · intro r hr
      obtain ⟨q, hcq, hqr⟩ := exists_between hr
      have hh := eventually_log_bounds_of_exp_bounds hL hlbase (hupper q hcq)
      exact hh.mono fun _ hn ↦ hn.2.2.trans_lt hqr

/-- The paper's exponential Laplace exponent yields its weak logarithmic
profile exponent, assuming the Laplace limits on an open neighborhood. -/
theorem log_binMass_convergence_of_exponential_laplace
    (s : (n : ι) → Finset (α n)) (w d : (n : ι) → α n → ℝ)
    {L : ι → ℝ} (hL : Tendsto L ℓ atTop)
    (hw : ∀ n, ∀ i ∈ s n, 0 ≤ w n i)
    {c γ x B : ℝ} (hγ : 0 < γ) (hx : 0 ≤ x) (hB : γ * Real.exp x < B)
    {U : Set ℝ} (hU : IsOpen U) (hxU : x ∈ U)
    (hZ : ∀ t ∈ U, ∀ᶠ n in ℓ, 0 < laplaceSum (s n) (w n) (d n) t)
    (hLap : ∀ t ∈ U, Tendsto
      (fun n ↦ Real.log (laplaceSum (s n) (w n) (d n) t) / L n)
      ℓ (𝓝 (c + γ * (Real.exp t - 1)))) :
    (∀ᶠ n in ℓ, 0 < binMass (s n) (w n) (d n) (γ * Real.exp x * L n) (B * L n)) ∧
    Tendsto (fun n ↦ Real.log (binMass (s n) (w n) (d n)
      (γ * Real.exp x * L n) (B * L n)) / L n)
      ℓ (𝓝 (c + γ * (Real.exp x - 1 - x * Real.exp x))) := by
  have hd : ∀ t ∈ U, HasDerivAt (fun u : ℝ ↦ c + γ * (Real.exp u - 1))
      (γ * Real.exp t) t := by
    intro t _
    convert (((Real.hasDerivAt_exp t).sub_const 1).const_mul γ).const_add c using 1
  have hm : StrictMonoOn (fun t : ℝ ↦ γ * Real.exp t) U := by
    intro t _ u _ htu
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr htu) hγ
  have hc : ContinuousAt (fun t : ℝ ↦ γ * Real.exp t) x :=
    (continuous_const.mul Real.continuous_exp).continuousAt
  convert log_binMass_convergence_of_laplace s w d hL hw hU hd hm hx hxU hc hB hZ hLap using 2
  congr 1
  ring

/-- A logarithmic Laplace limit gives every strictly larger tail exponent,
without requiring a finite upper endpoint. -/
theorem eventually_tailMass_le_exp_of_log_laplace
    (s : (n : ι) → Finset (α n)) (w d : (n : ι) → α n → ℝ)
    {L : ι → ℝ} (hL : Tendsto L ℓ atTop)
    (hw : ∀ n, ∀ i ∈ s n, 0 ≤ w n i)
    {t A c r : ℝ} (ht : 0 ≤ t) (hr : c - t * A < r)
    (hZ : ∀ᶠ n in ℓ, 0 < laplaceSum (s n) (w n) (d n) t)
    (hc : Tendsto (fun n ↦ Real.log (laplaceSum (s n) (w n) (d n) t) / L n) ℓ (𝓝 c)) :
    ∀ᶠ n in ℓ, tailMass (s n) (w n) (d n) (A * L n) ≤ Real.exp (r * L n) := by
  have he := eventually_exp_bounds_of_log_tendsto hL hZ hc
    (show c - 1 < c by linarith) (show c < r + t * A by linarith)
  filter_upwards [he] with n hn
  calc
    _ ≤ Real.exp (-t * (A * L n)) * laplaceSum (s n) (w n) (d n) t :=
      tailMass_le_exp_neg_mul_laplaceSum _ _ _ ht _ (hw n)
    _ ≤ Real.exp (-t * (A * L n)) * Real.exp ((r + t * A) * L n) :=
      mul_le_mul_of_nonneg_left hn.2 (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Local logarithmic Laplace limits also identify the mass above a lower
endpoint, with no upper cutoff. A fixed finite bin supplies the lower bound. -/
theorem log_tailMass_convergence_of_laplace
    (s : (n : ι) → Finset (α n)) (w d : (n : ι) → α n → ℝ)
    {L : ι → ℝ} (hL : Tendsto L ℓ atTop)
    (hw : ∀ n, ∀ i ∈ s n, 0 ≤ w n i)
    {ψ D : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hder : ∀ t ∈ U, HasDerivAt ψ (D t) t) (hD : StrictMonoOn D U)
    {x : ℝ} (hx : 0 ≤ x) (hxU : x ∈ U) (hDc : ContinuousAt D x)
    (hZ : ∀ t ∈ U, ∀ᶠ n in ℓ, 0 < laplaceSum (s n) (w n) (d n) t)
    (hLap : ∀ t ∈ U, Tendsto
      (fun n ↦ Real.log (laplaceSum (s n) (w n) (d n) t) / L n) ℓ (𝓝 (ψ t))) :
    (∀ᶠ n in ℓ, 0 < tailMass (s n) (w n) (d n) (D x * L n)) ∧
    Tendsto (fun n ↦ Real.log (tailMass (s n) (w n) (d n) (D x * L n)) / L n)
      ℓ (𝓝 (ψ x - x * D x)) := by
  let c := ψ x - x * D x
  have hlower : ∀ r < c, ∀ᶠ n in ℓ, Real.exp (r * L n) ≤
      tailMass (s n) (w n) (d n) (D x * L n) := by
    intro r hr
    have hb := eventually_exp_le_binMass_of_convex_laplace s w d hL hw hU hder hD
      hx hxU hDc (show D x < D x + 1 by linarith) hr hZ hLap
    exact hb.mono fun n hn ↦ hn.trans (binMass_le_tailMass _ _ _ _ _ (hw n))
  have hupper : ∀ r > c, ∀ᶠ n in ℓ,
      tailMass (s n) (w n) (d n) (D x * L n) ≤ Real.exp (r * L n) := by
    intro r hr
    exact eventually_tailMass_le_exp_of_log_laplace s w d hL hw hx hr (hZ x hxU) (hLap x hxU)
  have hlbase := hlower (c - 1) (by linarith)
  have hubase := hupper (c + 1) (by linarith)
  constructor
  · exact hlbase.mono fun n hn ↦ (Real.exp_pos _).trans_le hn
  · apply tendsto_order.mpr
    constructor
    · intro r hr
      obtain ⟨q, hrq, hqc⟩ := exists_between hr
      have hh := eventually_log_bounds_of_exp_bounds hL (hlower q hqc) hubase
      exact hh.mono fun _ hn ↦ hrq.trans_le hn.2.1
    · intro r hr
      obtain ⟨q, hcq, hqr⟩ := exists_between hr
      have hh := eventually_log_bounds_of_exp_bounds hL hlbase (hupper q hcq)
      exact hh.mono fun _ hn ↦ hn.2.2.trans_lt hqr

/-- The infinite-upper-endpoint case of the deterministic weak profile bridge
for the paper's exponential Laplace rate. -/
theorem log_tailMass_convergence_of_exponential_laplace
    (s : (n : ι) → Finset (α n)) (w d : (n : ι) → α n → ℝ)
    {L : ι → ℝ} (hL : Tendsto L ℓ atTop)
    (hw : ∀ n, ∀ i ∈ s n, 0 ≤ w n i)
    {c γ x : ℝ} (hγ : 0 < γ) (hx : 0 ≤ x)
    {U : Set ℝ} (hU : IsOpen U) (hxU : x ∈ U)
    (hZ : ∀ t ∈ U, ∀ᶠ n in ℓ, 0 < laplaceSum (s n) (w n) (d n) t)
    (hLap : ∀ t ∈ U, Tendsto
      (fun n ↦ Real.log (laplaceSum (s n) (w n) (d n) t) / L n)
      ℓ (𝓝 (c + γ * (Real.exp t - 1)))) :
    (∀ᶠ n in ℓ, 0 < tailMass (s n) (w n) (d n) (γ * Real.exp x * L n)) ∧
    Tendsto (fun n ↦ Real.log (tailMass (s n) (w n) (d n) (γ * Real.exp x * L n)) / L n)
      ℓ (𝓝 (c + γ * (Real.exp x - 1 - x * Real.exp x))) := by
  have hd : ∀ t ∈ U, HasDerivAt (fun u : ℝ ↦ c + γ * (Real.exp u - 1))
      (γ * Real.exp t) t := by
    intro t _
    convert (((Real.hasDerivAt_exp t).sub_const 1).const_mul γ).const_add c using 1
  have hm : StrictMonoOn (fun t : ℝ ↦ γ * Real.exp t) U := by
    intro t _ u _ htu
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr htu) hγ
  have hc : ContinuousAt (fun t : ℝ ↦ γ * Real.exp t) x :=
    (continuous_const.mul Real.continuous_exp).continuousAt
  convert log_tailMass_convergence_of_laplace s w d hL hw hU hd hm hx hxU hc hZ hLap using 2
  congr 1
  ring

end HeightPaper.Profile
