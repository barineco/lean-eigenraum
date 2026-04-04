/-
# DDD ODE Dynamics: properties of the density-driven system

Given C = 1/f (established by MasterTheorem), the DDD ODE system has
provable dynamical properties. These are deductive consequences of
the equation structure, not empirical findings.

## The DDD ODE (simplified 2-mode version for formalization)

  dE₁/dt = -k · (ρ₁ - ρ₂)
  dE₂/dt = +k · (ρ₁ - ρ₂)

where ρ_i = E_i · ω_i, k > 0.

## Reference

https://zenn.dev/barineco/articles/395585d1763549 §2.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Basic

/-! ## Energy conservation (lossless 2-mode system) -/

/-- Total energy conservation: dE₁ + dE₂ = 0. -/
theorem energy_conservation (k ρ₁ ρ₂ : ℝ) :
    let dE₁ := -k * (ρ₁ - ρ₂)
    let dE₂ :=  k * (ρ₁ - ρ₂)
    dE₁ + dE₂ = 0 := by
  simp only
  ring

/-- N-mode energy conservation from pairwise antisymmetric flux.
    Each mode's net flux is Σⱼ J(i,j). The total Σᵢ Σⱼ J(i,j) = 0
    because J(i,j) + J(j,i) = 0 for all i,j (and J(i,i) = 0). -/
theorem energy_conservation_n {n : ℕ} (J : Fin n → Fin n → ℝ)
    (h_antisym : ∀ i j, J i j = -J j i) :
    Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (J i)) = 0 := by
  set S := ∑ i : Fin n, ∑ j : Fin n, J i j
  -- S = Σ_j Σ_i J(i,j)  (swap summation order)
  have h1 : S = ∑ j, ∑ i, J i j := Finset.sum_comm
  -- Σ_i J(i,j) = -Σ_i J(j,i)  (antisymmetry)
  have h2 : ∀ j, (∑ i, J i j) = -(∑ i, J j i) := fun j => by
    rw [show (∑ i, J i j) = ∑ i, -J j i from
      Finset.sum_congr rfl (fun i _ => h_antisym i j), Finset.sum_neg_distrib]
  -- Σ_j Σ_i J(i,j) = -Σ_j Σ_i J(j,i) = -S  (alpha-rename)
  have h3 : (∑ j, ∑ i, J i j) = -S := by
    simp_rw [h2, Finset.sum_neg_distrib]; rfl
  -- S = -S implies S = 0
  linarith

/-! ## Uniqueness of equilibrium -/

/-- Zero flux iff ρ₁ = ρ₂ (unique equilibrium up to total energy). -/
theorem equilibrium_unique_2mode (E₁ E₂ ω₁ ω₂ k : ℝ) (hk : k ≠ 0) :
    -k * (E₁ * ω₁ - E₂ * ω₂) = 0 ↔ E₁ * ω₁ = E₂ * ω₂ := by
  rw [neg_mul, neg_eq_zero, mul_eq_zero]
  constructor
  · intro h; rcases h with h | h
    · exact absurd h hk
    · linarith
  · intro h; right; linarith

/-- At equilibrium E_n = T/omega_n. -/
theorem equilibrium_distribution (E₁ E₂ ω₁ ω₂ T : ℝ)
    (h₁ : E₁ * ω₁ = T) (h₂ : E₂ * ω₂ = T)
    (hω₁ : ω₁ ≠ 0) (hω₂ : ω₂ ≠ 0) :
    E₁ = T / ω₁ ∧ E₂ = T / ω₂ := by
  constructor
  · field_simp at h₁ ⊢; linarith
  · field_simp at h₂ ⊢; linarith

/-! ## Flux direction: energy flows from high density to low density -/

/-- Energy flows down the density gradient: ρ₁ > ρ₂ implies dE₁ < 0. -/
theorem flux_direction (k ρ₁ ρ₂ : ℝ) (hk : 0 < k) (hρ : ρ₁ > ρ₂) :
    -k * (ρ₁ - ρ₂) < 0 := by
  nlinarith

/-- Receiver gains energy: dE₂ > 0. -/
theorem flux_direction_receiver (k ρ₁ ρ₂ : ℝ) (hk : 0 < k) (hρ : ρ₁ > ρ₂) :
    k * (ρ₁ - ρ₂) > 0 := by
  nlinarith

/-! ## Density difference as Lyapunov function (2-mode lossless) -/

/-- Lyapunov algebra: d/dt[(Δρ)²] = -2k(ω₁+ω₂)(Δρ)². -/
theorem lyapunov_algebraic (k ω₁ ω₂ Δρ : ℝ) :
    let dρ₁ := ω₁ * (-k * Δρ)
    let dρ₂ := ω₂ * (k * Δρ)
    let dΔρ := dρ₁ - dρ₂
    2 * Δρ * dΔρ = -2 * k * (ω₁ + ω₂) * Δρ ^ 2 := by
  simp only
  ring

/-- Lyapunov derivative is non-positive for k > 0, ω₁+ω₂ > 0. -/
theorem lyapunov_nonpositive (k ω₁ ω₂ Δρ : ℝ)
    (hk : 0 < k) (hω : 0 < ω₁ + ω₂) :
    -2 * k * (ω₁ + ω₂) * Δρ ^ 2 ≤ 0 := by
  have h1 : 0 ≤ Δρ ^ 2 := sq_nonneg Δρ
  have h2 : 0 < 2 * k * (ω₁ + ω₂) := by positivity
  nlinarith [mul_nonneg (le_of_lt h2) h1]

/-- Lyapunov derivative = 0 iff equilibrium (Δρ = 0). -/
theorem lyapunov_zero_iff_equilibrium (k ω₁ ω₂ Δρ : ℝ)
    (hk : 0 < k) (hω : 0 < ω₁ + ω₂) :
    -2 * k * (ω₁ + ω₂) * Δρ ^ 2 = 0 ↔ Δρ = 0 := by
  constructor
  · intro h
    have h2 : 0 < 2 * k * (ω₁ + ω₂) := by positivity
    have h3 : 2 * k * (ω₁ + ω₂) * Δρ ^ 2 = 0 := by nlinarith
    have h4 : Δρ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h3 with h5 | h5
      · linarith
      · exact h5
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h4
  · intro h; rw [h]; ring

/-! ## Exponential stability of the density difference

The linear ODE dΔρ/dt = -λΔρ (where λ = k(ω₁+ω₂) > 0) has the
exact solution Δρ(t) = Δρ₀ · exp(-λt), which decays to 0. -/

open Real in
/-- Stability bound: |Δρ(t)| ≤ |Δρ₀| for all t ≥ 0 when rate > 0. -/
theorem exponential_decay_bounded (Δρ₀ rate t : ℝ) (hr : 0 < rate) (ht : 0 ≤ t) :
    |Δρ₀ * exp (-rate * t)| ≤ |Δρ₀| := by
  rw [abs_mul, abs_of_pos (exp_pos _)]
  have hexp : exp (-rate * t) ≤ 1 := by
    rw [exp_le_one_iff]
    nlinarith
  exact mul_le_of_le_one_right (abs_nonneg _) hexp

open Real Filter Topology in
/-- Asymptotic stability: Δρ(t) → 0 as t → ∞ for rate > 0. -/
theorem density_difference_decays (Δρ₀ rate : ℝ) (hr : 0 < rate) :
    Tendsto (fun t => Δρ₀ * exp (-rate * t)) atTop (nhds 0) := by
  rw [show (0 : ℝ) = Δρ₀ * 0 from (mul_zero _).symm]
  apply Tendsto.const_mul
  have h1 : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b / rate, fun t ht =>
      calc b = rate * (b / rate) := by rw [mul_div_cancel₀ b (ne_of_gt hr)]
        _ ≤ rate * t := by exact mul_le_mul_of_nonneg_left ht (le_of_lt hr)⟩
  have h2 : Tendsto (fun t : ℝ => -(rate * t)) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp h1
  rw [show (fun t => exp (-rate * t)) = (fun t => exp (-(rate * t))) from by ext; ring_nf]
  exact tendsto_exp_atBot.comp h2

/-! ## High-frequency preferential decay -/

/-- Kelvin-Voigt: γ ~ ω, so higher modes decay faster. -/
theorem kelvin_voigt_ordering (σ₁ ω₁ ω₂ : ℝ) (hσ : 0 < σ₁) (hω : ω₁ < ω₂) :
    4 * Real.pi * σ₁ * ω₁ < 4 * Real.pi * σ₁ * ω₂ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h4ps : 0 < 4 * Real.pi * σ₁ := by positivity
  nlinarith

