/-
# MFP-DDD Consistency: the two descriptions agree

MFP retains phase: q_n(t) = A·e^{-γt}·sin(ωt)
DDD discards phase: tracks E_n(t) only

Proves consistency at three levels:
1. Energy decay rate (single mode)
2. Conservation law (multi-mode, LCAM completeness)
3. Equilibrium preservation
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Real

/-! ## 1. Energy integrand decomposition -/

/-- Energy integrand = DC part + oscillating part. -/
theorem energy_integrand_decomposition (γ ω θ : ℝ) :
    (γ ^ 2 + ω ^ 2) * sin θ ^ 2 - 2 * γ * ω * sin θ * cos θ + ω ^ 2 * cos θ ^ 2 =
    (ω ^ 2 + γ ^ 2 / 2) +
    (-(γ ^ 2 / 2) * cos (2 * θ) - γ * ω * sin (2 * θ)) := by
  rw [sin_two_mul, cos_two_mul]
  nlinarith [sin_sq_add_cos_sq θ, sq_nonneg (sin θ), sq_nonneg (cos θ)]

/-- DC part omega^2 + gamma^2/2 > 0 for omega > 0. -/
theorem phase_average_positive (γ ω : ℝ) (hω : 0 < ω) :
    0 < ω ^ 2 + γ ^ 2 / 2 := by
  nlinarith [sq_nonneg γ]

/-! ## 2. LCAM energy conservation via completeness -/

/-- LCAM energy interchange: site total = hybrid total via completeness. -/
theorem lcam_energy_interchange {N M : ℕ}
    (c_sq : Fin M → Fin N → ℝ)
    (E_α : Fin M → ℝ)
    (h_complete : ∀ α, Finset.sum Finset.univ (fun n => c_sq α n) = 1) :
    Finset.sum Finset.univ (fun n =>
      Finset.sum Finset.univ (fun α => c_sq α n * E_α α)) =
    Finset.sum Finset.univ (fun α => E_α α) := by
  rw [Finset.sum_comm]
  congr 1; ext α
  simp_rw [mul_comm (c_sq α _) (E_α α)]
  rw [← Finset.mul_sum, h_complete α, mul_one]

/-! ## 3. Equilibrium preservation under uniform decay -/

/-- Uniform decay preserves energy ratios. -/
theorem mfp_ratio_preserved (E₁₀ E₂₀ γ t : ℝ)
    (hexp : exp (-2 * γ * t) ≠ 0) :
    (E₁₀ * exp (-2 * γ * t)) / (E₂₀ * exp (-2 * γ * t)) =
    E₁₀ / E₂₀ := by
  rw [mul_div_mul_right _ _ hexp]

/-- DDD equilibrium preserved by MFP decay (common e^{-2gamma t} factor). -/
theorem ddd_equilibrium_preserved_by_mfp (E₀ ω T γ t : ℝ)
    (h_eq : E₀ * ω = T) :
    (E₀ * exp (-2 * γ * t)) * ω = T * exp (-2 * γ * t) := by
  have : E₀ * exp (-2 * γ * t) * ω = E₀ * ω * exp (-2 * γ * t) := by ring
  rw [this, h_eq]

/-! ## 4. The phase-averaging bridge

The MFP energy integrand, when integrated over one phase cycle,
yields exactly 2π · (ω² + γ²/2). The phase average (divide by 2π)
is therefore ω² + γ²/2, which is the DDD energy per mode.

This theorem takes the period integral values as hypotheses;
PhaseAveraging.lean proves those values, and EquivalenceFramework.lean
connects the two to close the bridge without circular imports. -/

/-- Phase-averaged MFP energy = DDD energy, given period integral values.
    The hypotheses are proved by PhaseAveraging.integral_{sin_sq,cos_sq,sin_mul_cos}_period. -/
theorem ddd_is_phase_average_of_mfp (γ ω I_ss I_cc I_sc : ℝ)
    (h_ss : I_ss = π) (h_cc : I_cc = π) (h_sc : I_sc = 0) :
    (1 / (2 * π)) *
      ((γ ^ 2 + ω ^ 2) * I_ss - 2 * γ * ω * I_sc + ω ^ 2 * I_cc) =
    ω ^ 2 + γ ^ 2 / 2 := by
  subst h_ss; subst h_cc; subst h_sc; field_simp; ring
