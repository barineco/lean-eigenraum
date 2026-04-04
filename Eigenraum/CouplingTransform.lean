/-
# Coupling Transform: from modal loss rates to density-driven couplings

This file upgrades `k = γ / f` from a single algebraic identity to a
small calculus for transforming modal loss laws into density-driven
coupling laws.
-/

import Eigenraum.AlgebraicIdentities
import Mathlib.Tactic

noncomputable section

/-! ## General transform -/

/-- The density-driven coupling induced by a modal loss rate. -/
def k_of_gamma (gamma f : ℝ) : ℝ := gamma / f

/-- γE = kρ via k = γ/f. -/
theorem k_of_gamma_identity (E gamma f : ℝ) (hf : f ≠ 0) :
    gamma * E = k_of_gamma gamma f * (E * f) := by
  unfold k_of_gamma
  exact k_eff_identity E gamma f hf

/-- Additivity: k(γ₁+γ₂) = k(γ₁) + k(γ₂). -/
theorem k_of_gamma_additive (gamma1 gamma2 f : ℝ) (hf : f ≠ 0) :
    k_of_gamma (gamma1 + gamma2) f = k_of_gamma gamma1 f + k_of_gamma gamma2 f := by
  unfold k_of_gamma
  field_simp [hf]

/-- γ = πf/Q gives k = π/Q. -/
theorem k_of_quality_factor (Q f : ℝ) (hQ : Q ≠ 0) (hf : f ≠ 0) :
    k_of_gamma (Real.pi * f / Q) f = Real.pi / Q := by
  unfold k_of_gamma
  field_simp [hQ, hf]

/-! ## Power-law family -/

/-- k = const iff alpha = 1. -/
theorem powerlaw_constant_iff_alpha_eq_one (alpha : ℝ) :
    alpha - 1 = 0 ↔ alpha = 1 := by
  constructor <;> intro h <;> linarith

/-! ## Named special cases -/

/-- Velocity-proportional damping: k = 2σ/f. -/
theorem velocity_proportional_k (sigma f : ℝ) :
    k_of_gamma (2 * sigma) f = (2 * sigma) / f := by
  unfold k_of_gamma
  rfl

/-- Kelvin-Voigt: γ = 4πσf gives k = 4πσ (constant). -/
theorem kelvin_voigt_gives_constant_k (sigma f : ℝ) (hf : f ≠ 0) :
    k_of_gamma (4 * Real.pi * sigma * f) f = 4 * Real.pi * sigma := by
  unfold k_of_gamma
  field_simp [hf]

/-- γ ~ f gives constant k. -/
theorem linear_in_frequency_gives_constant_k (gamma0 f fref : ℝ)
    (hf : f ≠ 0) (href : fref ≠ 0) :
    k_of_gamma (gamma0 * f / fref) f = gamma0 / fref := by
  unfold k_of_gamma
  field_simp [hf, href]
