/-
# Algebraic Identities

Structural identities that follow from the definition ρ = E · f (C = 1/f).
-/

import Mathlib.Tactic

/-! ## k_eff = γ / f identity -/

/-- The fundamental identity: γ · E = (γ/f) · (E · f) = k_eff · ρ. -/
theorem k_eff_identity (E γ f : ℝ) (hf : f ≠ 0) :
    γ * E = (γ / f) * (E * f) := by
  field_simp

/-- k_int = 4π σ₁ for Kelvin-Voigt loss γ = 4πσ₁f. -/
theorem k_int_constant (σ₁ f : ℝ) (hf : f ≠ 0) :
    (4 * Real.pi * σ₁ * f) / f = 4 * Real.pi * σ₁ := by
  field_simp

/-! ## Structural 1/f separation -/

/-- β_k = β_γ - 1: the structural -1 comes from C = 1/f. -/
theorem structural_1f_decomposition (β_γ : ℝ) :
    β_γ - 1 = β_γ + (-1) := by ring
