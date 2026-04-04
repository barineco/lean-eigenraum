/-
# Nonlinear Capacity: C^NL = 1/[f(1+βE)]
-/

import Mathlib.Tactic

noncomputable section

def ρ_NL (E ω₀ β : ℝ) : ℝ := E * ω₀ * (1 + β * E)

/-- Zero-flux condition: equal nonlinear densities. -/
theorem zero_flux_NL (En Em ω₀n ω₀m β : ℝ) :
    ρ_NL En ω₀n β = ρ_NL Em ω₀m β ↔
    En * ω₀n * (1 + β * En) = Em * ω₀m * (1 + β * Em) := by
  unfold ρ_NL; exact Iff.rfl

/-- Harmonic limit: β = 0 recovers ρ = E·ω₀. -/
theorem harmonic_limit (E ω₀ : ℝ) :
    ρ_NL E ω₀ 0 = E * ω₀ := by
  unfold ρ_NL; ring

/-- Hardening (β > 0): nonlinear density exceeds linear density. -/
theorem hardening_increases_density (E ω₀ β : ℝ)
    (hE : 0 < E) (hω : 0 < ω₀) (hβ : 0 < β) :
    ρ_NL E ω₀ 0 < ρ_NL E ω₀ β := by
  unfold ρ_NL; nlinarith [mul_pos hE hω, mul_pos hβ hE]

/-- n⁴ cancellation: α_n/ω_n⁴ is mode-independent for strings. -/
theorem n4_cancellation (α₁ ω₁ : ℝ) (n : ℝ) (hn : n ≠ 0) (hω : ω₁ ≠ 0) :
    (α₁ * n ^ 4) / (ω₁ * n) ^ 4 = α₁ / ω₁ ^ 4 := by
  field_simp

end
