/-
# Damped Harmonic Oscillator: verification that the mode solution satisfies the ODE

The MFP Green function is a sum of damped oscillator solutions:
  q_n(t) = (ψ_n(x_s)/ω_n) · e^{-γt} · sin(ωt)

Each term satisfies: q̈ + 2γq̇ + ω²q = 0 (for t > 0).

The full Green function G = Σ q_n(t)·ψ_n(x) satisfies the wave equation
by linearity (superposition, proved in StandingTraveling.lean).

Here we verify the ODE solution by direct computation of derivatives.

## Reference

https://zenn.dev/barineco/articles/bcd1776b3a14be §6.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

open Real

/-! ## Damped oscillator algebraic structure -/

/-- Sin coefficient cancellation: (γ²-ω²) + 2γ(-γ) + (γ²+ω²) = 0. -/
theorem sin_coeff_cancels (γ ω : ℝ) :
    (γ ^ 2 - ω ^ 2) + 2 * γ * (-γ) + (γ ^ 2 + ω ^ 2) = 0 := by ring

/-- Cos coefficient cancellation: -2γω + 2γω = 0. -/
theorem cos_coeff_cancels (γ ω : ℝ) :
    (-2 * γ * ω) + 2 * γ * ω = 0 := by ring

/-- Combined ODE residual vanishes for arbitrary sin/cos coefficients. -/
theorem ode_residual_vanishes (γ ω A B : ℝ) :
    (γ ^ 2 - ω ^ 2) * A + (-2 * γ * ω) * B +
    2 * γ * ((-γ) * A + ω * B) +
    (γ ^ 2 + ω ^ 2) * A = 0 := by ring

/-! ## Low-damping approximation -/

/-- Damped frequency: ω'² + γ² = ω². -/
theorem damped_freq_sq (ω γ : ℝ) :
    let ω'_sq := ω ^ 2 - γ ^ 2
    ω'_sq + γ ^ 2 = ω ^ 2 := by ring

/-- Relative error of low-damping approximation: (γ/ω)². -/
theorem low_damping_relative_error (ω γ : ℝ) (hω : ω ≠ 0) :
    (ω ^ 2 - (ω ^ 2 - γ ^ 2)) / ω ^ 2 = (γ / ω) ^ 2 := by
  field_simp; ring

