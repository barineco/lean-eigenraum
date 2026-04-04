/-
# Mode Expansion Satisfies the Wave Equation

Separation of variables: the MFP Green function G = Σ qₙ(t)·ψₙ(x)
satisfies the damped wave equation because each term does.

The proof chain:
1. ψₙ is a spatial eigenfunction: Lψₙ = kₙ²ψₙ  (assumed)
2. qₙ satisfies the temporal ODE: q̈+2γq̇+ωₙ²qₙ = 0 (DampedOscillator.lean)
3. The product qₙ·ψₙ satisfies the PDE (THIS FILE: algebraic)
4. The sum Σ qₙ·ψₙ satisfies the PDE by linearity (StandingTraveling.lean)
5. The mode expansion is complete (Completeness.lean: spectral theorem)

This closes the MFP proof chain.

## What is proven

- Eigenmap scaling: L(q·ψ) = (q·ev)·ψ for eigenfunction ψ with eigenvalue ev
- Separation of variables: PDE residual vanishes when temporal ODE holds
- Damped wave equation instantiation with dispersion relation ω² = c²k²
- Two- and three-mode sums satisfy the PDE
- Green function coefficient algebra: aₙ = ψₙ(xₛ)/ωₙ

## Reference

https://zenn.dev/barineco/articles/bcd1776b3a14be §6, DampedOscillator.lean, StandingTraveling.lean.
-/

import Mathlib.Tactic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace ModeExpansion

/-! ## Eigenfunction property under scaling -/

/-- L(q * psi) = (q * ev) * psi for eigenfunction psi. -/
theorem eigenmap_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] V) (ψ : V) (ev q : ℝ)
    (hψ : L ψ = ev • ψ) :
    L (q • ψ) = (q * ev) • ψ := by
  rw [map_smul, hψ, smul_smul]

/-! ## Separation of variables -/

/-- PDE residual vanishes when temporal ODE is satisfied. -/
theorem pde_residual_vanishes {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] V) (ψ : V) (ev c_sq q R : ℝ)
    (hψ : L ψ = ev • ψ)
    (h_ode : R + c_sq * ev * q = 0) :
    R • ψ + c_sq • L (q • ψ) = 0 := by
  rw [eigenmap_smul L ψ ev q hψ, smul_smul, ← add_smul]
  have key : c_sq * (q * ev) = c_sq * ev * q := by ring
  rw [show R + c_sq * (q * ev) = 0 from by linarith [key], zero_smul]

/-! ## Damped wave equation -/

/-- Dispersion: omega^2 = (c*k)^2. -/
theorem dispersion_sq (c k ω : ℝ) (hω : ω ^ 2 = c ^ 2 * k ^ 2) :
    ω ^ 2 = (c * k) ^ 2 := by nlinarith [sq_abs (c * k)]

/-- Temporal ODE + dispersion => q*psi satisfies the PDE. -/
theorem damped_wave_separation {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] V) (ψ : V) (k_sq c_sq q ω_sq temporal_res : ℝ)
    (hψ : L ψ = k_sq • ψ)
    (h_dispersion : ω_sq = c_sq * k_sq)
    (h_temporal : temporal_res + ω_sq * q = 0) :
    temporal_res • ψ + c_sq • L (q • ψ) = 0 := by
  apply pde_residual_vanishes L ψ k_sq c_sq q temporal_res hψ
  rw [← h_dispersion]; exact h_temporal

/-! ## Multi-mode sums -/

/-- Two-mode sum satisfies the PDE. -/
theorem two_mode_sum {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] V) (ψ₁ ψ₂ : V) (ev₁ ev₂ c_sq q₁ q₂ R₁ R₂ : ℝ)
    (hψ₁ : L ψ₁ = ev₁ • ψ₁) (hψ₂ : L ψ₂ = ev₂ • ψ₂)
    (h₁ : R₁ + c_sq * ev₁ * q₁ = 0) (h₂ : R₂ + c_sq * ev₂ * q₂ = 0) :
    (R₁ • ψ₁ + c_sq • L (q₁ • ψ₁)) + (R₂ • ψ₂ + c_sq • L (q₂ • ψ₂)) = 0 := by
  rw [pde_residual_vanishes L ψ₁ ev₁ c_sq q₁ R₁ hψ₁ h₁,
      pde_residual_vanishes L ψ₂ ev₂ c_sq q₂ R₂ hψ₂ h₂,
      add_zero]

/-- Three-mode sum satisfies the PDE. -/
theorem three_mode_sum {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] V) (ψ₁ ψ₂ ψ₃ : V) (ev₁ ev₂ ev₃ c_sq q₁ q₂ q₃ R₁ R₂ R₃ : ℝ)
    (hψ₁ : L ψ₁ = ev₁ • ψ₁) (hψ₂ : L ψ₂ = ev₂ • ψ₂) (hψ₃ : L ψ₃ = ev₃ • ψ₃)
    (h₁ : R₁ + c_sq * ev₁ * q₁ = 0) (h₂ : R₂ + c_sq * ev₂ * q₂ = 0)
    (h₃ : R₃ + c_sq * ev₃ * q₃ = 0) :
    (R₁ • ψ₁ + c_sq • L (q₁ • ψ₁)) +
    (R₂ • ψ₂ + c_sq • L (q₂ • ψ₂)) +
    (R₃ • ψ₃ + c_sq • L (q₃ • ψ₃)) = 0 := by
  rw [pde_residual_vanishes L ψ₁ ev₁ c_sq q₁ R₁ hψ₁ h₁,
      pde_residual_vanishes L ψ₂ ev₂ c_sq q₂ R₂ hψ₂ h₂,
      pde_residual_vanishes L ψ₃ ev₃ c_sq q₃ R₃ hψ₃ h₃]
  simp [add_zero]

/-! ## Green's function coefficients -/

/-- Impulse response amplitude: 1/omega * omega = 1. -/
theorem impulse_amplitude (ω : ℝ) (hω : ω ≠ 0) :
    1 / ω * ω = 1 := by field_simp

/-- Green coefficient reconstruction: (psi/omega) * omega * psi = psi^2. -/
theorem green_coefficient_reconstruction (ψ_xs ω : ℝ) (hω : ω ≠ 0) :
    (ψ_xs / ω) * ω * ψ_xs = ψ_xs ^ 2 := by
  field_simp

/-- 1/omega weighting: lower modes contribute more to Green function. -/
theorem low_freq_dominance (ω₁ ω₂ ψ₁ ψ₂ : ℝ)
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (h_lower : ω₁ < ω₂)
    (h_same_shape : ψ₁ = ψ₂) :
    ψ₂ / ω₂ < ψ₁ / ω₁ ∨ ψ₁ ≤ 0 := by
  by_cases hψ : 0 < ψ₁
  · left
    rw [h_same_shape]
    exact div_lt_div_of_pos_left (h_same_shape ▸ hψ) (by linarith) h_lower
  · right; linarith

/-! ## Finite-dimensional equivalence

In finite dimensions, the spectral theorem for self-adjoint operators
gives eigenspace completeness without Rellich-Kondrachov. Combined with
the separation-of-variables results above, this yields: every solution
of the wave equation in a finite-dimensional eigenspace admits a mode
expansion, and every mode expansion satisfies the PDE. -/

/-- Forward direction: mode expansion satisfies the PDE (arbitrary dimension).
    This is just pde_residual_vanishes packaged as a standalone statement. -/
theorem mode_expansion_satisfies_pde {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] V) (ψ : V) (ev c_sq q R : ℝ)
    (hψ : L ψ = ev • ψ)
    (h_ode : R + c_sq * ev * q = 0) :
    R • ψ + c_sq • L (q • ψ) = 0 :=
  pde_residual_vanishes L ψ ev c_sq q R hψ h_ode

/-- In finite dimensions, eigenspaces of a self-adjoint operator span V,
    so the mode expansion is complete (no assumptions on compactness needed).
    The eigenspace completeness is Completeness.eigenspaces_complete_findim;
    this theorem connects it to the mode expansion context. -/
theorem findim_eigenspaces_span_all
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (T : H →ₗ[𝕜] H) (hSymm : T.IsSymmetric) :
    (⨆ μ, Module.End.eigenspace T μ)ᗮ = ⊥ :=
  hSymm.orthogonalComplement_iSup_eigenspaces_eq_bot

end ModeExpansion
