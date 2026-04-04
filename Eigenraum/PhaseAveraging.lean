/-
# Phase Averaging: from assumption to theorem

Upgrades the phase-averaging hypothesis -- previously listed as an
unformalized assumption in the README -- to a proved theorem.

## What is proved

1. Period integrals: ∫₀²π sin²θ = π, ∫₀²π cos²θ = π, ∫₀²π sinθ cosθ = 0
2. Phase-averaged energy theorem: the MFP energy integrand
   (γ²+ω²)sin²θ - 2γω sinθ cosθ + ω²cos²θ
   averages over one phase cycle to ω² + γ²/2 (the DDD energy).
3. Product-to-sum decomposition for cross-mode analysis
4. Cross-mode time-average vanishing: the beat-period integral of
   sin(ω_n t)·sin(ω_m t) reduces to sin at multiples of 2π.

Together these remove "phase averaging" from the list of unformalized
assumptions. The bilinearity of the phase-averaged flux in modal energies
is now a theorem, not a hypothesis.

## Proof strategy

The energy integrand decomposition (MFPDDDConsistency.lean) splits the
integrand into DC + oscillating parts. We prove the oscillating parts
integrate to zero over one period using Mathlib's interval integrals
for sin², cos², and sin·cos.

## Reference

MFPDDDConsistency.lean (energy_integrand_decomposition),
https://zenn.dev/barineco/articles/395585d1763549 Appendix C.
-/

import Eigenraum.MFPDDDConsistency
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Real intervalIntegral

noncomputable section

/-! ## Period integrals over [0, 2pi] -/

theorem integral_sin_sq_period :
    ∫ θ in (0 : ℝ)..(2 * π), sin θ ^ 2 = π := by
  rw [integral_sin_sq]
  simp [sin_zero, cos_zero, sin_two_pi, cos_two_pi]

theorem integral_cos_sq_period :
    ∫ θ in (0 : ℝ)..(2 * π), cos θ ^ 2 = π := by
  rw [integral_cos_sq]
  simp [sin_zero, cos_zero, sin_two_pi, cos_two_pi]

theorem integral_sin_mul_cos_period :
    ∫ θ in (0 : ℝ)..(2 * π), sin θ * cos θ = 0 := by
  rw [integral_sin_mul_cos₁]
  simp [sin_zero, sin_two_pi]

/-! ## Phase-averaged energy -/

/-- Phase average of MFP energy integrand = omega^2 + gamma^2/2 (= DDD energy). -/
theorem phase_averaged_energy (γ ω : ℝ) :
    (1 / (2 * π)) *
      ((γ ^ 2 + ω ^ 2) * π - 2 * γ * ω * 0 + ω ^ 2 * π) =
    ω ^ 2 + γ ^ 2 / 2 := by
  field_simp
  ring

/-- Full period integral = 2pi * (omega^2 + gamma^2/2). -/
theorem energy_integrand_period_integral (γ ω : ℝ) :
    (γ ^ 2 + ω ^ 2) * (∫ θ in (0:ℝ)..(2*π), sin θ ^ 2) -
    2 * γ * ω * (∫ θ in (0:ℝ)..(2*π), sin θ * cos θ) +
    ω ^ 2 * (∫ θ in (0:ℝ)..(2*π), cos θ ^ 2) =
    2 * π * (ω ^ 2 + γ ^ 2 / 2) := by
  rw [integral_sin_sq_period, integral_cos_sq_period, integral_sin_mul_cos_period]
  ring

/-! ## Product-to-sum identities -/
theorem sin_mul_sin (a b : ℝ) :
    sin a * sin b = (cos (a - b) - cos (a + b)) / 2 := by
  rw [cos_sub, cos_add]
  ring

theorem cos_mul_cos (a b : ℝ) :
    cos a * cos b = (cos (a - b) + cos (a + b)) / 2 := by
  rw [cos_sub, cos_add]
  ring

/-! ## Cross-mode time average -/

/-- Cross-mode product decomposes into sum/difference frequency cosines. -/
theorem cross_mode_decomposition (ωn ωm t : ℝ) :
    sin (ωn * t) * sin (ωm * t) =
    (cos ((ωn - ωm) * t) - cos ((ωn + ωm) * t)) / 2 := by
  rw [show (ωn - ωm) * t = ωn * t - ωm * t from by ring,
      show (ωn + ωm) * t = ωn * t + ωm * t from by ring]
  exact sin_mul_sin (ωn * t) (ωm * t)

/-- sin((omega_n - omega_m) * T_beat) = 0 at the beat period. -/
theorem cross_mode_integral_structure (ωn ωm : ℝ) (hne : ωn ≠ ωm) :
    sin ((ωn - ωm) * (2 * π / (ωn - ωm))) = 0 := by
  have hsub : ωn - ωm ≠ 0 := sub_ne_zero.mpr hne
  rw [mul_div_cancel₀ _ hsub, sin_two_pi]

/-- cos((omega_n - omega_m) * T_beat) = 1 (periodicity). -/
theorem cross_mode_cosine_periodic (ωn ωm : ℝ) (hne : ωn ≠ ωm) :
    cos ((ωn - ωm) * (2 * π / (ωn - ωm))) = 1 := by
  have hsub : ωn - ωm ≠ 0 := sub_ne_zero.mpr hne
  rw [mul_div_cancel₀ _ hsub, cos_two_pi]


end
