/-
# Nonlinear and Spatial Extension

This file records two lightweight extensions of the core theory:

1. the first nonlinear correction to the density `ρ = Eω`
2. the fact that spatial reconstruction from DDD uses only diagonal data

The goal is to formalize the structural content without pretending to
recover phase-sensitive observables that DDD does not track.
-/

import Eigenraum.NonlinearCapacity
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

/-! ## Nonlinear density as linear part plus correction -/

/-- rho_NL = E*omega + beta*omega*E^2. -/
theorem rho_nl_linear_plus_quadratic (E ω₀ β : ℝ) :
    ρ_NL E ω₀ β = E * ω₀ + β * ω₀ * E ^ 2 := by
  unfold ρ_NL
  ring

/-- Nonlinear correction is quadratic in E. -/
theorem rho_nl_minus_linear (E ω₀ β : ℝ) :
    ρ_NL E ω₀ β - E * ω₀ = β * ω₀ * E ^ 2 := by
  rw [rho_nl_linear_plus_quadratic]
  ring

/-- beta = 0 removes the correction. -/
theorem rho_nl_correction_vanishes_at_beta_zero (E ω₀ : ℝ) :
    ρ_NL E ω₀ 0 - E * ω₀ = 0 := by
  rw [rho_nl_minus_linear]
  ring

/-- Correction is positive for positive parameters. -/
theorem rho_nl_correction_positive (E ω₀ β : ℝ)
    (hE : 0 < E) (hω : 0 < ω₀) (hβ : 0 < β) :
    0 < ρ_NL E ω₀ β - E * ω₀ := by
  rw [rho_nl_minus_linear]
  have hcorr : 0 < β * ω₀ * E ^ 2 := by positivity
  exact hcorr

/-! ## Spatial reconstruction from diagonal data -/

/-- Diagonal spatial energy: sum of E_n * w_n(x), no cross terms. -/
def spatial_energy_diag {n : ℕ} (E w : Fin n → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun i => E i * w i)

/-- Full reconstruction = diagonal + coherence term. -/
def spatial_energy_full {n : ℕ} (E w : Fin n → ℝ) (coh : ℝ) : ℝ :=
  spatial_energy_diag E w + coh

/-- Zero coherence => full = diagonal. -/
theorem spatial_full_eq_diag_when_coherence_zero {n : ℕ}
    (E w : Fin n → ℝ) :
    spatial_energy_full E w 0 = spatial_energy_diag E w := by
  unfold spatial_energy_full
  ring

/-- Difference of two reconstructions = difference of coherence terms. -/
theorem spatial_full_difference_is_coherence_difference {n : ℕ}
    (E w : Fin n → ℝ) (coh1 coh2 : ℝ) :
    spatial_energy_full E w coh1 - spatial_energy_full E w coh2 = coh1 - coh2 := by
  unfold spatial_energy_full
  ring

/-- Normalized weights reconstruct total energy (spatial completeness). -/
theorem spatial_diag_total_energy {n : ℕ}
    (E : Fin n → ℝ) (w : Fin n → Fin n → ℝ)
    (hpartition : ∀ i, Finset.sum Finset.univ (fun x => w i x) = 1) :
    Finset.sum Finset.univ (fun x => spatial_energy_diag E (fun i => w i x)) =
    Finset.sum Finset.univ E := by
  unfold spatial_energy_diag
  rw [Finset.sum_comm]
  congr 1
  ext i
  calc
    (∑ x, E i * w i x) = (∑ x, w i x) * E i := by
      simp_rw [mul_comm (E i)]
      rw [Finset.sum_mul]
    _ = E i := by rw [hpartition i, one_mul]
