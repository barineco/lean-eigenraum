/-
# Equivalence Framework: invariant observables across descriptions

This file collects theorems expressing that DDD, SEA-like, action-like,
and MFP descriptions can encode the same observable transport when the
parameters are reparametrized appropriately.

The point is not regime branching, but coordinate equivalence:
different descriptions expose different variables while preserving the
same total flux or total energy.
-/

import Eigenraum.GaugeEquivalence
import Eigenraum.PhaseAveraging
import Mathlib.Tactic

open Real intervalIntegral

noncomputable section

/-! ## Alternative parametrizations of the same pairwise flux -/

/-- Action-like flux (r = infinity branch). -/
def flux_rInf (k'' En ωn Em ωm : ℝ) : ℝ := k'' * (En / ωn - Em / ωm)

/-- r=0 flux can be rewritten in r=1 form by reparametrizing k. -/
theorem flux_r0_eq_flux_r1_reparam
    (k En ωn Em ωm : ℝ)
    (hden : (ωn + ωm) * (En - Em) ≠ 0) :
    flux_r0 k En ωn Em ωm =
    flux_r1
      (k * (En * ωn - Em * ωm) / ((ωn + ωm) * (En - Em)))
      En ωn Em ωm := by
  have hrew :
      flux_r1
        (k * (En * ωn - Em * ωm) / ((ωn + ωm) * (En - Em)))
        En ωn Em ωm =
      flux_r0 k En ωn Em ωm := by
    unfold flux_r0 flux_r1
    field_simp [hden]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_div_cancel_left₀ (k * (En * ωn - Em * ωm)) hden)
  exact hrew.symm

/-- r=0 flux can be rewritten in r=inf form by reparametrizing k. -/
theorem flux_r0_eq_flux_rInf_reparam
    (k En ωn Em ωm : ℝ)
    (hωn : ωn ≠ 0) (hωm : ωm ≠ 0)
    (hden : En / ωn - Em / ωm ≠ 0) :
    flux_r0 k En ωn Em ωm =
    flux_rInf
      (k * (En * ωn - Em * ωm) / (En / ωn - Em / ωm))
      En ωn Em ωm := by
  have hrew :
      flux_rInf
        (k * (En * ωn - Em * ωm) / (En / ωn - Em / ωm))
        En ωn Em ωm =
      flux_r0 k En ωn Em ωm := by
    have hcross : En * ωm - ωn * Em ≠ 0 := by
      intro hzero
      apply hden
      field_simp [hωn, hωm]
      linarith
    unfold flux_r0 flux_rInf
    field_simp [hωn, hωm, hden]
  exact hrew.symm

/-- Decay exponent invariant under capacity-gauge tradeoff. -/
theorem gamma_exponent_invariant (α β Δα : ℝ) :
    (α + Δα) + (β - Δα) = α + β :=
  capacity_k_tradeoff α β Δα

/-! ## Basis changes preserve total energy -/

/-- Total energy is invariant under basis change. -/
theorem total_energy_basis_invariant {N M : ℕ}
    (c_sq : Fin M → Fin N → ℝ)
    (E_α : Fin M → ℝ)
    (h_complete : ∀ α, Finset.sum Finset.univ (fun n => c_sq α n) = 1) :
    Finset.sum Finset.univ (fun n =>
      Finset.sum Finset.univ (fun α => c_sq α n * E_α α)) =
    Finset.sum Finset.univ (fun α => E_α α) :=
  lcam_energy_interchange c_sq E_α h_complete

/-- DDD equilibrium preserved by uniform MFP decay. -/
theorem ddd_equilibrium_invariant_under_uniform_decay (E₀ ω T γ t : ℝ)
    (h_eq : E₀ * ω = T) :
    (E₀ * exp (-2 * γ * t)) * ω = T * exp (-2 * γ * t) :=
  ddd_equilibrium_preserved_by_mfp E₀ ω T γ t h_eq

/-- Density ratios invariant under uniform decay. -/
theorem density_ratio_invariant_under_uniform_decay (E₁₀ E₂₀ ω₁ ω₂ γ t : ℝ) :
    ((E₁₀ * exp (-2 * γ * t)) * ω₁) / ((E₂₀ * exp (-2 * γ * t)) * ω₂) =
    (E₁₀ * ω₁) / (E₂₀ * ω₂) := by
  have hexp : exp (-2 * γ * t) ≠ 0 := by
    exact ne_of_gt (exp_pos _)
  have hcancel := mfp_ratio_preserved (E₁₀ * ω₁) (E₂₀ * ω₂) γ t hexp
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcancel

/-- Phase-averaged MFP energy = DDD energy, with period integrals instantiated.
    Combines MFPDDDConsistency.ddd_is_phase_average_of_mfp with the period
    integral results from PhaseAveraging. -/
theorem ddd_mfp_phase_average_agreement (γ ω : ℝ) :
    (1 / (2 * π)) *
      ((γ ^ 2 + ω ^ 2) * (∫ θ in (0:ℝ)..(2*π), sin θ ^ 2) -
       2 * γ * ω * (∫ θ in (0:ℝ)..(2*π), sin θ * cos θ) +
       ω ^ 2 * (∫ θ in (0:ℝ)..(2*π), cos θ ^ 2)) =
    ω ^ 2 + γ ^ 2 / 2 := by
  rw [integral_sin_sq_period, integral_cos_sq_period, integral_sin_mul_cos_period]
  field_simp; ring
