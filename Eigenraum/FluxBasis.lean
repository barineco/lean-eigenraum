/-
# FluxBasis: Bilinear antisymmetric flux has exactly two basis elements

Given bilinear form J(E_n, ω_n, E_m, ω_m) with:
- Each term is E_i · ω_j (power dimension constraint)
- Antisymmetry: J(n→m) = -J(m→n) under n ↔ m exchange

Then J = α · L + β · X where:
  L = E_m ω_m - E_n ω_n  (Local basis)
  X = E_m ω_n - E_n ω_m  (Cross basis)

Appendix A of https://zenn.dev/barineco/articles/395585d1763549
-/

import Mathlib.Tactic

/-! ## Setup: A bilinear antisymmetric form over (E, ω) pairs -/

/-- Bilinear form over (E, omega) pairs, determined by four coefficients. -/
structure BilinearFluxCoeffs where
  a₁ : ℝ  -- coefficient of E_n ω_n
  a₂ : ℝ  -- coefficient of E_n ω_m
  a₃ : ℝ  -- coefficient of E_m ω_n
  a₄ : ℝ  -- coefficient of E_m ω_m

/-- Evaluate the general bilinear form -/
def BilinearFluxCoeffs.eval (c : BilinearFluxCoeffs) (En ωn Em ωm : ℝ) : ℝ :=
  c.a₁ * (En * ωn) + c.a₂ * (En * ωm) + c.a₃ * (Em * ωn) + c.a₄ * (Em * ωm)

/-- The form obtained by swapping n ↔ m -/
def BilinearFluxCoeffs.swap (c : BilinearFluxCoeffs) : BilinearFluxCoeffs :=
  { a₁ := c.a₄, a₂ := c.a₃, a₃ := c.a₂, a₄ := c.a₁ }

/-- Antisymmetry condition: J(n→m) + J(m→n) = 0 for all (E, ω) values -/
def BilinearFluxCoeffs.isAntisymmetric (c : BilinearFluxCoeffs) : Prop :=
  c.a₁ + c.a₄ = 0 ∧ c.a₂ + c.a₃ = 0

theorem antisymmetric_iff (c : BilinearFluxCoeffs) :
    c.isAntisymmetric ↔ c.a₄ = -c.a₁ ∧ c.a₃ = -c.a₂ := by
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · intro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- Antisymmetric bilinear flux = alpha * L + beta * X. -/
theorem flux_basis_decomposition (c : BilinearFluxCoeffs) (h : c.isAntisymmetric)
    (En ωn Em ωm : ℝ) :
    c.eval En ωn Em ωm =
      (-c.a₁) * (Em * ωm - En * ωn) + (-c.a₂) * (Em * ωn - En * ωm) := by
  obtain ⟨h1, h2⟩ := (antisymmetric_iff c).mp h
  unfold BilinearFluxCoeffs.eval
  rw [h1, h2]
  ring
