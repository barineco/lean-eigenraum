/-
# Dimensional Analysis: E·ω is the unique power-dimensional monomial

## Statement (Step 1 of the derivation)

Given the dimensional constraint [dE/dt] = kg·m²·s⁻³,
and independent dimensional quantities E (kg·m²·s⁻²) and ω (s⁻¹),
the monomial E^a · ω^b satisfying the constraint has a unique solution:
  a = 1, b = 1.

This is formalized as a system of linear equations over ℤ (dimension exponents).

## Reference

https://zenn.dev/barineco/articles/395585d1763549 §4 Step 1.
-/

import Mathlib.Tactic

/-! ## Dimensional exponent system -/

/-- E^a omega^b has power dimension iff a=1, b=1. -/
theorem dimensional_uniqueness (a b : ℤ) :
    a = 1 ∧ 2 * a = 2 ∧ -2 * a + -1 * b = -3 ↔
    a = 1 ∧ b = 1 := by
  constructor
  · rintro ⟨ha, _, hs⟩
    exact ⟨ha, by omega⟩
  · rintro ⟨ha, hb⟩
    subst ha; subst hb
    exact ⟨rfl, by ring, by ring⟩

/-- Forward direction: system constraints imply a=1, b=1. -/
theorem dim_analysis_unique_solution (a b : ℤ)
    (h_kg : a = 1)
    (h_s : -2 * a + (-1) * b = -3) :
    a = 1 ∧ b = 1 := by
  exact ⟨h_kg, by omega⟩
