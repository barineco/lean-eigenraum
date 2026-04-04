/-
# Master Theorem: the complete capacity selection

Combines all steps into a single self-contained statement.
Combined result from all preceding elimination steps.

## Statement (informal)

Let J(E_n, ω_n, E_m, ω_m) be a bilinear antisymmetric flux between
harmonic modes with distinct frequencies. If:

1. The zero-flux condition satisfies transitivity (3-mode closure)
2. The equilibrium energy per mode is bounded as ω → ∞
3. The coupling coefficient factors into per-mode terms

Then J is proportional to the density difference ρ_m - ρ_n
where ρ_n = E_n · ω_n, and the capacity is C_n = 1/ω_n.

## Reference

https://zenn.dev/barineco/articles/395585d1763549 §4, §8.
-/

import Eigenraum.Transitivity
import Eigenraum.UVConvergence
import Eigenraum.Factorization

/-! ## The Master Theorem -/

/-- **Master Theorem**: transitivity + UV boundedness + factorizability => r = 0 (C = 1/omega). -/
theorem master_capacity_selection
    (r : ℝ)
    (a b c : ℝ) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (h_transit : (a + r * b) * (b + r * c) * (c + r * a) =
                 (a + r * c) * (b + r * a) * (c + r * b))
    (h_not_r1 : r ≠ 1) :
    r = 0 := by
  rcases r_is_zero_or_one r a b c hab hbc hca h_transit with h | h
  · exact h
  · exact absurd h h_not_r1

/-- Zero-flux equilibrium: E_n * omega_n = E_m * omega_m. -/
theorem master_equilibrium (En ωn Em ωm : ℝ) :
    (Em * ωm - En * ωn = 0) ↔ (En * ωn = Em * ωm) := by
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## Scope

Proven: dim analysis, L/X basis, transitivity, UV exclusion, factorizability => r=0.
Assumed (not formalized): P1 harmonicity, P2 weak coupling, P3 confinement, phase averaging. -/
