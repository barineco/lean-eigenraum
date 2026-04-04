/-
# Gauge Equivalence: (C, k) reparametrization invariance

## Statement

For single-pathway systems (one coupling path between subsystems),
the observable flux J = k · Δρ can be reparametrized:

  J = k · (E_n · f_n - E_m · f_m)       [C = 1/f, density-driven]
    = k' · (E_n - E_m)                    [C = const, SEA-like]
    = k'' · (E_n/f_n - E_m/f_m)           [C ∝ f, action-driven]

by absorbing the frequency factors into k.
The observable J(t) is identical in all parametrizations.

This is why C=1/f cannot be distinguished from C=const by fitting alone.
The selection is by the derivation (P1-P4), not by data.

## Reference

https://zenn.dev/barineco/articles/395585d1763549 §5.
-/

import Mathlib.Tactic

/-! ## Gauge transformation between (C, k) parametrizations -/
def flux_r0 (k En ωn Em ωm : ℝ) : ℝ := k * (En * ωn - Em * ωm)

def flux_r1 (k' En ωn Em ωm : ℝ) : ℝ := k' * (ωn + ωm) * (En - Em)

/-- L-flux = SEA-flux + cross term proportional to Δω·ΔE. -/
theorem flux_algebraic_decomposition (En ωn Em ωm : ℝ) :
    En * ωn - Em * ωm =
    (ωn + ωm) / 2 * (En - Em) + (En + Em) / 2 * (ωn - ωm) := by
  ring

/-- At equal frequencies, L-flux and SEA-flux are indistinguishable. -/
theorem same_freq_gauge_equivalence (En Em ω k : ℝ) :
    flux_r0 k En ω Em ω = k * ω * (En - Em) := by
  unfold flux_r0
  ring

/-- Capacity-k tradeoff: shifting α by Δα requires β -> β - Δα. -/
theorem capacity_k_tradeoff (α β Δα : ℝ) :
    (α + Δα) + (β - Δα) = α + β := by ring
