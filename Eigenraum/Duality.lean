/-
# Duality: r=0 and r=∞ are ω ↔ 1/ω duals
-/

import Mathlib.Tactic

def L_basis (En ωn Em ωm : ℝ) : ℝ := Em * ωm - En * ωn
def X_basis (En ωn Em ωm : ℝ) : ℝ := Em * ωn - En * ωm

/-- Under ω → 1/ω, L becomes proportional to X. -/
theorem L_becomes_X_under_inversion (En ωn Em ωm : ℝ)
    (hωn : ωn ≠ 0) (hωm : ωm ≠ 0) :
    L_basis En (1/ωn) Em (1/ωm) =
    (1 / (ωn * ωm)) * X_basis En ωn Em ωm := by
  unfold L_basis X_basis; field_simp

/-- Under ω → 1/ω, X becomes proportional to L. -/
theorem X_becomes_L_under_inversion (En ωn Em ωm : ℝ)
    (hωn : ωn ≠ 0) (hωm : ωm ≠ 0) :
    X_basis En (1/ωn) Em (1/ωm) =
    (1 / (ωn * ωm)) * L_basis En ωn Em ωm := by
  unfold L_basis X_basis; field_simp

/-- r=1 (L+X) is self-dual under frequency inversion. -/
theorem r1_self_dual (En ωn Em ωm : ℝ) (hωn : ωn ≠ 0) (hωm : ωm ≠ 0) :
    L_basis En (1/ωn) Em (1/ωm) + X_basis En (1/ωn) Em (1/ωm) =
    (1 / (ωn * ωm)) * (L_basis En ωn Em ωm + X_basis En ωn Em ωm) := by
  rw [L_becomes_X_under_inversion En ωn Em ωm hωn hωm,
      X_becomes_L_under_inversion En ωn Em ωm hωn hωm]
  ring

/-- Equilibrium duality: r=0 ↔ r=∞ under ω → 1/ω. -/
theorem equilibrium_duality (E ω T : ℝ) :
    E * (1/ω) = T ↔ E / ω = T := by
  rw [mul_one_div]

/-- The three equilibria: T/ω and T·ω are mutual inverses. -/
theorem three_equilibria_duality (T ω : ℝ) (hω : ω ≠ 0) :
    (T / ω) * ω = T ∧ (T * ω) / ω = T :=
  ⟨div_mul_cancel₀ T hω, mul_div_cancel_right₀ T hω⟩
