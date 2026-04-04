/-
# Transitivity: The core algebraic constraint r(r-1) = 0

## Statement

For bilinear antisymmetric flux J = α(L) + β(X) with mixing ratio r = β/α,
the zero-flux transitivity condition over 3 modes (n, m, k) with
distinct frequencies (ω_n, ω_m, ω_k) implies:

  r * (r - 1) = 0

i.e., r = 0 or r = 1.

## Proof strategy

Define:
  LHS = (a + r·b)(b + r·c)(c + r·a)
  RHS = (a + r·c)(b + r·a)(c + r·b)

where a = ω_n, b = ω_m, c = ω_k.

Transitivity requires LHS = RHS, i.e., LHS - RHS = 0.

We prove:
  LHS - RHS = (a - b)(b - c)(c - a) · r · (r - 1)

Since (a - b)(b - c)(c - a) ≠ 0 for distinct frequencies,
we conclude r(r - 1) = 0.

Appendix B of https://zenn.dev/barineco/articles/395585d1763549
-/

import Mathlib.Tactic

/-! ## The key algebraic identity -/

/-- a^2(b-c) + b^2(c-a) + c^2(a-b) = -(a-b)(b-c)(c-a). -/
theorem symmetric_poly_identity (a b c : ℝ) :
    a ^ 2 * (b - c) + b ^ 2 * (c - a) + c ^ 2 * (a - b) =
    -(a - b) * (b - c) * (c - a) := by
  ring

/-- Transitivity factorization: LHS - RHS = (a-b)(b-c)(c-a) * r * (r-1). -/
theorem transitivity_factorization (a b c r : ℝ) :
    (a + r * b) * (b + r * c) * (c + r * a) -
    (a + r * c) * (b + r * a) * (c + r * b) =
    (a - b) * (b - c) * (c - a) * r * (r - 1) := by
  ring

/-- Transitivity + distinct frequencies => r * (r - 1) = 0. -/
theorem transitivity_implies_r_constraint (r : ℝ)
    (a b c : ℝ) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (h_transit : (a + r * b) * (b + r * c) * (c + r * a) =
                 (a + r * c) * (b + r * a) * (c + r * b)) :
    r * (r - 1) = 0 := by
  have h_factor := transitivity_factorization a b c r
  have h_diff : (a + r * b) * (b + r * c) * (c + r * a) -
                (a + r * c) * (b + r * a) * (c + r * b) = 0 := by linarith
  rw [h_factor] at h_diff
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hbc' : b - c ≠ 0 := sub_ne_zero.mpr hbc
  have hca' : c - a ≠ 0 := sub_ne_zero.mpr hca
  have h_prod_ne : (a - b) * (b - c) * (c - a) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hab' hbc') hca'
  have h_eq : (a - b) * (b - c) * (c - a) * (r * (r - 1)) = 0 := by linarith
  exact (mul_eq_zero.mp h_eq).resolve_left h_prod_ne

theorem r_is_zero_or_one (r : ℝ)
    (a b c : ℝ) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (h_transit : (a + r * b) * (b + r * c) * (c + r * a) =
                 (a + r * c) * (b + r * a) * (c + r * b)) :
    r = 0 ∨ r = 1 := by
  have h := transitivity_implies_r_constraint r a b c hab hbc hca h_transit
  rcases mul_eq_zero.mp h with h0 | h1
  · left; exact h0
  · right; linarith

/-! ## Zero-flux equilibrium conditions for each r value -/

/-- r=0 equilibrium: E_n * omega_n = E_m * omega_m. -/
theorem r0_equilibrium (En ωn Em ωm : ℝ) :
    let J := Em * ωm - En * ωn  -- L-basis with r = 0
    J = 0 ↔ En * ωn = Em * ωm := by
  simp only
  constructor
  · intro h; linarith
  · intro h; linarith

/-- r=1 equilibrium: (omega_n + omega_m)(E_m - E_n) = 0. -/
theorem r1_equilibrium (En ωn Em ωm : ℝ) :
    let J := (Em * ωm - En * ωn) + (Em * ωn - En * ωm)
    -- = (ωn + ωm)(Em - En)
    J = 0 ↔ (ωn + ωm) * (Em - En) = 0 := by
  simp only
  constructor
  · intro h
    have : Em * ωm - En * ωn + (Em * ωn - En * ωm) =
           (ωn + ωm) * (Em - En) := by ring
    linarith
  · intro h
    have : (ωn + ωm) * (Em - En) =
           Em * ωm - En * ωn + (Em * ωn - En * ωm) := by ring
    linarith
