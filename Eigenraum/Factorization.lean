/-
# Factorization: r = 1 flux cannot factor into per-mode terms

## Statement

The r = 1 flux has the form (ω_n + ω_m)(E_m - E_n).
The coefficient (ω_n + ω_m) CANNOT be written as h(ω_n) · h(ω_m)
for any function h : ℝ → ℝ.

This is a pure algebraic fact: a sum is not a product.

Combined with:
- Transitivity → r ∈ {0, 1, ∞}
- UV boundedness → r ∈ {0, 1}
- Factorization impossibility → r = 0

We get: C = 1/f is the unique capacity for factorizable coupling.

## Reference

https://zenn.dev/barineco/articles/395585d1763549 §4 Step 4 (P4a).
-/

import Mathlib.Tactic

/-! ## The factorization impossibility theorem -/

/-- x + y cannot factor as h(x) * h(y) (AM != GM). -/
theorem sum_not_factorizable :
    ¬ ∃ h : ℝ → ℝ, ∀ x y : ℝ, 0 < x → 0 < y → x + y = h x * h y := by
  intro ⟨h, hf⟩
  -- Evaluate at (1,1), (1,3), (3,3) to derive 16 = 12 contradiction
  have h11 := hf 1 1 one_pos one_pos
  have h13 := hf 1 3 one_pos (by norm_num : (0:ℝ) < 3)
  have h33 := hf 3 3 (by norm_num : (0:ℝ) < 3) (by norm_num : (0:ℝ) < 3)
  have h1_ne : h 1 ≠ 0 := by
    intro h1z
    rw [h1z, mul_zero] at h11
    norm_num at h11
  have h3_eq : h 3 = 4 / h 1 := by
    have := h13
    field_simp at this ⊢
    linarith
  have h1_sq : h 1 * h 1 = 2 := by linarith
  rw [h3_eq] at h33
  have h33' : (4 / h 1) * (4 / h 1) = 6 := by linarith
  have : 16 = 6 * (h 1 * h 1) := by
    field_simp at h33'
    nlinarith [sq_abs (h 1)]
  rw [h1_sq] at this
  norm_num at this

/-! ## The r = 0 flux IS factorizable -/

/-- r = 0 flux has constant coupling: trivially factorizable. -/
theorem r0_trivially_factors :
    ∀ En ωn Em ωm : ℝ,
    Em * ωm - En * ωn = 1 * (Em * ωm) - 1 * (En * ωn) := by
  intros
  ring

/-! ## Combined selection theorem -/

/-- Combined: factorizability excludes r=1, leaving r=0 (C = 1/f). -/
theorem capacity_selection_summary :
    -- r = 1 coupling coefficient is non-factorizable
    (¬ ∃ h : ℝ → ℝ, ∀ x y : ℝ, 0 < x → 0 < y → x + y = h x * h y)
    -- therefore if factorizability is required, r = 1 is excluded
    -- leaving r = 0 as the unique solution
    := sum_not_factorizable
