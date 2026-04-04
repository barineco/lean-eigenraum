/-
# Channel Transmission: T_α = 4s_α(1-s_α) properties

## Statement

The LCAM transmission coefficient T_α = 4·s_α·(1-s_α),
where s_α ∈ [0,1] is the string character of hybrid mode α,
has the following properties:

1. T_α ∈ [0, 1]
2. T_α = 0 iff s_α = 0 or s_α = 1 (pure modes don't transmit)
3. T_α = 1 iff s_α = 1/2 (perfectly hybridized mode)
4. T_α is symmetric: T(s) = T(1-s)

## Reference

https://zenn.dev/barineco/articles/bcd1776b3a14be §4.
-/

import Mathlib.Tactic

/-! ## Transmission coefficient -/

/-- The LCAM transmission coefficient -/
def T_lcam (s : ℝ) : ℝ := 4 * s * (1 - s)

theorem T_symmetric (s : ℝ) : T_lcam s = T_lcam (1 - s) := by
  unfold T_lcam; ring

theorem T_at_zero : T_lcam 0 = 0 := by unfold T_lcam; ring

theorem T_at_one : T_lcam 1 = 0 := by unfold T_lcam; ring

theorem T_at_half : T_lcam (1/2) = 1 := by unfold T_lcam; ring

theorem T_zero_iff (s : ℝ) : T_lcam s = 0 ↔ s = 0 ∨ s = 1 := by
  unfold T_lcam
  constructor
  · intro h
    have h1 : 4 * (s * (1 - s)) = 0 := by linarith
    have h2 : s * (1 - s) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with hs | hs
    · left; exact hs
    · right; linarith
  · rintro (rfl | rfl) <;> ring

theorem T_le_one (s : ℝ) (_hs0 : 0 ≤ s) (_hs1 : s ≤ 1) :
    T_lcam s ≤ 1 := by
  unfold T_lcam
  nlinarith [sq_nonneg (s - 1/2)]

theorem T_nonneg (s : ℝ) (_hs0 : 0 ≤ s) (_hs1 : s ≤ 1) :
    0 ≤ T_lcam s := by
  unfold T_lcam
  nlinarith

/-- T = 1 iff s = 1/2 on [0,1]. -/
theorem T_max_unique (s : ℝ) (_hs0 : 0 ≤ s) (_hs1 : s ≤ 1)
    (hT : T_lcam s = 1) : s = 1 / 2 := by
  unfold T_lcam at hT
  have h : (2 * s - 1) ^ 2 = 0 := by ring_nf; nlinarith
  have h2 : 2 * s - 1 = 0 := by nlinarith [sq_nonneg (2 * s - 1)]
  linarith

/-- N_eff <= N. -/
theorem neff_le_count {n : ℕ} (s : Fin n → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1) :
    Finset.sum Finset.univ (fun i => T_lcam (s i)) ≤ (n : ℝ) := by
  calc Finset.sum Finset.univ (fun i => T_lcam (s i))
      ≤ Finset.sum Finset.univ (fun _ => (1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        exact T_le_one (s i) (hs0 i) (hs1 i)
    _ = (n : ℝ) := by simp [Finset.sum_const]
