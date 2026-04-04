/-
# 1D Dirichlet Spectrum: explicit eigenpairs without Rellich-Kondrachov

The 1D Laplacian on [0, L] with Dirichlet boundary conditions has
explicit eigenpairs:

    ψₙ(x) = sin(nπx/L),   λₙ = (nπ/L)²,   n = 1, 2, …

This file proves orthogonality, normalization, eigenvalue positivity,
and ordering -- all by direct computation, without Rellich-Kondrachov.

## Reference

Evans, PDE §6.5. Completeness: Mathlib `fourierBasis`.
-/

import Eigenraum.PhaseAveraging
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Real intervalIntegral

noncomputable section

/-! ## Eigenvalue formula -/

def dirichlet_ev (n : ℕ) (L : ℝ) : ℝ := (↑n * π / L) ^ 2

theorem dirichlet_ev_pos (n : ℕ) (L : ℝ)
    (hn : 0 < n) (hL : 0 < L) :
    0 < dirichlet_ev n L := by
  unfold dirichlet_ev; positivity

theorem dirichlet_dispersion (n : ℕ) (L c : ℝ) :
    c ^ 2 * dirichlet_ev n L = (↑n * π * c / L) ^ 2 := by
  unfold dirichlet_ev; ring

/-! ## Core integral lemma -/
theorem integral_cos_vanish (α L : ℝ)
    (hα : α ≠ 0) (hsin : sin (α * L) = 0) :
    ∫ x in (0 : ℝ)..L, cos (α * x) = 0 := by
  have step : α • ∫ x in (0:ℝ)..L, cos (α * x) =
      ∫ u in (α * 0)..(α * L), cos u :=
    smul_integral_comp_mul_left cos α
  simp only [mul_zero, integral_cos, sin_zero,
    sub_zero, hsin, smul_eq_mul] at step
  exact (mul_eq_zero.mp step).elim
    (fun h => absurd h hα) id

theorem sin_diff_nat_mul_pi (n m : ℕ) :
    sin ((↑n - ↑m) * π) = 0 := by
  rw [show (↑n - ↑m : ℝ) * π =
    (↑(↑n - ↑m : ℤ) : ℝ) * π from by push_cast; ring]
  exact sin_int_mul_pi _

theorem sin_sum_nat_mul_pi (n m : ℕ) :
    sin ((↑n + ↑m) * π) = 0 := by
  rw [show (↑n + ↑m : ℝ) * π =
    ↑(n + m) * π from by push_cast; ring]
  exact_mod_cast sin_nat_mul_pi (n + m)

/-! ## Orthogonality -/

set_option maxHeartbeats 400000 in
-- product-to-sum + integral_sub decomposition
theorem dirichlet_orthogonality (n m : ℕ) (L : ℝ)
    (hn : 0 < n) (hm : 0 < m)
    (hnm : n ≠ m) (hL : 0 < L) :
    ∫ x in (0:ℝ)..L,
      sin (↑n * π / L * x) * sin (↑m * π / L * x) = 0 := by
  have hdiff : ∫ x in (0:ℝ)..L,
      cos ((↑n - ↑m) * π / L * x) = 0 :=
    integral_cos_vanish _ _
      (div_ne_zero
        (mul_ne_zero
          (sub_ne_zero.mpr (Nat.cast_injective.ne hnm))
          (ne_of_gt pi_pos))
        (ne_of_gt hL))
      (by rw [show (↑n - ↑m) * π / L * L =
                (↑n - ↑m) * π from by field_simp]
          exact sin_diff_nat_mul_pi n m)
  have hsum : ∫ x in (0:ℝ)..L,
      cos ((↑n + ↑m) * π / L * x) = 0 :=
    integral_cos_vanish _ _
      (by apply div_ne_zero _ (ne_of_gt hL); positivity)
      (by rw [show (↑n + ↑m) * π / L * L =
                (↑n + ↑m) * π from by field_simp]
          exact sin_sum_nat_mul_pi n m)
  -- Product-to-sum identity
  have decomp : ∀ x : ℝ,
      sin (↑n * π / L * x) * sin (↑m * π / L * x) =
      (2:ℝ)⁻¹ • (cos ((↑n - ↑m) * π / L * x) -
        cos ((↑n + ↑m) * π / L * x)) := by
    intro x
    have h := sin_mul_sin (↑n * π / L * x) (↑m * π / L * x)
    rw [show ↑n * π / L * x - ↑m * π / L * x =
          (↑n - ↑m) * π / L * x from by ring,
        show ↑n * π / L * x + ↑m * π / L * x =
          (↑n + ↑m) * π / L * x from by ring] at h
    simp only [smul_eq_mul]; linarith
  simp_rw [decomp]
  rw [integral_smul]
  -- Split integral of difference
  have h_split : ∫ x in (0:ℝ)..L,
      (cos ((↑n - ↑m) * π / L * x) -
       cos ((↑n + ↑m) * π / L * x)) =
      (∫ x in (0:ℝ)..L, cos ((↑n - ↑m) * π / L * x)) -
      (∫ x in (0:ℝ)..L, cos ((↑n + ↑m) * π / L * x)) := by
    apply integral_sub <;>
      apply Continuous.intervalIntegrable <;>
      exact continuous_cos.comp
        (continuous_const.mul continuous_id')
  rw [h_split, hdiff, hsum, sub_self, smul_zero]

/-! ## Normalization -/

set_option maxHeartbeats 400000 in
-- substitution + integral_sin_sq evaluation
theorem dirichlet_normalization (n : ℕ) (L : ℝ)
    (hn : 0 < n) (hL : 0 < L) :
    ∫ x in (0:ℝ)..L,
      sin (↑n * π / L * x) ^ 2 = L / 2 := by
  have hc_pos : (0 : ℝ) < ↑n * π / L := by positivity
  have hc_ne : (↑n * π / L : ℝ) ≠ 0 := ne_of_gt hc_pos
  -- Substitution u = cx
  have step : (↑n * π / L) •
      ∫ x in (0:ℝ)..L,
        (fun u => sin u ^ 2) (↑n * π / L * x) =
      ∫ u in (↑n * π / L * 0)..(↑n * π / L * L),
        sin u ^ 2 :=
    smul_integral_comp_mul_left (fun u => sin u ^ 2)
      (↑n * π / L)
  simp only [mul_zero] at step
  rw [show ↑n * π / L * L = ↑n * π from by field_simp,
      integral_sin_sq, sin_zero, cos_zero,
      sin_nat_mul_pi] at step
  simp only [smul_eq_mul, zero_mul,
    sub_zero, mul_one, zero_add] at step
  -- Solve (nπ/L) * I = nπ/2 for I = L/2
  have hnpi : (↑n * π : ℝ) ≠ 0 := by positivity
  field_simp [hnpi, ne_of_gt hL] at step ⊢
  linarith

/-! ## Eigenvalue ordering -/

theorem dirichlet_ev_strict_mono (n m : ℕ) (L : ℝ)
    (hL : 0 < L) (hnm : n < m) :
    dirichlet_ev n L < dirichlet_ev m L := by
  unfold dirichlet_ev; gcongr

theorem dirichlet_ev_gap (n : ℕ) (L : ℝ) (hL : 0 < L) :
    dirichlet_ev (n + 1) L - dirichlet_ev n L =
    (2 * ↑n + 1) * (π / L) ^ 2 := by
  unfold dirichlet_ev; push_cast; field_simp; ring

end
