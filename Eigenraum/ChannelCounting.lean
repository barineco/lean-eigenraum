/-
# Channel Counting: effective channel number and saturation structure

This file packages the Landauer-style channel count

  N_eff = Σ T_α

and a few structural consequences used in the theory documents.
-/

import Eigenraum.ChannelTransmission
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

/-- Effective channel count as the sum of LCAM transmission coefficients. -/
def neff {n : ℕ} (s : Fin n → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun i => T_lcam (s i))

/-- Number of geometrically coupled channels represented as a real number. -/
def ncoupled {n : ℕ} (active : Fin n → Prop) [DecidablePred active] : ℝ :=
  ((Finset.univ.filter active).card : ℝ)

/-- Mean transmission over the active channel set. -/
def mean_transmission {n : ℕ} (s : Fin n → ℝ) (active : Fin n → Prop) [DecidablePred active] : ℝ :=
  if (Finset.univ.filter active).card = 0 then 0
  else
    (Finset.sum (Finset.univ.filter active) (fun i => T_lcam (s i))) /
    (((Finset.univ.filter active).card : ℝ))

theorem neff_eq_sum_transmissions {n : ℕ} (s : Fin n → ℝ) :
    neff s = Finset.sum Finset.univ (fun i => T_lcam (s i)) := rfl

/-- N_eff >= 0 when s_i in [0,1]. -/
theorem neff_nonneg {n : ℕ} (s : Fin n → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1) :
    0 ≤ neff s := by
  unfold neff
  exact Finset.sum_nonneg (by
    intro i _
    exact T_nonneg (s i) (hs0 i) (hs1 i))

theorem neff_le_raw_count {n : ℕ} (s : Fin n → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1) :
    neff s ≤ (n : ℝ) :=
  neff_le_count s hs0 hs1

/-- All channels at s=1/2: N_eff = N. -/
theorem neff_all_half_is_maximal {n : ℕ} :
    neff (fun _ : Fin n => (1 / 2 : ℝ)) = (n : ℝ) := by
  unfold neff
  simp [T_lcam, Finset.sum_const]
  ring

/-- N_eff = N * mean_T when all channels are active. -/
theorem neff_factorization_full {n : ℕ}
    (s : Fin n → ℝ)
    (hn : n ≠ 0) :
    neff s = (n : ℝ) *
      mean_transmission s (fun _ : Fin n => True) := by
  unfold neff mean_transmission
  have hcard : Finset.card (Finset.univ.filter (fun _ : Fin n => True)) ≠ 0 := by
    simpa using hn
  simp [hn]
  field_simp [hcard, Nat.cast_ne_zero.mpr hcard]
