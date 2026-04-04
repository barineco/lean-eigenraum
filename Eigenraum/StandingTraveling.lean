/-
# Standing Wave ↔ Traveling Wave Decomposition

The mathematical core of MFP §2: "定在波は止まらない"

A standing wave cos(kx)cos(ωt) is the superposition of two
counter-propagating traveling waves. This is a trigonometric identity,
not a physical approximation.

When multiple standing waves with different frequencies are summed,
the cross-terms between different standing waves produce NET traveling
components that are not canceled -- this is the origin of "moving antinodes"
and ultimately of wavefront propagation in mode sums.

## Reference

https://zenn.dev/barineco/articles/bcd1776b3a14be §2, §3.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Real

/-! ## The fundamental decomposition -/

/-- Standing wave = two counter-propagating traveling waves. -/
theorem standing_wave_decomposition (k x ω t : ℝ) :
    cos (k * x) * cos (ω * t) =
    (cos (k * x - ω * t) + cos (k * x + ω * t)) / 2 := by
  rw [cos_sub, cos_add]
  ring

/-- Two standing waves produce four traveling wave components. -/
theorem two_standing_waves_four_travelers (k₁ k₂ x ω₁ ω₂ t : ℝ) :
    cos (k₁ * x) * cos (ω₁ * t) + cos (k₂ * x) * cos (ω₂ * t) =
    (cos (k₁ * x - ω₁ * t) + cos (k₁ * x + ω₁ * t) +
     cos (k₂ * x - ω₂ * t) + cos (k₂ * x + ω₂ * t)) / 2 := by
  rw [standing_wave_decomposition k₁ x ω₁ t,
      standing_wave_decomposition k₂ x ω₂ t]
  ring

/-! ## Beat period = round-trip time -/

/-- Beat period 1/Delta_f = 2L/c. -/
theorem beat_period_eq_round_trip (c L : ℝ) (hc : c ≠ 0) (hL : L ≠ 0) :
    1 / (c / (2 * L)) = 2 * L / c := by
  field_simp

/-- Distance per beat period = 2L (round trip). -/
theorem beat_distance_eq_round_trip (c L : ℝ) (hc : c ≠ 0) (hL : L ≠ 0) :
    c * (1 / (c / (2 * L))) = 2 * L := by
  rw [beat_period_eq_round_trip c L hc hL]
  field_simp

/-! ## Spatial resolution from mode count -/

/-- Wave packet width: Delta_x = 2L/N. -/
theorem packet_width (c L N : ℝ) (hN : N ≠ 0) (hL : L ≠ 0) (hc : c ≠ 0) :
    c / (N * c / (2 * L)) = 2 * L / N := by
  field_simp

/-! ## Superposition -/

/-- L(f) = 0 and L(g) = 0 imply L(alpha*f + beta*g) = 0. -/
theorem linear_superposition {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (L : V →ₗ[ℝ] V) (f g : V)
    (hf : L f = 0) (hg : L g = 0) (α β : ℝ) :
    L (α • f + β • g) = 0 := by
  rw [map_add, map_smul, map_smul, hf, hg, smul_zero, smul_zero, add_zero]
