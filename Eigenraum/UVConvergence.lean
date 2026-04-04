/-
# UV Convergence: r = ∞ exclusion by boundedness

The exclusion of r = ∞ is a mathematical consequence of a boundedness
condition, not a physical judgment.

Axiom (boundedness): equilibrium energy per mode is bounded as ω → ∞.
Theorem: r = ∞ violates this condition; r ∈ {0, 1} satisfy it.
-/

import Mathlib.Tactic

/-! ## Equilibrium energy functions -/

noncomputable def E_eq_r0 (T : ℝ) (ω : ℝ) : ℝ := T / ω
def E_eq_r1 (T : ℝ) (_ : ℝ) : ℝ := T
def E_eq_rinf (T : ℝ) (ω : ℝ) : ℝ := T * ω

/-! ## Boundedness properties -/

theorem r1_bounded (T : ℝ) : ∀ ω : ℝ, E_eq_r1 T ω = T := fun _ => rfl

theorem r0_bounded_above (T : ℝ) (hT : 0 < T) (ω : ℝ) (hω : 1 ≤ ω) :
    E_eq_r0 T ω ≤ T := by
  unfold E_eq_r0
  have hω_pos : (0 : ℝ) < ω := by linarith
  exact div_le_of_le_mul₀ (le_of_lt hω_pos) (le_of_lt hT) (by nlinarith)

/-- E = T*omega is unbounded as omega -> infinity. -/
theorem rinf_unbounded (T : ℝ) (hT : 0 < T) :
    ∀ M : ℝ, ∃ ω : ℝ, 1 ≤ ω ∧ E_eq_rinf T ω > M := by
  intro M
  use max 1 (M / T + 1)
  constructor
  · exact le_max_left 1 _
  · unfold E_eq_rinf
    have hmax : (max 1 (M / T + 1) : ℝ) ≥ M / T + 1 := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left hmax (le_of_lt hT),
               div_mul_cancel₀ M (ne_of_gt hT)]

/-! ## Main theorem: boundedness excludes r = ∞ -/

/-- Boundedness of E(omega) excludes r = infinity. -/
theorem uv_convergence_excludes_rinf (T : ℝ) (hT : 0 < T)
    (h_bounded : ∃ M : ℝ, ∀ ω : ℝ, 1 ≤ ω → E_eq_rinf T ω ≤ M) :
    False := by
  obtain ⟨M, hM⟩ := h_bounded
  obtain ⟨ω, hω1, hω2⟩ := rinf_unbounded T hT M
  linarith [hM ω hω1]
