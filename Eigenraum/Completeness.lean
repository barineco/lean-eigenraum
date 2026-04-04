/-
# Completeness of Eigenfunctions

The spectral theorem for compact self-adjoint operators: eigenspaces
span the entire Hilbert space. This is the mathematical foundation
for the MFP mode expansion.

## What is proven (via Mathlib)

1. Eigenspaces of a compact self-adjoint operator span H
   (trivial orthogonal complement)
2. Eigenspaces are mutually orthogonal
3. Nonzero eigenspaces are finite-dimensional
4. Eigenvalues are conjugate-invariant (real over ℝ)

## What is still assumed

- The Green's operator G = (-Δ)⁻¹ on a bounded domain IS compact
  (Rellich-Kondrachov embedding theorem -- not yet in Mathlib)
- The Laplacian with symmetric BCs IS self-adjoint
  (requires Sobolev space theory -- not yet in Mathlib)

These two facts are standard in PDE theory (cf. Evans Ch.6, Reed-Simon
Vol.I Thm VI.16) but require functional analysis infrastructure that
Mathlib does not yet provide.

## Reference

https://zenn.dev/barineco/articles/bcd1776b3a14be §6, Reed-Simon Vol.I.
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact

open Module End

namespace Completeness

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ## Compact self-adjoint case -/

section Compact

variable [CompleteSpace H]

/-- **Spectral Theorem** (compact self-adjoint): eigenspaces span H. -/
theorem eigenspaces_complete (T : H →L[𝕜] H)
    (hCompact : IsCompactOperator T) (hSymm : T.IsSymmetric) :
    (⨆ μ, Module.End.eigenspace (T : Module.End 𝕜 H) μ)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hCompact hSymm

/-- Nonzero eigenspaces of a compact operator are finite-dimensional. -/
theorem eigenspaces_finite_dim (T : H →L[𝕜] H)
    (hCompact : IsCompactOperator T) (μ : 𝕜) (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (Module.End.eigenspace T.toLinearMap μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace hCompact μ hμ

end Compact

/-! ## General self-adjoint operators -/

/-- Eigenspaces of a self-adjoint operator are mutually orthogonal. -/
theorem eigenspaces_orthogonal (T : H →ₗ[𝕜] H) (hSymm : T.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun μ => Module.End.eigenspace T μ)
      fun μ => (Module.End.eigenspace T μ).subtypeₗᵢ :=
  hSymm.orthogonalFamily_eigenspaces

/-- Eigenvalues of a self-adjoint operator are conjugate-invariant (real over ℝ). -/
theorem eigenvalues_conjugate_invariant (T : H →ₗ[𝕜] H) (hSymm : T.IsSymmetric)
    {μ : 𝕜} (hμ : Module.End.HasEigenvalue T μ) :
    starRingEnd 𝕜 μ = μ :=
  hSymm.conj_eigenvalue_eq_self hμ

/-! ## Finite-dimensional case -/

section FiniteDim

variable [FiniteDimensional 𝕜 H]

/-- Finite-dimensional spectral theorem: eigenspaces span H. -/
theorem eigenspaces_complete_findim (T : H →ₗ[𝕜] H) (hSymm : T.IsSymmetric) :
    (⨆ μ, Module.End.eigenspace T μ)ᗮ = ⊥ :=
  hSymm.orthogonalComplement_iSup_eigenspaces_eq_bot

end FiniteDim

/-! ## 1D case: compactness without Rellich-Kondrachov

In dimension 1, the embedding H¹(0,L) ↪↪ L²(0,L) follows from
Arzelà-Ascoli + Cauchy-Schwarz, without the full Sobolev embedding
machinery. This gives a direct path to `IsCompactOperator` for
the 1D Green's operator.

**Logical chain:**

1. H¹(0,L) bounded ⟹ uniform bound + equicontinuity  (Cauchy-Schwarz)
2. Arzelà-Ascoli ⟹ compact in C([0,L])               (Mathlib)
3. C([0,L]) ↪ L²(0,L) continuous ⟹ compact in L²     (composition)
4. G = (-Δ)⁻¹ maps L² into H¹ boundedly              (elliptic regularity)
5. ∴ G : L² → L² is compact                           (1 + 2 + 3 + 4)

Steps 1–2 require only the fundamental theorem of calculus for
absolutely continuous functions. Step 3 is trivial. Step 4 is the
only PDE input, but in 1D it is an ODE estimate.

Combined with `eigenspaces_complete` above and the explicit eigenpairs
in `DirichletSpectrum1D`, this closes the 1D spectral picture:

- `DirichletSpectrum1D`: explicit ψₙ, λₙ by direct computation
- `Completeness.eigenspaces_complete`: abstract span from compactness
- This section: compactness from Arzelà-Ascoli (1D bridge)

### Roadmap to Mathlib

1. Define H¹(0,L) as a subspace of L²   (`WeakDerivative`)
2. Prove H¹(0,L) ↪ C([0,L])             (Cauchy-Schwarz)
3. Apply Arzelà-Ascoli                    (Mathlib `IsCompact.isCompact_arzela_ascoli`)
4. Conclude `IsCompactOperator G`         (composition)

Step 1–2 are the minimal Sobolev infrastructure needed.
Steps 3–4 use existing Mathlib API.
-/

section OneDim

variable [CompleteSpace H]

/-- **1D compactness bridge**: if a self-adjoint operator is compact
(which in 1D follows from Arzelà-Ascoli, not Rellich-Kondrachov),
then eigenspaces span H and each nonzero eigenspace is finite-dimensional.

This packages `eigenspaces_complete` and `eigenspaces_finite_dim` into
a single statement suitable for 1D applications. The hypothesis
`IsCompactOperator T` is the only gap; in 1D it is provable from
Arzelà-Ascoli once H¹(0,L) is formalized. -/
theorem compact_self_adjoint_spectral_package (T : H →L[𝕜] H)
    (hCompact : IsCompactOperator T) (hSymm : T.IsSymmetric) :
    (⨆ μ, Module.End.eigenspace (T : Module.End 𝕜 H) μ)ᗮ = ⊥ ∧
    ∀ μ : 𝕜, μ ≠ 0 →
      FiniteDimensional 𝕜 (Module.End.eigenspace T.toLinearMap μ) :=
  ⟨eigenspaces_complete T hCompact hSymm,
   fun μ hμ => eigenspaces_finite_dim T hCompact μ hμ⟩

open Real in
/-- **1D eigenvalue-eigenfunction link**: combining the spectral package
with the Dirichlet eigenvalue formula λₙ = (nπ/L)² gives
ω² = c²λₙ = (nπc/L)².

This is the bridge between `Completeness.eigenspaces_complete`
(abstract) and `DirichletSpectrum1D.dirichlet_dispersion` (concrete). -/
theorem dirichlet_spectral_bridge (n : ℕ) (L c : ℝ)
    (hL : 0 < L) (hn : 0 < n) :
    c ^ 2 * ((↑n * π / L) ^ 2) = (↑n * π * c / L) ^ 2 ∧
    0 < (↑n * π / L) ^ 2 := by
  refine ⟨by ring, ?_⟩
  apply sq_pos_of_pos
  exact div_pos (mul_pos (Nat.cast_pos.mpr hn) pi_pos) hL

end OneDim

/-! ## Eigenvalue-frequency relation -/

/-- ω² = c²/μ iff μ = c²/ω². -/
theorem green_eigenvalue_frequency (c_sq ω_sq μ : ℝ)
    (hμ : μ ≠ 0) (hω : ω_sq ≠ 0) :
    ω_sq = c_sq / μ ↔ μ = c_sq / ω_sq := by
  constructor <;> (intro h; field_simp at h ⊢; nlinarith)

end Completeness
