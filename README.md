# Eigenraum - Formal Verification of Vibrational Energy Transport in Frequency Space

[日本語](README-ja.md)

Lean 4 + Mathlib formalization of the mathematical core behind Density-Driven Dynamics (DDD) energy transport and Modal Field Projection (MFP) for vibrational systems.

This repository derives `C = 1 / f` from explicit premises, proves dynamical consequences for the DDD ODE, and verifies the consistency chain linking modal expansions to the transport equation. No numerical experiments or simulations are included.

**zero sorry, zero axiom, zero opaque.** Lean `v4.29.0`, Mathlib `v4.29.0`.

## What Is Proved

The central result is:

- Under stated premises (harmonicity, weak coupling, confinement, UV boundedness, factorizability), the mode capacity is forced to `C = 1 / f`.
- Each mode of the MFP modal expansion satisfies the wave equation (forward direction). In finite dimensions, eigenspace completeness guarantees that mode expansion spans all solutions (reverse direction). In infinite dimensions, the reverse direction additionally requires compactness (Rellich-Kondrachov; see Premises).

From that result, the repository also proves:

- structural identities for the DDD ODE,
- invariant observables across DDD, SEA-like, and MFP descriptions,
- a general transform from modal loss laws `γ(f)` to DDD couplings `k(f)`,
- Landauer-style channel counting `N_eff = Σ T_α`,
- nonlinear corrections and the separation of what DDD retains vs. discards in spatial reconstruction,
- basic properties of LCAM channel transmission,
- theorems required for MFP modal expansion,
- consistency between MFP and DDD transport.

For the full list of verified formulas with physical context, see [FORMULAS.md](./FORMULAS.md) ([日本語](./FORMULAS-ja.md)).

## Proof Map

### Capacity derivation

| File | Content |
|---|---|
| `DimensionalAnalysis` | The only power-law density with power dimension is `E · ω` |
| `FluxBasis` | Bilinear antisymmetric flux decomposes into `L` and `X` bases |
| `Transitivity` | Three-mode closure yields `r(r − 1) = 0` |
| `UVConvergence` | UV-divergent branch excluded by boundedness |
| `Factorization` | `ω_n + ω_m` cannot factor as `h(ω_n) · h(ω_m)` |
| `MasterTheorem` | Combined: the factorizable weak-coupling branch selects `C = 1/f` |

### Structural results

| File | Content |
|---|---|
| `AlgebraicIdentities` | `k_eff = γ/f`, `k_int = 4πσ₁`, structural `1/f` separation |
| `CouplingTransform` | `γ → k` additivity, `Q(f)` conversion, power-law family |
| `NonlinearCapacity` | `C^NL = 1/[f(1 + βE)]` and harmonic limit |
| `NonlinearSpatialExtension` | `ρ_NL = Eω + βωE²` and diagonal reconstruction |
| `Duality` | `ω ↔ 1/ω` duality and equilibrium correspondence |
| `GaugeEquivalence` | `(C, k)` reparametrization invariance |
| `EquivalenceFramework` | Invariant observables across descriptions, MFP-DDD phase-average agreement |

### LCAM and MFP

| File | Content |
|---|---|
| `ChannelTransmission` | `T(s) = 4s(1 − s)` properties |
| `ChannelCounting` | `N_eff = Σ T_α`, saturation, mean-transmission factorization |
| `StandingTraveling` | Standing-wave superposition produces traveling-wave structure |
| `DampedOscillator` | Residual cancellation and damped-oscillator identities |
| `Completeness` | Spectral-theorem consequences for modal expansion, 1D compactness bridge |
| `ModeExpansion` | Separation of variables, multi-mode reconstruction, finite-dimensional completeness |

### Dynamics and spectral foundations

| File | Content |
|---|---|
| `DDDynamics` | Conservation from antisymmetry, unique equilibrium, flux direction, Lyapunov algebra, exponential stability |
| `MFPDDDConsistency` | Phase-averaged MFP energy agrees with DDD equilibrium |
| `PhaseAveraging` | Fourier orthogonality, period integrals, cross-mode orthogonality |
| `DirichletSpectrum1D` | 1D Dirichlet eigenvalues, orthogonality, normalization |

## Premises

This derivation assumes:

| Assumption | Basis |
|---|---|
| Confinement implies a discrete spectrum | Standard (Evans Ch. 6). Not yet in Mathlib |
| Laplacian on a bounded domain is compact self-adjoint | Same (Rellich-Kondrachov) |

Bilinearity of phase-averaged flux is proved in `PhaseAveraging.lean` via Fourier orthogonality.

In finite dimensions (`eigenspaces_complete_findim`) and in 1D (`DirichletSpectrum1D`), the above two assumptions are not needed; the results are proved directly.

## Repository Layout

| Path | Role |
|---|---|
| `Eigenraum.lean` | Top-level import |
| `Eigenraum/` | Theorem files grouped by topic |
| `lakefile.toml` | Lean package definition |
| `lean-toolchain` | Lean toolchain pin |
| `.github/workflows/` | CI and Mathlib update workflows |

## Build

```bash
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

For a fresh environment, install [elan](https://github.com/leanprover/elan) first:

```bash
# macOS
brew install elan-init
```

## Background Reading

- `C = 1/f: Derivation for inter-modal energy transport`
  <https://zenn.dev/barineco/articles/395585d1763549>
- `Modal Field Projection (MFP): Real-time wave simulation in modal space`
  <https://zenn.dev/barineco/articles/bcd1776b3a14be>

## Contribution

Issue reports are welcome. See [CONTRIBUTING.md](./CONTRIBUTING.md).

## Support

If this work is useful to you, you can support ongoing development:

- OFUSE: <https://ofuse.me/barineco>
- Ko-fi: <https://ko-fi.com/barineco>

## License

Apache License 2.0. See [LICENSE](./LICENSE).
