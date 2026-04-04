# Verified Formulas

[日本語](FORMULAS-ja.md)

Every formula listed in this document has been formally verified in Lean 4 + Mathlib (zero `sorry`).
Each formula is annotated with the corresponding theorem name.

Terminology and notation follow [Derivation of $C = 1/f$](https://zenn.dev/barineco/articles/395585d1763549), [Introduction to MFP](https://zenn.dev/barineco/articles/bcd1776b3a14be), and forthcoming articles on the coupling-constant catalog and LCAM hybrid modes.

---

## Abbreviations

| Abbr. | Full Name | Meaning |
|-------|-----------|---------|
| DDD | Density-Driven Dynamics | Inter-modal energy transport driven by differences in acoustic density $\Delta\rho$ |
| MFP | Modal Field Projection | Expand the spatial field in a mode basis, evolve each mode analytically as a damped oscillator, and resynthesize the spatial field |
| LCAM | Linear Combination of Acoustic Modes | The acoustic analogue of LCAO (Linear Combination of Atomic Orbitals); constructs hybrid modes of a coupled system via the eigenvalue problem of a coupling matrix $H$ |
| SEA | Statistical Energy Analysis | Traditional approach assuming energy equipartition across modes; corresponds to the $r = 1$ regime |

---

## Correspondence between $f$ and $\omega$

In acoustics and structural vibration, capacity is naturally written $C = 1/f$ ($f$ in Hz). The companion articles adopt this convention. This formalization, however, uses angular frequency $\omega = 2\pi f$ [rad/s] for compatibility with trigonometric functions and differential equations.

The two are related by:

$$
C = \frac{1}{f} = \frac{2\pi}{\omega}
$$

The $2\pi$ factor can be left in the capacity or absorbed into the coupling constant; the observable flux $J = k\Delta\rho$ is unchanged. Concretely:

| Convention | Capacity | Density | Coupling constant |
|------------|----------|---------|-------------------|
| $f$ convention (articles) | $C = 1/f$ | $\rho = Ef$ | $k_f$ |
| $\omega$ convention (this formalization) | $C = 1/\omega$ | $\rho = E\omega$ | $k_\omega = k_f / (2\pi)$ |

The flux identity $k_f \cdot Ef = k_\omega \cdot E\omega$ holds. This formalization uses the $\omega$ convention; $k$ means $k_\omega$. When comparing with numerical values from the articles, note the placement of $2\pi$.

---

## Symbol Table

| Symbol | Physical quantity | Units / remarks |
|--------|------------------|-----------------|
| $E_n$ | Energy of mode $n$ | J |
| $\omega_n$, $f_n$ | Angular frequency / frequency of mode $n$ | rad/s, Hz. $\omega = 2\pi f$ |
| $C_n$ | Mode capacity: converts energy to acoustic density | $C_n = E_n / \rho_n$ |
| $\rho_n$ | Acoustic density of mode $n$; driving variable of the DDD equation | $\rho_n = E_n \omega_n$ ($\omega$ convention). See above |
| $T$ | Common equilibrium density $\rho_n^{\mathrm{eq}} = T$ | |
| $k$ | DDD coupling constant: rate of energy flow between modes | 1/s. Mode-pair-independent scalar under weak coupling |
| $K_{nm}$ | Coupling tensor. $k$ is its symmetric contraction | |
| $\gamma_n$ | Damping rate of mode $n$ (amplitude decay constant) | rad/s |
| $\sigma_0$ | Velocity-proportional loss coefficient. $\gamma = 2\sigma_0$ (frequency-independent) | 1/s. External friction (e.g. air resistance) |
| $\sigma_1$ | Kelvin–Voigt viscosity coefficient. $\gamma = 4\pi\sigma_1 f$ (frequency-proportional) | s. Internal material damping |
| $Q$ | Quality factor. $Q = \pi f / \gamma$ | dimensionless |
| $\beta$ | Nonlinear correction parameter. Duffing-type energy dependence of frequency | 1/J |
| $r$ | Flux basis mixing ratio $r = \beta_X / \beta_L$ | dimensionless. $r = 0$: DDD, $r = 1$: SEA |
| $s_\alpha$ | Subsystem-A membership of hybrid mode $\alpha$ | dimensionless. $\sum_{n \in A} \|c_{\alpha n}\|^2$. Called "stringiness" in string–soundboard systems |
| $T_\alpha$ | Transmission coefficient of channel $\alpha$ | dimensionless. $T_\alpha = 4s_\alpha(1 - s_\alpha)$ |
| $N_{\mathrm{eff}}$ | Effective channel count (Landauer-type) | dimensionless. $\sum_\alpha T_\alpha$ |
| $c$ | Wave propagation speed | m/s |
| $L$ | Domain length (1D Dirichlet problem) | m |
| $k_n$ | Spatial wavenumber $k_n = n\pi/L$ | rad/m |
| $\psi_n(x)$ | Spatial eigenfunction (site mode). $\sin(k_n x)$ | |
| $q_n(t)$ | Temporal mode amplitude. Damped-oscillator solution $e^{-\gamma t}\sin(\omega t)$ | |

---

## Premises [P1]–[P4b]

Structural conditions used in the capacity derivation. Labels follow Article 1.

| Label | Name | Content |
|-------|------|---------|
| [P1] | Harmonicity | Frequency $\omega_n$ is independent of energy $E_n$ |
| [P2] | Weak coupling / bilinearity | Coupling does not shift mode frequencies. Flux is first-order in each mode's energy |
| [P3] | Confinement | Boundary conditions on a finite domain produce a discrete spectrum |
| [P4a] | Factorizability | $k_{nm} = h(\omega_n) \cdot h(\omega_m)$ (separable into per-mode factors) |
| [P4b] | UV energy convergence | $E_n$ does not diverge as $\omega_n \to \infty$ |

[P1]–[P3] restrict the flux candidates to three discrete solutions ($r \in \{0, 1, \infty\}$). [P4b] eliminates the UV-divergent $r = \infty$ branch. [P4a] excludes $r = 1$, selecting $r = 0$ ($C = 1/f$).

---

## Capacity and Density

Premises: [P1]–[P3], [P4a], [P4b]

Master capacity selection (`MasterTheorem.master_capacity_selection`):

$$
C_n = \frac{1}{\omega_n}
$$

Coefficient converting mode energy to acoustic density. Higher-frequency modes have smaller capacity: the same energy yields a higher density.

Acoustic density:

$$
\rho_n = E_n \omega_n
$$

Driving variable of the DDD equation. At equilibrium, $\rho_n = T$ uniformly across all modes. The term "density" reflects that it measures the degree to which a mode is filled with energy.

Nonlinear zero-flux condition (`NonlinearCapacity.zero_flux_NL`):

$$
\rho_n^{\mathrm{NL}} = E_n \omega_n (1 + \beta E_n)
$$

Nonlinear density including amplitude-dependent correction. Arises when [P1] (harmonicity) is relaxed. Reduces to the linear theory as $\beta \to 0$.

Linear + quadratic decomposition (`NonlinearSpatialExtension.rho_nl_linear_plus_quadratic`):

$$
\rho_n^{\mathrm{NL}} = E_n \omega_n + \beta \omega_n E_n^2
$$

Separates nonlinear density into the linear part (tracked by DDD) and the quadratic correction (discarded by DDD).

---

## DDD ODE

No premises. All results below are algebraic consequences of $k > 0$, $\omega_n > 0$.

Two-mode DDD dynamics (`DDDynamics`):

$$
\frac{dE_1}{dt} = -k(\rho_1 - \rho_2), \quad \frac{dE_2}{dt} = +k(\rho_1 - \rho_2)
$$

Energy flows in proportion to the acoustic-density difference $\Delta\rho$: from the higher-density mode to the lower-density mode.

Energy conservation (`DDDynamics.energy_conservation`):

$$
\frac{dE_1}{dt} + \frac{dE_2}{dt} = 0
$$

Total energy is conserved in a lossless system.

$N$-mode energy conservation (`DDDynamics.energy_conservation_n`):

$$
\sum_i \sum_j J(i,j) = 0 \quad \bigl(\text{given } J(i,j) = -J(j,i)\bigr)
$$

The total of pairwise-antisymmetric fluxes vanishes for any $N$-mode system. Derived via $S = -S$ implies $S = 0$.

Equilibrium distribution (`DDDynamics.equilibrium_distribution`):

$$
E_n^{\mathrm{eq}} = \frac{T}{\omega_n}
$$

Energy per mode under density equalization $\rho_n = T$. Higher-frequency modes carry less energy at equilibrium.

Lyapunov algebraic structure (`DDDynamics.lyapunov_algebraic`):

$$
\frac{d(\Delta\rho)^2}{dt} = -2k(\omega_1 + \omega_2)(\Delta\rho)^2
$$

The time derivative of the squared density difference is non-positive, derived algebraically.

Equilibrium characterization (`DDDynamics.lyapunov_zero_iff_equilibrium`):

$$
\frac{d(\Delta\rho)^2}{dt} = 0 \iff \Delta\rho = 0
$$

The Lyapunov derivative vanishes only at equilibrium.

Stability bound (`DDDynamics.exponential_decay_bounded`):

$$
|\Delta\rho_0 \cdot e^{-\lambda t}| \le |\Delta\rho_0| \quad (t \ge 0,\; \lambda > 0)
$$

$\lambda = k(\omega_1 + \omega_2)$ is the relaxation rate. The density difference never exceeds its initial value.

Asymptotic stability (`DDDynamics.density_difference_decays`):

$$
\Delta\rho_0 \cdot e^{-\lambda t} \to 0 \quad (t \to \infty,\; \lambda > 0)
$$

The density difference converges to zero exponentially. Proved via `Filter.Tendsto`.

---

## Coupling Transform

No premises. Algebraic identities under $f \neq 0$.

Formulas for converting the damping rate $\gamma$ (loss constant in mode space) to the DDD coupling constant $k$ (transport rate in density space). The identity $k = \gamma/f$ follows algebraically from $\rho = Ef$; applying this transform to known loss models reveals the frequency structure of $k$ in density space.

Effective coupling constant (`AlgebraicIdentities.k_eff_identity`):

$$
k_{\mathrm{eff}} = \frac{\gamma}{f}
$$

$C = 1/f$ introduces a structural $1/f$ factor between $\gamma$ and $k$. Equivalently, $\gamma E = k\rho$.

Power-law constant-coupling condition (`CouplingTransform.powerlaw_constant_iff_alpha_eq_one`):

$$
k = \text{const} \iff \alpha = 1
$$

For $\gamma \propto \omega^\alpha$, we have $k \propto \omega^{\alpha-1}$. Only $\alpha = 1$ (frequency-proportional loss) gives frequency-independent $k$.

Kelvin–Voigt internal loss gives constant coupling (`CouplingTransform.kelvin_voigt_gives_constant_k`):

$$
k_{\mathrm{int}} = 4\pi\sigma_1
$$

When $\gamma = 4\pi\sigma_1 f$ ($\alpha = 1$), $k$ is a frequency-independent constant. Corresponds to internal viscous damping.

Coupling from quality factor (`CouplingTransform.k_of_quality_factor`):

$$
k = \frac{\pi}{Q}
$$

Derived from $\gamma = \pi f / Q$. Higher $Q$ (lower loss) gives smaller $k$.

Additivity of the coupling transform (`CouplingTransform.k_of_gamma_additive`):

$$
k(\gamma_1 + \gamma_2) = k(\gamma_1) + k(\gamma_2)
$$

Independent loss mechanisms compose additively in density space.

---

## LCAM Channel Transmission

No premises. Analysis under $s_\alpha \in [0, 1]$.

LCAM (Linear Combination of Acoustic Modes) applies when two subsystems with discrete modes (e.g. string and soundboard) are coupled. Hybrid modes $\Phi_\alpha = \sum_j c_{\alpha j} \phi_j$ are constructed as linear combinations of site modes $\phi_j$. The problem reduces to the eigenvalue problem of the coupling matrix $H$, sharing the same mathematical structure as LCAO.

$s_\alpha = \sum_{n \in A} |c_{\alpha n}|^2$ is the fraction of hybrid mode $\alpha$'s energy attributable to subsystem A's site modes. In string–soundboard systems, this is called stringiness.

LCAM transmission (`ChannelTransmission.T_lcam`):

$$
T_\alpha = 4\, s_\alpha (1 - s_\alpha), \quad s_\alpha \in [0, 1]
$$

Energy transmission through hybrid mode $\alpha$. Pure site modes ($s = 0$ or $1$) give $T = 0$; perfectly hybridized modes ($s = 1/2$) give $T = 1$.

Transmission symmetry (`ChannelTransmission.T_symmetric`):

$$
T(s) = T(1 - s)
$$

Swapping the contributions of subsystem A and B leaves the transmission unchanged. In a string–soundboard system this corresponds to exchanging $s$ and $1-s$.

Uniqueness of maximum transmission (`ChannelTransmission.T_max_unique`):

$$
T = 1 \iff s = \frac{1}{2}
$$

Full transmission is achieved only by hybrid modes with equal contribution from both subsystems.

Upper bound on effective channel count (`ChannelCounting.neff_le_raw_count`):

$$
N_{\mathrm{eff}} = \sum_\alpha T_\alpha \le N
$$

The effective channel count cannot exceed the geometric channel count $N$. Landauer-type channel counting.

Effective channel factorization (`ChannelCounting.neff_factorization_full`):

$$
N_{\mathrm{eff}} = N \cdot \langle T \rangle
$$

Effective channels = channel count $\times$ mean transmission. When all modes have $s = 1/2$, $N_{\mathrm{eff}} = N$.

---

## Gauge Equivalence

No premises. Pure algebraic identities.

For a single-pathway flux, different choices of $(C, k)$ produce the same observable. The selection $C = 1/f$ is determined by [P1]–[P4], not by data fitting.

Algebraic decomposition of the flux (`GaugeEquivalence.flux_algebraic_decomposition`):

$$
E_n\omega_n - E_m\omega_m = \frac{\omega_n + \omega_m}{2}(E_n - E_m) + \frac{E_n + E_m}{2}(\omega_n - \omega_m)
$$

The DDD flux (LHS) decomposes into an SEA-like energy-difference term and a frequency-difference term. The latter vanishes at equal frequencies.

Capacity–coupling tradeoff (`GaugeEquivalence.capacity_k_tradeoff`):

$$
(\alpha + \Delta\alpha) + (\beta - \Delta\alpha) = \alpha + \beta
$$

Shifting the capacity power-law exponent shifts the coupling exponent in the opposite direction; the observable (total exponent) is invariant.

---

## Duality

No premises. Algebraic symmetry over the frequency parameter.

Frequency-inversion exchange (`Duality.L_becomes_X_under_inversion`):

$$
\omega \leftrightarrow \frac{1}{\omega} \quad \text{exchanges} \quad r = 0 \;\text{and}\; r = \infty
$$

The $r = 0$ (DDD) equilibrium $E\omega = T$ and the $r = \infty$ equilibrium $E/\omega = T$ are interchanged by frequency inversion.

Self-dual point (`Duality.r1_self_dual`):

$$
r = 1 \;\text{is self-dual}
$$

The $r = 1$ (SEA) equilibrium $E = T$ is invariant under $\omega \leftrightarrow 1/\omega$.

---

## Phase Averaging

No premises. Trigonometric integral identities.

MFP retains phase information (the oscillatory structure of $e^{-\gamma t}\sin\omega t$), while DDD tracks only energy (phase-averaged quantities). The following integral identities bridge the two.

Period integral of $\sin^2$ (`PhaseAveraging.integral_sin_sq_period`):

$$
\int_0^{2\pi} \sin^2\theta\, d\theta = \pi
$$

Orthogonality of $\sin$ and $\cos$ (`PhaseAveraging.integral_sin_mul_cos_period`):

$$
\int_0^{2\pi} \sin\theta \cos\theta\, d\theta = 0
$$

Phase-averaged energy (`PhaseAveraging.phase_averaged_energy`):

$$
\frac{1}{2\pi}\int_0^{2\pi}\!\bigl[(\gamma^2 + \omega^2)\sin^2\theta - 2\gamma\omega\sin\theta\cos\theta + \omega^2\cos^2\theta\bigr]\,d\theta = \omega^2 + \frac{\gamma^2}{2}
$$

Averaging the MFP energy integrand over one phase cycle yields the DDD energy. Oscillating components cancel.

Cross-mode decomposition (`PhaseAveraging.cross_mode_decomposition`):

$$
\sin(\omega_n t)\sin(\omega_m t) = \frac{1}{2}\bigl[\cos((\omega_n - \omega_m)t) - \cos((\omega_n + \omega_m)t)\bigr]
$$

Product-to-sum decomposition into sum/difference frequencies. Basis for cross-mode time-average vanishing at the beat period.

---

## MFP Mode Expansion

No premises. Trigonometric identities and algebra under $c \neq 0$, $L \neq 0$.

MFP expands the wave field as $G(x,t) = \sum_n q_n(t)\psi_n(x)$ and evolves each $q_n(t)$ analytically as a damped oscillator. The insight that superposition of standing waves produces wavefront propagation is the origin of MFP.

Standing-to-traveling wave decomposition (`StandingTraveling.standing_wave_decomposition`):

$$
\cos(kx)\cos(\omega t) = \frac{1}{2}\bigl[\cos(kx - \omega t) + \cos(kx + \omega t)\bigr]
$$

A standing wave is the superposition of two counter-propagating traveling waves. Sums of standing waves produce macroscopic wavefront propagation.

Beat period equals round-trip time (`StandingTraveling.beat_period_eq_round_trip`):

$$
T_{\mathrm{beat}} = \frac{2L}{c}
$$

The beat period of adjacent modes equals the wave round-trip time. Sets the temporal resolution floor for MFP.

Packet width (`StandingTraveling.packet_width`):

$$
\Delta x = \frac{2L}{N}
$$

Spatial resolution achievable by superposition of $N$ modes.

PDE residual vanishing (`ModeExpansion.pde_residual_vanishes`):

Given eigenfunction property $L\psi = \lambda\psi$ and temporal ODE satisfaction, the PDE residual of $q(t)\psi(x)$ vanishes. Algebraic proof that each mode-expansion term satisfies the wave equation.

Dispersion relation (`ModeExpansion.dispersion_sq`):

$$
\omega^2 = c^2 k^2
$$

Relates spatial wavenumber $k$ to angular frequency $\omega$. Combined with confinement $k_n = n\pi/L$, yields the discrete spectrum.

Finite-dimensional eigenspace completeness (`ModeExpansion.findim_eigenspaces_span_all`):

For finite-dimensional self-adjoint operators, eigenspaces span the entire space without compactness assumptions. Combined with PDE residual vanishing, this establishes mode-expansion / wave-equation equivalence in finite dimensions.

---

## 1D Dirichlet Spectrum

No premises. Eigenvalue theory under $L > 0$, $n > 0$.

Explicit computation of eigenmodes for Dirichlet boundary conditions (fixed endpoints) on $[0, L]$. No Rellich–Kondrachov needed.

Eigenvalue (`DirichletSpectrum1D.dirichlet_ev`):

$$
\lambda_n = \left(\frac{n\pi}{L}\right)^2
$$

The $n$-th eigenvalue. Angular frequency via $\omega_n^2 = c^2\lambda_n$.

Orthogonality ($n \ne m$) (`DirichletSpectrum1D.dirichlet_orthogonality`):

$$
\int_0^L \sin\!\left(\frac{n\pi x}{L}\right)\sin\!\left(\frac{m\pi x}{L}\right)\,dx = 0
$$

Different modes have zero inner product. This allows mode-expansion coefficients to be determined independently.

Normalization (`DirichletSpectrum1D.dirichlet_normalization`):

$$
\int_0^L \sin^2\!\left(\frac{n\pi x}{L}\right)\,dx = \frac{L}{2}
$$

Norm of each eigenfunction. $\sqrt{2/L}\,\sin(n\pi x/L)$ forms an orthonormal basis.

Eigenvalue gap (`DirichletSpectrum1D.dirichlet_ev_gap`):

$$
\lambda_{n+1} - \lambda_n = (2n + 1)\left(\frac{\pi}{L}\right)^2
$$

The gap between adjacent eigenvalues grows linearly in $n$. Higher-frequency modes are more widely spaced.

---

## MFP-DDD Consistency

Phase-averaged MFP energy agrees with DDD energy (`EquivalenceFramework.ddd_mfp_phase_average_agreement`):

$$
\frac{1}{2\pi}\!\left[(\gamma^2 + \omega^2)\!\int_0^{2\pi}\!\sin^2\theta\,d\theta - 2\gamma\omega\!\int_0^{2\pi}\!\sin\theta\cos\theta\,d\theta + \omega^2\!\int_0^{2\pi}\!\cos^2\theta\,d\theta\right] = \omega^2 + \frac{\gamma^2}{2}
$$

Averaging the phase-resolved MFP energy over one period yields the energy tracked by DDD. Proved by substituting the period-integral results from PhaseAveraging ($\int\sin^2 = \pi$, $\int\cos^2 = \pi$, $\int\sin\cos = 0$). This theorem bridges MFP and DDD.

---

## Spectral Theorem

Premise: compact self-adjoint operator $T$.

Eigenspaces of a compact self-adjoint operator span $H$ (`Completeness.eigenspaces_complete`).

Functional-analytic guarantee that mode expansion is complete: any $v \in H$ can be expressed as a (possibly infinite) linear combination of eigenvectors.

In finite dimensions, compactness is not needed (`Completeness.eigenspaces_complete_findim`).

Corresponds to the basic linear-algebra fact that self-adjoint matrices are always diagonalizable.

Eigenspaces are mutually orthogonal (`Completeness.eigenspaces_orthogonal`).

Eigenvectors for distinct eigenvalues have zero inner product. Mathematical foundation for energy independence across modes.

Eigenvalues are real (`Completeness.eigenvalues_conjugate_invariant`).

Guarantees that $\omega_n^2$ is real, yielding physically observable frequencies.

### 1D Compactness Bridge

1D spectral package (`Completeness.compact_self_adjoint_spectral_package`):

Packages eigenspace completeness and finite-dimensionality of nonzero eigenspaces into a single theorem for compact self-adjoint operators. In 1D, `IsCompactOperator` follows from Arzelà–Ascoli (no Rellich–Kondrachov needed), so this package applies directly.

1D Dirichlet spectral bridge (`Completeness.dirichlet_spectral_bridge`):

$$
c^2 \cdot \left(\frac{n\pi}{L}\right)^2 = \left(\frac{n\pi c}{L}\right)^2 \quad \text{and} \quad \left(\frac{n\pi}{L}\right)^2 > 0
$$

Combines the dispersion relation and positivity of eigenvalues into a single theorem. This is the connection point between the abstract side (`eigenspaces_complete`: spectral theorem for compact self-adjoint operators) and the concrete side (`dirichlet_dispersion`: explicit 1D Dirichlet eigenvalue formula).
