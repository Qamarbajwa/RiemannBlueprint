# RiemannBlueprint (Lean 4.35.0)

**Author:** Qamar Munawer (Brandenburg University of Technology Cottbus–Senftenberg)  
**MSC 2020:** Primary `11M26`; Secondary `46E20`, `68V20`

## Project Status & AI Disclosure

1. **AI-Assisted Exploration:** This repository is a standalone, AI-assisted Lean 4 formalization exploration developed by the author using LLM proof assistants.
2. **Closed Mathlib Pull Requests (Nov 2026):** Between 16 and 18 November 2026, 15 pull requests derived from this repository were opened against `leanprover-community/mathlib4`, labelled `LLM-generated`, and closed by Mathlib triage without merging because they did not meet Mathlib's community standards for human-authored learning and AI use.
3. **Decommissioned Automation & No Pending PRs:** All automated PR staging scripts and `Qamarbajwa/mathlib4` `feat/*` fork branches have been permanently removed, Zenodo publishing is frozen, and no further pull requests will be submitted to Mathlib without prior human mentorship and manual authorship. None of the modules here are staged for or claimed to be ready for upstream `mathlib4`.

## Repository Structure

### Part I — Classical Analytic Number Theory Formalizations

- **Littlewood's (1912) Forward Theorem (`LittlewoodForward.lean`):** Unconditional proof that the Mertens bound $M(x) = O_\varepsilon(x^{1/2+\varepsilon})$ implies $\zeta(s)$ has a holomorphic right inverse (and hence no zeros) on $\operatorname{Re}(s) > 1/2$, using Mathlib's `LSeries_eq_mul_integral'`, `mellin_differentiableAt_of_isBigO_rpow`, and `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
- **Hardy's (1914) Theorem (`MathlibPR_HardyZeros.lean`, `Modules/HardyCriticalLineZeros.lean`):** Unconditional proof of `infinite_criticalLine_zeros` ($\{t \in \mathbb{R} : \zeta(1/2 + it) = 0\}$ is infinite) via `hardyZ` sign changes, `HardyPsiAndThetaKernel.lean`, `HardyThetaIteratedDeriv.lean`, `CompletedZetaStripDecay.lean`, `HardyGContourAndMellin.lean`, and `HardyEvenMomentIdentity.lean`.
- **De la Vallée Poussin (1899) Zero-Free Region (`MathlibPR_ZeroFreeRegion.lean`, `Modules/ZetaZeroFreeRegion.lean`):** Unconditional proof of `deLaValleePoussin_zero_free_region_unconditional` ($\zeta(s) \neq 0$ for $\operatorname{Re}(s) > 1 - c / \ln^9(|s.\mathrm{im}| + 2)$ and $|s.\mathrm{im}| \ge 2$), built on Mathlib's `norm_LFunction_product_ge_one` and Cauchy derivative estimates.

### Part II — Finite-$N$ Báez-Duarte / Vasyunin Cotangent Calculations and Conditional Reductions

- **`RiemannBlueprint/Modules/` (`64` modular Lean 4 files) and Matrix / Bridge Files:**
  - **Identity-Matrix Gaussian Elimination & Projection Residual (`MatrixFactorizationAndHalfObservation.lean`):** Formalizes $\mathbf{D}_M \mathbf{D}_M^{-1} = \mathbf{I}_M$, forward Gaussian elimination $\mathbf{D}_M \mu = e_1$, the unit lower-triangular factorization $\mathbf{F}_M = \mathbf{\Sigma}_M \mathbf{D}_M$ ($\mathbf{F}_M \mathbf{F}_M^{-1} = \mathbf{I}_M$), pivot-row elimination $r_1 = 0$ under $c_1 = -1$, nullspace basis matrix $T_{N,N-2}$, Cholesky whitening $\widetilde{\mathbf{\Psi}}_N^T \widetilde{\mathbf{\Psi}}_N = \mathbf{I}_{N-2}$, wavefunction Gram factorization $M_{M,N} = \mathbf{\Omega}_{M,N}^T \mathbf{\Omega}_{M,N}$, and the projection residual $\langle b | (\mathbf{I} - \widehat{\Pi}_N) | b \rangle = 1 - \sum_{k=3}^N \rho_k^2 / s_k \ge 0$.
  - **Finite-$N$ Algebraic Computations ($N = 3, 4, 5, 6$):** Exact evaluations of the finite-dimensional quadratic forms on the nullspace manifold (`VasyuninIntegral.lean`, `VasyuninSmoothAndCotDefs.lean`, `MobiusCandidateFourCert.lean`, `VariationalOptimumFour.lean`, `DirichletOptFourCert.lean`, `DipoleGramFiveCert.lean`, `CotangentSixReciprocity.lean`, etc.).
  - **Cotangent Symmetries & Conditional Reductions:** Known cotangent periodicities/symmetries (`UniversalCotangentSymmetries.lean`, `UnitPartitionHomogenization.lean`, `SuperdiagonalAndOrthogonalTriple.lean`, `PointwiseContinuityAndPeriodicity.lean`, `HarmonicCellL2QuadratureAndPrimeJumps.lean`, `PeriodicL2CellSumCompression.lean`, `DoubleConeL2FoldingAndFlux.lean`, `EuclideanExhaustionTailBound.lean`) and conditional reductions whose asymptotic $N \to \infty$ hypotheses ($\widehat{\Pi}_N \to \mathbf{I}$ on $|b\rangle$, `MertensBound`, `TitchmarshMellinProperty`) carry the full analytic difficulty of the Nyman–Beurling problem.

## Prior Art & Ecosystem Credit

- **`leanprover-community/mathlib4`:** Already provides `riemannZeta_ne_zero_of_one_le_re` ($\operatorname{Re}(s) \ge 1$) and `norm_LFunction_product_ge_one` (the 3-4-1 trigonometric inequality for Dirichlet $L$-functions in `Mathlib.NumberTheory.LSeries.Nonvanishing`), as well as `LSeries_eq_mul_integral'` and `mellin_differentiableAt_of_isBigO_rpow`. Mathlib does not currently contain a classical strip zero-free region ($\sigma > 1 - c/\log^k|t|$), Hardy's 1914 theorem, or Littlewood's forward theorem.
- **`AlexKontorovich/PrimeNumberTheoremAnd`:** Already formalized the $\log^9 |t|$ zero-free region (`ZetaZeroFree9` in `PrimeNumberTheoremAnd/ZetaBounds.lean`: $1 - A / \log^9 |t| \le \sigma < 1$, $3 < |t|$) using the 3-4-1 inequality and a $\log^2 |t|$ derivative/strip bound. `deLaValleePoussin_zero_free_region_unconditional` here arrives at the same $\log^9$ exponent via the analogous 3-4-1 + Cauchy horizontal Lipschitz route (with $\log(|t|+2)^9$ for $|t| \ge 2$). `PrimeNumberTheoremAnd` is the established ecosystem prior art for the $\log^9$ zero-free region. See [`PRIOR_ART_AND_VERIFICATION_AUDIT.md`](../PRIOR_ART_AND_VERIFICATION_AUDIT.md) for full details.

## Build & Verify

```bash
lake build RiemannBlueprint
```

- **Study Companion:** [`STUDY_GUIDE_LITTLEWOOD_FORWARD_LINE_BY_LINE.md`](../STUDY_GUIDE_LITTLEWOOD_FORWARD_LINE_BY_LINE.md)
- **Prior-Art & Axiom Audit:** [`PRIOR_ART_AND_VERIFICATION_AUDIT.md`](../PRIOR_ART_AND_VERIFICATION_AUDIT.md)
- **Companion Notes Repository:** `https://github.com/Qamarbajwa/riemann-lean4-papers`
- **Historical Zenodo Concept Archive (Frozen):** [`10.5281/zenodo.24150107`](https://doi.org/10.5281/zenodo.24150107)


### Part III — Exterior Wedge, Half-Dimension Split, & 10-Theorem Compression Booster (`v3.4.0-rosetta`)

- **40 Root Imports (`3,137` Lake jobs, zero `sorry`, `[propext, Classical.choice, Quot.sound]`):** Modules `PrimeIdentityExteriorWedge.lean`, `EuclidOppositeSideExclusion.lean`, `HalfDimensionIdentitySplit.lean`, `RiemannSphereDoubleCover.lean`, and `PrimeBinaryCompressionBooster.lean` (10 zero-axiom theorems).
- **100-Digit `flint.arb` Schur Trigonometry (`N = 2..1000`, `test_prime_dimensions.py` Tests 1–12):**
  - `N = 211`: $E_{\mathrm{dir}} = 0.008629$, $\Theta = 5.330^\circ$, $t_{\mathrm{half}} = 0.046547$, $\beta_{\min} - 1/2 = 0.00108331$.
  - `N = 500`: $E_{\mathrm{dir}} = 0.007427$, $\Theta = 4.944^\circ$, $t_{\mathrm{half}} = 0.043170$, $\beta_{\min} - 1/2 = 0.00093181$.
  - `N = 1000`: $E_{\mathrm{dir}} = 0.006561$, $\Theta = 4.646^\circ$, $t_{\mathrm{half}} = 0.040568$, $\beta_{\min} - 1/2 = 0.00082287$ (`4.45x` $\{0,1\}$ compression speedup, `62.99%` memory savings, `arb100` pinch residual $\le 5.05 \times 10^{-100}$).
- **Zero-Axiom Finite-Dimensional & Parameterized Bridge Certification:** All finite-cutoff bounds ($N \le 1000$) are unconditional in Lean 4, isolating the asymptotic $N \to \infty$ limit inside explicit parameterized hypotheses. In this work, ai is being used as a tool by Qamar Munawer (Brandenburg University of Technology Cottbus–Senftenberg).
