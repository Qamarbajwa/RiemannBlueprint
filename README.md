# RiemannBlueprint (Lean 4.35.0)

**Author:** Qamar Munawer (Brandenburg University of Technology Cottbus–Senftenberg)  
**Epistemic Invariant:** `NO_RH_PROOF = TRUE` — Formalizes classical conditional equivalences (`Littlewood`, `Nyman–Beurling`, `Mellin–Nyman–Beurling`, `Von Koch`, reciprocal zeta holomorphy), unconditional classical theorems (`de la Vallée Poussin` 1899 zero-free region, `Hardy` 1914 infinitely many critical-line zeros), exact identities on the Báez–Duarte affine manifold, and prime–composite audit bridges. **No unconditional proof of the Riemann Hypothesis is claimed.**

## Structure & Highlights

- **`RiemannBlueprint/UpstreamPRs/` (`36` atomic `mathlib4` PR modules, Waves 1–5):**
  - Wave 1: `UpstreamPR_1A` (critical-line IVT & 3-4-1 kernel), `UpstreamPR_3A` (Vasyunin $L^1/L^2$ integrals), `UpstreamPR_4A` (affine Lagrange projection).
  - Wave 2: `UpstreamPR_1B`–`1F` (unconditional de la Vallée Poussin zero-free region).
  - Wave 3: `UpstreamPR_3B`–`3H` & `4B`–`4M` (Vasyunin cross-integral, harmonic wavelets, cumulative dipoles, exact $N=4$ global KKT optimum $((19+\sqrt{3})/72)\pi$, and dipole Gram diagonal positivity).
  - Wave 4: `UpstreamPR_2B`–`2G` (unconditional Hardy 1914 critical-line zeros).
  - Wave 5: `UpstreamPR_5A`–`5C` (reciprocal zeta holomorphy, unconditional Von Koch forward theorem, bidirectional Mellin Nyman–Beurling converse).
- **Zenodo Hub 07 DOIs:** `10.5281/zenodo.24328027` (`v3.0.0`) / `10.5281/zenodo.24329861` (`v3.0.1`), Concept DOI `10.5281/zenodo.24150107`.
- **Companion Papers Repository:** `https://github.com/Qamarbajwa/riemann-lean4-papers`
- **Open Upstream `mathlib4` PRs (Wave 1):** `#46127`, `#46128`, `#46129`.

## Build & Verify
```bash
lake build RiemannBlueprint
```
