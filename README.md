# RiemannBlueprint (Lean 4.35.0)

**Author:** Qamar Munawer (Brandenburg University of Technology Cottbus–Senftenberg)  
**Epistemic Invariant:** `NO_RH_PROOF = TRUE` — Formalizes classical conditional equivalences (`Littlewood`, `Nyman–Beurling`, `Mellin–Nyman–Beurling`, `Von Koch`, reciprocal zeta holomorphy), unconditional classical theorems (`de la Vallée Poussin` 1899 zero-free region, `Hardy` 1914 infinitely many critical-line zeros), exact identities on the Báez–Duarte affine manifold, and prime–composite audit bridges. **No unconditional proof of the Riemann Hypothesis is claimed.**

## Structure & Highlights

- **`RiemannBlueprint/UpstreamPRs/` (`53` self-contained, linter-verified modular Lean 4 formalization units, Waves 1–8):**
  - Wave 1: `UpstreamPR_1A` (critical-line IVT & 3-4-1 kernel), `UpstreamPR_3A` (Vasyunin $L^1/L^2$ integrals), `UpstreamPR_4A` (affine Lagrange projection).
  - Wave 2: `UpstreamPR_1B`–`1F` (unconditional de la Vallée Poussin zero-free region).
  - Wave 3: `UpstreamPR_3B`–`3H` & `4B`–`4M` (Vasyunin cross-integral, harmonic wavelets, cumulative dipoles, exact $N=4$ global KKT optimum $((19+\sqrt{3})/72)\pi$, and dipole Gram diagonal positivity).
  - Wave 4: `UpstreamPR_2B`–`2G` (unconditional Hardy 1914 critical-line zeros).
  - Wave 5: `UpstreamPR_5A`–`5C` (reciprocal zeta holomorphy, unconditional Von Koch forward theorem, bidirectional Mellin Nyman–Beurling converse).
  - Wave 6: `UpstreamPR_6A`–`6C` (completed zeta derivative antisymmetry & equipartition fulcrum, critical-line penetration barrier & strip defect Mellin coupling, prime–composite natural partition & critical-strip RH equivalence).
  - Wave 7: `UpstreamPR_7A`–`7D` (Mellin kernel $L^2$ energy identity, 4-segment rectangle contour subdivision, pure 4-point plaque anchor-drive cancellation, and diagonal/off-diagonal frontier split).
  - Wave 8: `UpstreamPR_8A`–`8J` (pure plaque Cauchy–Schwarz lower bound, Dirichlet-anchored $c_1=-1$ plaque positivity & unit-drive $L^2$ law, 2D discrete Abel telescoping kernel reduction, pure plaque / telescoped RH criteria, exact closed-form $(31/108)\pi$ $N=4$ Dirichlet optimum, closed-form $N=5$ dipole Gram entries, exact $N=6$ $\mathbb{Q}(\sqrt{3})$ decoupling $\widetilde{G}_{24}=0$, all-$N$ universal symmetries $K(k,2k)=0$, BBLR $C/\ln N$ decay bridge, and homogeneous unit-partition kernel `unitDefectEntry` simplex duality).
- **Zenodo Hub 07 DOI:** [`10.5281/zenodo.24329861`](https://doi.org/10.5281/zenodo.24329861) (Concept DOI [`10.5281/zenodo.24150107`](https://doi.org/10.5281/zenodo.24150107); earlier `v3.0.0` `10.5281/zenodo.24328027`)
- **CI & Citation:** Automated build via [`.github/workflows/lean_action_ci.yml`](./.github/workflows/lean_action_ci.yml) (`leanprover/lean-action@v1`) and [`CITATION.cff`](./CITATION.cff)
- **Companion Papers Repository (`Paper 0`, `Papers A–L`, `14` Live Zenodo Hubs):** `https://github.com/Qamarbajwa/riemann-lean4-papers` (Unified Master Review `Paper L`: [`10.5281/zenodo.24342101`](https://doi.org/10.5281/zenodo.24342101), prev [`10.5281/zenodo.24341718`](https://doi.org/10.5281/zenodo.24341718))
- **Standalone Archive & Fork Policy:** All `53` modules are maintained as standalone verifiable artifacts in `Qamarbajwa/RiemannBlueprint`, `Qamarbajwa/mathlib4` (`53` stacked `feat/*` fork branches), and Zenodo, with automated upstream `leanprover-community/mathlib4` PR/commenting disabled (`ALLOW_UPSTREAM_BOT_ACTIONS = False`). Earlier manual Wave 1 references: `#46127`, `#46128`, `#46129`.

## Build & Verify
```bash
lake build RiemannBlueprint
```
