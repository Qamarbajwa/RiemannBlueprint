"""
papers_rh_theorems.py

Aggregates all 9 Riemann Standalone Papers:
- Paper 00: Common-Person Relational Master Guide
- Paper T01: Numbers As Exterior Prime Identity Matrices & Grade-2 Semiprime Drop
- Paper T02: Identity Of One As Two Halves, Cholesky Whitening & Pi From Scratch
- Paper T03: Tripotent {0, 1} Mobius Projectors & 4.71x Square-Free Subspace Booster
- Paper T04: Higher-Dimensional Schur Trigonometry & Pythagorean Telescoping
- Paper T05: Weierstrass-Euclid Half-Dimension Pinch & Exclusion Disc
- Paper T06: Semiprime GCD Tare Sqrt-Multiplicity & BBLR Angle Pinch
- Paper T07: Lipschitz Continuity, Nested 4-Rosetta Intervals & Archimedean Squeeze
- Paper T08: Continuum Selberg Quadratic Mollifier & Bettin-Conrey Reciprocity
"""

from paper_00_common_person import PAPER_00
from papers_rh_theorems_part1 import PAPERS_PART1
from papers_rh_theorems_part2 import PAPERS_PART2

ALL_RIEMANN_PAPERS = [PAPER_00] + PAPERS_PART1 + PAPERS_PART2
