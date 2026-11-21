#!/usr/bin/env python3
"""
probe_constructive_finset_and_trig_basis.py (Audit Probe 25)

Verifies the constructive Finset, trigonometric basis, and prime-power
Schur trace identities certified in ConstructiveFinsetPrimeTailAndCosineBasisCert.lean:
1. Dirichlet cosine mode boundary vanishing: e_0(L/2) = 0, e_0(0) = 1.
2. Autocorrelation envelope evaluation: g_00(0) = 1, g_00(L) = 0.
3. Telescoping place-shift series: sum_{n=0}^{N-1} 1/((p_r+n)(p_r+n+1)) = 1/p_r - 1/(p_r+N) < 1/p_r.
4. Constructive first six primes trace sum: 11351/15015 ≈ 0.755977 < 1.0.

Author: Qamar Munawer
Affiliation: Brandenburg University of Technology Cottbus-Senftenberg
Methodology: ai is being used as a tool
Epistemic Status: Verified-Finite Constructive Finset & Trigonometric Basis (status: verified-finite).
All Clay Millennium Problems remain strictly OPEN.
"""

from __future__ import annotations

import json
import math
import sys
import numpy as np
from pathlib import Path
from fractions import Fraction

def run_probe_constructive_finset_and_trig_basis():
    # 1. Cosine boundary vanishing
    L = 10.0
    u_bdry = L / 2.0
    u_center = 0.0
    e_bdry = math.cos((2 * 0 + 1) * math.pi * u_bdry / L)
    e_center = math.cos((2 * 0 + 1) * math.pi * u_center / L)
    assert abs(e_bdry) < 1e-15, f"Expected 0 at boundary, got {e_bdry}"
    assert abs(e_center - 1.0) < 1e-15, f"Expected 1 at center, got {e_center}"

    # 2. Autocorrelation envelope
    omega = 1.25
    g_0 = (1.0 - 0.0 / L) * math.cos(omega * 0.0)
    g_L = (1.0 - L / L) * math.cos(omega * L)
    assert abs(g_0 - 1.0) < 1e-15
    assert abs(g_L) < 1e-15

    # 3. Telescoping place-shift series
    p_r = 17.0
    telescoping_records = []
    for N in [10, 50, 100, 1000]:
        n_arr = np.arange(N, dtype=float)
        terms = 1.0 / ((p_r + n_arr) * (p_r + n_arr + 1.0))
        num_sum = float(np.sum(terms))
        exact_closed = 1.0 / p_r - 1.0 / (p_r + float(N))
        diff = abs(num_sum - exact_closed)
        assert diff < 1e-14
        assert exact_closed < 1.0 / p_r
        telescoping_records.append({
            "N": N,
            "numerical_sum": num_sum,
            "exact_closed": exact_closed,
            "bound_1_over_pr": 1.0 / p_r,
            "diff": diff
        })

    # 4. First six primes trace sum
    primes = [2, 3, 5, 7, 11, 13]
    frac_terms = [Fraction(1, p * (p - 1)) for p in primes]
    exact_sum = sum(frac_terms)
    expected_sum = Fraction(11351, 15015)
    assert exact_sum == expected_sum
    assert exact_sum < 1

    receipt = {
        "title": "Constructive Finset & Trigonometric Basis Probe (Audit Probe 25)",
        "author": "Qamar Munawer",
        "affiliation": "Brandenburg University of Technology Cottbus-Senftenberg",
        "methodology": "ai is being used as a tool",
        "status": "PASS",
        "verified": True,
        "epistemic_lock": {
            "all_four_clay_millennium_problems_open": True,
            "status": "verified-finite"
        },
        "metrics": {
            "cosine_boundary_val": e_bdry,
            "cosine_center_val": e_center,
            "autocorr_center": g_0,
            "autocorr_boundary": g_L,
            "telescoping_records": telescoping_records,
            "first_six_primes_exact_fraction": str(exact_sum),
            "first_six_primes_float": float(exact_sum),
            "schur_budget_margin": float(1 - exact_sum)
        }
    }

    out_path = Path(r"d:\Comfy UI\rheihman hypothesis\scripts\probe_constructive_finset_and_trig_basis_receipt.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    print(f"[OK] RH Probe 25 Receipt written to {out_path} (status: PASS, verified: True)")
    return receipt

if __name__ == "__main__":
    run_probe_constructive_finset_and_trig_basis()
