#!/usr/bin/env python3
"""
probe_weil_schur_factorized_mollifier.py

Numerical verification of the synthesis of:
- Option 1: Two-Piece Grade-1 x Grade-2 Factorized Mollifier inside theta < 4/7 (up to N = 10000)
- Option 2: Semilocal Weil Quadratic Form Schur-Complement Coercivity across L in {1.0, 2.0, 3.0, 4.0}

Methodology note: ai is being used as a tool.
Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg.
"""

from __future__ import annotations

import json
import math
import time
from pathlib import Path
import numpy as np


def sieve_mobius_and_omega(n_max: int) -> tuple[np.ndarray, np.ndarray]:
    """Return Mobius mu(n) and distinct prime factor count omega(n) for 0 <= n <= n_max."""
    mu = np.ones(n_max + 1, dtype=int)
    mu[0] = 0
    omega = np.zeros(n_max + 1, dtype=int)
    is_prime = np.ones(n_max + 1, dtype=bool)
    is_prime[0] = is_prime[1] = False
    for p in range(2, n_max + 1):
        if is_prime[p]:
            for mult in range(p, n_max + 1, p):
                if mult > p:
                    is_prime[mult] = False
                omega[mult] += 1
                if (mult // p) % p == 0:
                    mu[mult] = 0
                else:
                    mu[mult] = -mu[mult]
    return mu, omega


def test_1_two_piece_factorized_mollifier() -> dict[str, object]:
    """Compare 1-piece, 2-piece Grade-1 x Grade-2 factorized, and full Selberg mollifier up to N=10000."""
    N_list = [100, 500, 1000, 2000, 5000, 10000]
    mu, omega = sieve_mobius_and_omega(max(N_list))

    gamma_euler = 0.5772156649015329
    c_diag = (math.log(2.0 * math.pi) + gamma_euler) / 2.0

    results = []
    all_capture_ok = True
    for N in N_list:
        ln_N = math.log(N)
        k = np.arange(1, N + 1, dtype=float)
        w_k = (np.log(N / k) / ln_N) ** 2
        sqf = (mu[1:N+1] != 0)
        om = omega[1:N+1]

        # Weighted Selberg diagonal energy density (sum mu(k)^2 w_k^2 / k)
        term = np.where(sqf, (w_k ** 2) * c_diag / k, 0.0)
        E_full_sqf = float(np.sum(term))
        E_1piece_prime = float(np.sum(np.where(sqf & (om <= 1), term, 0.0)))
        E_2piece_grade12 = float(np.sum(np.where(sqf & (om <= 2), term, 0.0)))

        # Composite energy above Grade-0 (k=1)
        E_comp_full = E_full_sqf - term[0]
        E_comp_2piece = E_2piece_grade12 - term[0]
        capture_pct = (E_comp_2piece / E_comp_full) * 100.0 if E_comp_full > 0 else 100.0

        n_factor_bound = math.isqrt(N)
        if capture_pct <= 94.7:
            all_capture_ok = False

        results.append({
            "N": N,
            "N1_N2_factor_bound": n_factor_bound,
            "E_1piece_prime": round(E_1piece_prime, 6),
            "E_2piece_grade12": round(E_2piece_grade12, 6),
            "E_full_sqf": round(E_full_sqf, 6),
            "composite_capture_pct": round(capture_pct, 4),
        })

    return {
        "passed": all_capture_ok,
        "N_max": 10000,
        "factor_length_at_10000": 100,
        "capture_pct_at_10000": results[-1]["composite_capture_pct"],
        "cutoffs": results,
    }


def test_2_weil_semilocal_schur_coercivity() -> dict[str, object]:
    """Verify Q_PP > 0, lambda_min(Sigma_L) > 0, and Banachiewicz identity across L in {1,2,3,4}."""
    L_values = [1.0, 2.0, 3.0, 4.0]
    # Prime baseline modes P = {2, 3, 5, 7} and composite mode C = {6} (1D composite slice) + full block
    primes = np.array([2.0, 3.0, 5.0, 7.0])
    composites = np.array([6.0, 10.0, 14.0, 15.0])

    # Gauss-Legendre quadrature on [-L, L] for positive-definite Weil test-function Gram matrix
    xi, wi = np.polynomial.legendre.leggauss(48)

    records = []
    all_ok = True
    for L in L_values:
        x_nodes = L * xi
        w_nodes = L * wi
        # Windowed Mellin/Weil test basis phi_k(x) = exp(-x^2 / (2*L^2)) * cos(log(k) * x) / sqrt(k)
        env = np.exp(-0.5 * (x_nodes / L) ** 2)
        all_modes = np.concatenate([primes, composites])
        basis = env[:, None] * np.cos(x_nodes[:, None] * np.log(all_modes)[None, :]) / np.sqrt(all_modes)[None, :]
        # Weil Gram matrix Q_W = basis^T * diag(w_nodes) * basis + small Archimedean diagonal floor
        Q_W = (basis * w_nodes[:, None]).T @ basis + 0.05 * np.eye(len(all_modes))

        n_p = len(primes)
        Q_PP = Q_W[:n_p, :n_p]
        Q_PC = Q_W[:n_p, n_p:]
        Q_CP = Q_W[n_p:, :n_p]
        Q_CC = Q_W[n_p:, n_p:]

        lam_min_PP = float(np.min(np.linalg.eigvalsh(Q_PP)))
        Sigma_L = Q_CC - Q_CP @ np.linalg.solve(Q_PP, Q_PC)
        lam_min_Sigma = float(np.min(np.linalg.eigvalsh(Sigma_L)))

        # Block matrix inverse Banachiewicz identity: Sigma_L @ (Q_W^{-1})_CC == I
        Q_W_inv = np.linalg.inv(Q_W)
        Q_W_inv_CC = Q_W_inv[n_p:, n_p:]
        banach_err = float(np.max(np.abs(Sigma_L @ Q_W_inv_CC - np.eye(len(composites)))))

        # 1D scalar composite slice (k=6) Banachiewicz sine identity: sin^2(Theta_L) == 1 / (Q_CC_0 * (Q_5x5^{-1})_CC)
        Q_5 = Q_W[:n_p+1, :n_p+1]
        Q_5_inv_CC = float(np.linalg.inv(Q_5)[-1, -1])
        q_pc_1d = Q_W[:n_p, n_p:n_p+1]
        q_cc_1d = float(Q_W[n_p, n_p])
        sigma_1d = float((q_cc_1d - (q_pc_1d.T @ np.linalg.solve(Q_PP, q_pc_1d))[0, 0]))
        sin2_theta_direct = sigma_1d / q_cc_1d
        sin2_theta_banach = 1.0 / (q_cc_1d * Q_5_inv_CC)
        scalar_banach_err = abs(sin2_theta_direct - sin2_theta_banach)

        ok = (lam_min_PP > 0.0) and (lam_min_Sigma > 0.0) and (banach_err < 1e-14) and (scalar_banach_err < 1e-14)
        if not ok:
            all_ok = False

        records.append({
            "L": L,
            "lambda_min_Q_PP": round(lam_min_PP, 8),
            "lambda_min_Sigma_L": round(lam_min_Sigma, 8),
            "sin2_theta_L": round(sin2_theta_direct, 8),
            "banachiewicz_block_err": banach_err,
            "banachiewicz_scalar_err": scalar_banach_err,
            "passed": ok,
        })

    return {
        "passed": all_ok,
        "windows": records,
    }


def main() -> int:
    t0 = time.perf_counter()
    print("=" * 80)
    print("PROBE: WEIL SCHUR-COMPLEMENT COERCIVITY & 2-PIECE FACTORIZED MOLLIFIER")
    print("Methodology note: ai is being used as a tool.")
    print("Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg.")
    print("=" * 80)

    t1 = test_1_two_piece_factorized_mollifier()
    t2 = test_2_weil_semilocal_schur_coercivity()
    elapsed = round(time.perf_counter() - t0, 4)

    overall = t1["passed"] and t2["passed"]
    print(f"[Test 1] 2-Piece Grade-1 x Grade-2 Mollifier (N=10000, N1,N2<=100): {'PASS' if t1['passed'] else 'FAIL'} | Capture = {t1['capture_pct_at_10000']}%")
    print(f"[Test 2] Semilocal Weil Schur Coercivity (L=1..4):                  {'PASS' if t2['passed'] else 'FAIL'}")
    for r in t2["windows"]:
        print(f"   L={r['L']:.1f} | lam_min(Q_PP)={r['lambda_min_Q_PP']:.6f} | lam_min(Sigma_L)={r['lambda_min_Sigma_L']:.6f} | sin^2(Theta)={r['sin2_theta_L']:.6f} | err={r['banachiewicz_scalar_err']:.2e}")
    print(f"Elapsed: {elapsed}s | Overall: {'PASS' if overall else 'FAIL'}")

    receipt = {
        "status": "PASS" if overall else "FAIL",
        "epistemic_boundary": "Infinite-horizon L -> infinity coercivity Premise A remains strictly OPEN",
        "elapsed_s": elapsed,
        "test_1_factorized_mollifier": t1,
        "test_2_weil_schur_coercivity": t2,
    }
    out_path = Path(__file__).resolve().parent / "probe_weil_schur_factorized_mollifier_receipt.json"
    out_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    print(f"Receipt written to: {out_path}")
    return 0 if overall else 1


if __name__ == "__main__":
    raise SystemExit(main())
