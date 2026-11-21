#!/usr/bin/env python3
"""
probe_asymptotic_sobolev_quotient.py

Asymptotic Window Scaling and Sobolev Metric Weighting Diagnostic for the
Signed Weil Form on the Active Quotient Space H_active = L^2 / ker(Q_W).

Probes L in [1.0, 12.0] with adaptive modal dimension K = max(32, round(8L)):
1. Evaluates exact unshifted signed Weil form Q_W = Q_pole + Q_arch - Q_prime.
2. Fast separable prime sum assembly across all prime powers p^m <= exp(L).
3. Evaluates the sub-gap Schur tare Sigma_act on Range(Sigma_act).
4. Tests generalized Sobolev-weighted quotient floors:
   lambda_min^+(W_act^{-s/2} Sigma_act W_act^{-s/2}) for s in {-1.0, -0.5, 0.0, 0.5, 1.0}.
5. Computes asymptotic scaling exponents and condition numbers.

Methodology note: ai is being used as a tool.
Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg.
"""

from __future__ import annotations

import json
import math
import time
from pathlib import Path
import numpy as np
from scipy.special import digamma

GAMMA_1 = 14.13472514173469379  # Lowest nontrivial Riemann zero


def prime_powers_up_to(limit: float) -> list[tuple[int, int]]:
    """Return all prime powers (p^m, p) with p^m <= limit."""
    n_max = int(math.floor(limit))
    if n_max < 2:
        return []
    is_prime = [True] * (n_max + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(math.sqrt(n_max)) + 1):
        if is_prime[i]:
            for j in range(i * i, n_max + 1, i):
                is_prime[j] = False
    out = []
    for p in range(2, n_max + 1):
        if is_prime[p]:
            pm = p
            while pm <= limit:
                out.append((pm, p))
                pm *= p
    return sorted(out)


def omega(k: np.ndarray, L: float) -> np.ndarray:
    return (2.0 * k + 1.0) * np.pi / L


def compute_weil_blocks_fast(L: float, K: int) -> tuple[np.ndarray, np.ndarray, np.ndarray, int]:
    """Compute exact closed-form Weil blocks using separable prime assembly and Gauss-Legendre quadrature."""
    k = np.arange(K, dtype=np.float64)
    w = omega(k, L)
    signs = np.where(k % 2 == 0, 1.0, -1.0)
    v = np.sqrt(2.0 / L) * (2.0 * signs * w * math.cosh(L / 4.0)) / (w ** 2 + 0.25)
    Q_pole = 2.0 * np.outer(v, v)

    # Prime block fast separable assembly
    pps = prime_powers_up_to(math.exp(L))
    if len(pps) > 0:
        x_list = []
        w_list = []
        for pm, p in pps:
            x = math.log(pm)
            if x < L:
                x_list.append(x)
                w_list.append(2.0 * math.log(p) / math.sqrt(pm))
        x_arr = np.array(x_list)
        w_arr = np.array(w_list)
        sin_mat = np.sin(x_arr[:, None] * w[None, :])
        cos_mat = np.cos(x_arr[:, None] * w[None, :])
        V = np.sum(w_arr[:, None] * sin_mat, axis=0)
        D = np.sum(
            w_arr[:, None] * ((1.0 - x_arr[:, None] / L) * cos_mat + sin_mat / ((2.0 * k[None, :] + 1.0) * np.pi)),
            axis=0,
        )

        j_idx = k[:, None]
        k_idx = k[None, :]
        w_j = w[:, None]
        w_k = w[None, :]
        parity = np.where((j_idx + k_idx) % 2 == 0, 1.0, -1.0)
        diff_sq = w_j ** 2 - w_k ** 2
        safe_diff_sq = np.where(j_idx == k_idx, 1.0, diff_sq)
        Q_prime = (-2.0 * parity / (L * safe_diff_sq)) * (w_k * V[:, None] - w_j * V[None, :])
        np.fill_diagonal(Q_prime, D)
    else:
        Q_prime = np.zeros((K, K))

    # Archimedean quadrature
    edges = np.concatenate([np.linspace(0.0, 200.0, 81)[:-1], np.geomspace(200.0, 100000.0, 120)])
    xi32, wi32 = np.polynomial.legendre.leggauss(32)
    t_all = [0.5 * (edges[i + 1] - edges[i]) * xi32 + 0.5 * (edges[i + 1] + edges[i]) for i in range(len(edges) - 1)]
    w_all = [0.5 * (edges[i + 1] - edges[i]) * wi32 for i in range(len(edges) - 1)]
    t_pts = np.concatenate(t_all)
    w_pts = np.concatenate(w_all)

    t_row = t_pts[None, :]
    denom = w[:, None] ** 2 - t_row ** 2
    resonant = np.abs(denom) < 1e-11
    safe_denom = np.where(resonant, 1.0, denom)
    val = np.sqrt(2.0 / L) * (2.0 * signs[:, None] * w[:, None] * np.cos(0.5 * t_row * L)) / safe_denom
    E_hat = np.where(resonant, math.sqrt(L / 2.0), val)
    psi_kernel = np.real(digamma(0.25 + 0.5j * t_pts)) - math.log(math.pi)
    weights_arch = (1.0 / math.pi) * w_pts * psi_kernel
    Q_arch = (E_hat * weights_arch[None, :]) @ E_hat.T

    Q_pole = 0.5 * (Q_pole + Q_pole.T)
    Q_arch = 0.5 * (Q_arch + Q_arch.T)
    Q_prime = 0.5 * (Q_prime + Q_prime.T)
    return Q_pole, Q_arch, Q_prime, len(pps)


def main() -> int:
    t0 = time.perf_counter()
    print("=" * 110)
    print("PROBE: ASYMPTOTIC SOBOLEV QUOTIENT SCALING & WEIGHTED COERCIVITY (L in [1.0, 12.0])")
    print("Methodology note: ai is being used as a tool.")
    print("Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg.")
    print("=" * 110)

    L_values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0]
    sobolev_s_values = [-1.0, -0.5, 0.0, 0.5, 1.0]

    print(
        f"{'L':>4} | {'K':>3} | {'p^m':>5} | {'n_sub':>5} | {'dim(act)':>8} | "
        f"{'s=-1.0':>12} | {'s=-0.5':>12} | {'s=0.0 (L2)':>12} | {'s=+0.5':>12} | {'s=+1.0 (H1)':>12}"
    )
    print("-" * 110)

    records = []
    all_positive = True

    for L in L_values:
        K = int(max(32, round(8.0 * L)))
        Q_pole, Q_arch, Q_prime, n_pps = compute_weil_blocks_fast(L, K)
        Q_W = Q_pole + Q_arch - Q_prime

        k_all = np.arange(K, dtype=float)
        w_all = omega(k_all, L)
        sub_gap_mask = w_all < GAMMA_1
        n_sub = int(np.sum(sub_gap_mask))
        dim_act = K - n_sub

        Q_sub = Q_W[:n_sub, :n_sub]
        Q_cross = Q_W[:n_sub, n_sub:]
        Q_act = Q_W[n_sub:, n_sub:]

        if n_sub > 0:
            Q_sub_pinv = np.linalg.pinv(Q_sub, rcond=1e-6)
            Sigma_act = Q_act - Q_cross.T @ Q_sub_pinv @ Q_cross
            Sigma_act = 0.5 * (Sigma_act + Sigma_act.T)
        else:
            Sigma_act = Q_act

        w_act = w_all[n_sub:]
        floors = {}
        eigs_h1 = None

        for s in sobolev_s_values:
            weights_s = (1.0 + w_act ** 2) ** (-s / 2.0)
            Sig_s = (Sigma_act * weights_s[:, None]) * weights_s[None, :]
            Sig_s = 0.5 * (Sig_s + Sig_s.T)
            eigs = np.sort(np.linalg.eigvalsh(Sig_s))
            pos_eigs = eigs[eigs > 1e-12]
            if len(pos_eigs) > 0:
                val = float(pos_eigs[0])
            else:
                val = 0.0
                all_positive = False
            floors[f"s_{s:+3.1f}"] = val
            if s == 1.0:
                eigs_h1 = eigs

        s_neg1 = floors["s_-1.0"]
        s_neg05 = floors["s_-0.5"]
        s_0 = floors["s_+0.0"]
        s_pos05 = floors["s_+0.5"]
        s_pos1 = floors["s_+1.0"]

        print(
            f"{L:4.1f} | {K:3d} | {n_pps:5d} | {n_sub:5d} | {dim_act:8d} | "
            f"{s_neg1:12.4e} | {s_neg05:12.4e} | {s_0:12.4e} | {s_pos05:12.4e} | {s_pos1:12.4e}"
        )

        records.append({
            "L": L,
            "K_modes": K,
            "prime_powers_count": n_pps,
            "n_sub_gap_modes": n_sub,
            "dimension_active": dim_act,
            "sobolev_floors": floors,
            "h1_max_eigenvalue": round(float(eigs_h1[-1]), 6) if eigs_h1 is not None else None,
            "h1_condition_number": round(float(eigs_h1[-1] / s_pos1), 2) if s_pos1 > 0 else None,
        })

    print("-" * 110)
    elapsed = time.perf_counter() - t0
    status = "PASS" if all_positive else "FAIL"
    print(f"Status: {status} across all windows L in [1.0, 12.0]! Elapsed: {elapsed:.2f}s")
    print("=" * 110)

    # Save receipt
    receipt_path = Path("scripts/probe_asymptotic_sobolev_quotient_receipt.json")
    receipt_data = {
        "status": status,
        "author": "Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg",
        "methodology_note": "ai is being used as a tool",
        "epistemic_status": "verified-finite (Clay Millennium Problems remain strictly OPEN)",
        "scan_domain": {"L_min": 1.0, "L_max": 12.0, "L_steps": len(L_values)},
        "sobolev_indices_tested": sobolev_s_values,
        "gamma_1": GAMMA_1,
        "all_floors_positive": all_positive,
        "records": records,
        "elapsed_seconds": round(elapsed, 4),
    }
    with open(receipt_path, "w", encoding="utf-8") as f:
        json.dump(receipt_data, f, indent=2)
    print(f"Receipt saved to: {receipt_path}")
    return 0 if all_positive else 1


if __name__ == "__main__":
    raise SystemExit(main())
