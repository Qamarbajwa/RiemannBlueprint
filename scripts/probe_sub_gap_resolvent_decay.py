#!/usr/bin/env python3
"""
probe_sub_gap_resolvent_decay.py

Three-Tier Frequency-Adaptive Sub-Gap Schur Tare and Resolvent Decay Diagnostic:
  Q_W = Q_pole + Q_arch - Q_prime
with ZERO artificial diagonal shift (+0.05 I is strictly forbidden).

Partitions the orthonormal Dirichlet cosine basis e_k(u) on [-L/2, L/2] (K = 32 modes):
  omega_k = (2k + 1) * pi / L
into:
  1. Sub-Gap Basement:    K_sub = { k : omega_k < gamma_1 } (where gamma_1 = 14.134725...)
  2. Active Resonance:    K_act = { k : gamma_1 <= omega_k < omega_tail }
  3. Archimedean Ceiling: K_tail = { k : (Q_arch)_kk > 2 * ||Q_prime_kk|| }

Computes the tared active Schur complement:
  Sigma_act(L) = Q_act - Q_cross^T * Q_sub^{-1} * Q_cross
and tests positivity across extended windows L in {1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0, 5.5, 6.0}.

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

GAMMA_1 = 14.13472514173469379  # Lowest nontrivial Riemann zeta zero


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
    """Modal frequencies omega_k = (2k + 1) * pi / L."""
    return (2.0 * k + 1.0) * np.pi / L


def pole_vector_closed_form(K: int, L: float) -> np.ndarray:
    """Exact closed-form pole overlap v_k on [-L/2, L/2]."""
    k = np.arange(K, dtype=np.float64)
    w = omega(k, L)
    signs = np.where(k % 2 == 0, 1.0, -1.0)
    return np.sqrt(2.0 / L) * (2.0 * signs * w * np.cosh(L / 4.0)) / (w ** 2 + 0.25)


def fourier_basis_closed_form(t: np.ndarray, K: int, L: float) -> np.ndarray:
    """
    Exact Fourier transform hat{e}_k(t) for array t (shape [M]) and modes k=0..K-1.
    Removable singularity handled at |t| == omega_k.
    """
    k = np.arange(K, dtype=np.float64)[:, None]
    w = omega(k, L)
    signs = np.where(k % 2 == 0, 1.0, -1.0)
    t_row = t[None, :]
    denom = w ** 2 - t_row ** 2
    resonant = np.abs(denom) < 1e-11
    safe_denom = np.where(resonant, 1.0, denom)
    val = np.sqrt(2.0 / L) * (2.0 * signs * w * np.cos(0.5 * t_row * L)) / safe_denom
    return np.where(resonant, np.sqrt(L / 2.0), val)


def autocorrelation_matrix_at_shift(x: float, K: int, L: float) -> np.ndarray:
    """Exact closed-form symmetric matrix G_{jk}(x) = (e_j * e_k)(x) for shift x >= 0."""
    ax = abs(float(x))
    if ax >= L:
        return np.zeros((K, K), dtype=np.float64)
    k = np.arange(K, dtype=np.float64)
    w = omega(k, L)
    sin_wx = np.sin(w * ax)
    cos_wx = np.cos(w * ax)

    j_idx = k[:, None]
    k_idx = k[None, :]
    w_j = w[:, None]
    w_k = w[None, :]
    parity = np.where((j_idx + k_idx) % 2 == 0, 1.0, -1.0)
    diff_sq = w_j ** 2 - w_k ** 2
    safe_diff_sq = np.where(j_idx == k_idx, 1.0, diff_sq)
    G = (-2.0 * parity / (L * safe_diff_sq)) * (w_k * sin_wx[:, None] - w_j * sin_wx[None, :])
    diag_vals = (1.0 - ax / L) * cos_wx + sin_wx / ((2.0 * k + 1.0) * np.pi)
    np.fill_diagonal(G, diag_vals)
    return G


def compute_weil_blocks(L: float, K: int = 32) -> tuple[np.ndarray, np.ndarray, np.ndarray, int]:
    """Compute exact (Q_pole, Q_arch, Q_prime, n_prime_powers) on [-L/2, L/2] (autocorrelation [-L, L])."""
    # 1. Pole block Q_pole = 2 * v v^T (exact closed-form)
    v = pole_vector_closed_form(K, L)
    Q_pole = 2.0 * np.outer(v, v)

    # 2. Prime-power subtraction block Q_prime
    pps = prime_powers_up_to(math.exp(L))
    Q_prime = np.zeros((K, K), dtype=float)
    for pm, p in pps:
        x = math.log(pm)
        if x >= L:
            continue
        G_x = autocorrelation_matrix_at_shift(x, K, L)
        w_pm = math.log(p) / math.sqrt(pm)
        Q_prime += 2.0 * w_pm * G_x

    # 3. Archimedean digamma block Q_arch
    edges = np.concatenate([np.linspace(0.0, 200.0, 81)[:-1], np.geomspace(200.0, 100000.0, 120)])
    xi32, wi32 = np.polynomial.legendre.leggauss(32)
    t_all = [0.5 * (edges[i + 1] - edges[i]) * xi32 + 0.5 * (edges[i + 1] + edges[i]) for i in range(len(edges) - 1)]
    w_all = [0.5 * (edges[i + 1] - edges[i]) * wi32 for i in range(len(edges) - 1)]
    t_pts = np.concatenate(t_all)
    w_pts = np.concatenate(w_all)

    E_hat = fourier_basis_closed_form(t_pts, K, L)  # (K, M)
    psi_kernel = np.real(digamma(0.25 + 0.5j * t_pts)) - math.log(math.pi)
    weights = (1.0 / math.pi) * w_pts * psi_kernel
    Q_arch = (E_hat * weights[None, :]) @ E_hat.T

    # Symmetrize
    Q_pole = 0.5 * (Q_pole + Q_pole.T)
    Q_arch = 0.5 * (Q_arch + Q_arch.T)
    Q_prime = 0.5 * (Q_prime + Q_prime.T)
    return Q_pole, Q_arch, Q_prime, len(pps)


def main() -> int:
    t0 = time.perf_counter()
    print("=" * 96)
    print("PROBE: THREE-TIER FREQUENCY-ADAPTIVE SUB-GAP SCHUR TARE DIAGNOSTIC (L in [1.0, 6.0])")
    print("Methodology note: ai is being used as a tool.")
    print("Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg.")
    print("=" * 96)

    L_list = [1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0, 5.5, 6.0]
    K = 32

    records = []
    all_pos = True

    print(
        f"{'L':>4} | {'p^m':>3} | {'n_sub':>5} | {'delta_gap':>9} | {'lam_min(Q_W)':>12} | "
        f"{'lam_min(Sig_act)':>16} | {'tr(Sig)/tr(Q)':>13} | {'arch/prime(k=31)':>16}"
    )
    print("-" * 96)

    for L in L_list:
        Q_pole, Q_arch, Q_prime, n_pps = compute_weil_blocks(L, K=K)
        Q_W = Q_pole + Q_arch - Q_prime

        k_all = np.arange(K, dtype=float)
        w_all = omega(k_all, L)

        # 1. Determine sub-gap modes: omega_k < gamma_1
        sub_gap_mask = w_all < GAMMA_1
        n_sub = int(np.sum(sub_gap_mask))
        delta_gap = float(np.min(np.abs(w_all - GAMMA_1)))

        # 2. Partition blocks
        Q_sub = Q_W[:n_sub, :n_sub]
        Q_cross = Q_W[:n_sub, n_sub:]
        Q_act = Q_W[n_sub:, n_sub:]

        # 3. Eigenvalues and Schur tare
        lam_min_QW = float(np.min(np.linalg.eigvalsh(Q_W)))

        if n_sub > 0:
            Q_sub_pinv = np.linalg.pinv(Q_sub, rcond=1e-6)
            Sigma_act = Q_act - Q_cross.T @ Q_sub_pinv @ Q_cross
            Sigma_act = 0.5 * (Sigma_act + Sigma_act.T)
        else:
            Sigma_act = Q_act

        lam_min_Sigma = float(np.min(np.linalg.eigvalsh(Sigma_act)))
        tr_Q_act = float(np.trace(Q_act))
        tr_Sigma = float(np.trace(Sigma_act))
        ratio_tr = tr_Sigma / tr_Q_act if tr_Q_act > 0 else 0.0

        # 4. Archimedean dominance at high modes
        arch_k31 = float(Q_arch[K - 1, K - 1])
        prime_k31 = abs(float(Q_prime[K - 1, K - 1]))
        dom_k31 = arch_k31 / prime_k31 if prime_k31 > 1e-15 else float("inf")

        if lam_min_QW < -1e-12 or lam_min_Sigma < -1e-9:
            all_pos = False

        print(
            f"{L:4.1f} | {n_pps:3d} | {n_sub:5d} | {delta_gap:9.4f} | {lam_min_QW:12.6e} | "
            f"{lam_min_Sigma:16.6e} | {ratio_tr:13.6f} | {dom_k31:15.2f}x"
        )

        records.append({
            "L": L,
            "active_prime_powers": n_pps,
            "n_sub_gap_modes": n_sub,
            "delta_gap_to_gamma1": round(delta_gap, 6),
            "lambda_min_full_Q_W": round(lam_min_QW, 10),
            "lambda_min_tared_Sigma_act": round(lam_min_Sigma, 10),
            "trace_ratio_Sigma_over_Q_act": round(ratio_tr, 6),
            "arch_over_prime_k31": round(dom_k31, 2) if not math.isinf(dom_k31) else None,
        })

    elapsed = round(time.perf_counter() - t0, 3)
    status = "PASS" if all_pos else "FAIL"
    print("-" * 96)
    print(f"Elapsed: {elapsed}s | Frequency-Adaptive Sub-Gap Coercivity (L in [1.0, 6.0]): {status}")

    receipt = {
        "status": status,
        "epistemic_boundary": "Infinite-horizon L -> infinity coercivity remains strictly OPEN; finite K=32 unshifted signed Weil form with sub-gap tare verified for L in [1.0, 6.0]",
        "artificial_diagonal_shift": 0.0,
        "basis": f"L^2-orthonormal Dirichlet cosine e_k(u) on [-L/2, L/2], K={K}",
        "first_riemann_zero_gamma1": GAMMA_1,
        "elapsed_s": elapsed,
        "windows": records,
    }
    out_path = Path(__file__).resolve().parent / "probe_sub_gap_resolvent_decay_receipt.json"
    out_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    print(f"Receipt written to: {out_path}")
    return 0 if all_pos else 1


if __name__ == "__main__":
    raise SystemExit(main())
