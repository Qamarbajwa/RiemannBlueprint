#!/usr/bin/env python3
"""
probe_true_signed_weil_schur_coercivity.py

True Signed Semilocal Weil Quadratic Form Schur-Complement Coercivity Diagnostic:
  Q_W = Q_pole + Q_arch - Q_prime
with ZERO artificial diagonal shifts (+0.05 I is strictly forbidden).

Uses the exact L^2-orthonormal Dirichlet cosine basis on [-L/2, L/2]:
  e_k(u) = sqrt(2/L) * cos((2k+1)*pi*u / L),  k = 0, ..., 15 (K = 16).
Partitions Q_W into:
  - Q_PP (4x4 low-mode pole/bulk block, 0 <= k < 4)
  - Q_CC (12x12 high-oscillation block, 4 <= k < 16)
and measures lambda_min(Q_W), lambda_min(Q_PP), lambda_min(Sigma_L), sin^2(Theta_L),
and the high-degree Archimedean dominance ratio (Q_arch)_kk / |(Q_prime)_kk| across
L in {0.6, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0}.

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


def eval_e_hat(L: float, omegas: np.ndarray, t: np.ndarray) -> np.ndarray:
    """Evaluate Fourier transform hat{e}_k(t) for k=0..K-1 at points t (shape (M,)).
    Returns shape (K, M).
    """
    K = len(omegas)
    ks = np.arange(K)
    signs = np.where(ks % 2 == 0, 1.0, -1.0)[:, None]  # (K, 1)
    w = omegas[:, None]                                  # (K, 1)
    t_row = t[None, :]                                   # (1, M)
    denom = w ** 2 - t_row ** 2
    cos_tL2 = np.cos(t_row * (L / 2.0))
    # Handle removable singularity near |t| == omega_k
    safe_denom = np.where(np.abs(denom) < 1e-10, 1.0, denom)
    raw = math.sqrt(2.0 / L) * 2.0 * signs * w * cos_tL2 / safe_denom
    near_sing = np.abs(denom) < 1e-10
    if np.any(near_sing):
        # lim_{t -> +/- omega_k} hat{e}_k(t) = sqrt(L/2)
        raw = np.where(near_sing, math.sqrt(L / 2.0), raw)
    return raw


def compute_weil_blocks(L: float, K: int = 16) -> tuple[np.ndarray, np.ndarray, np.ndarray, int]:
    """Compute exact (Q_pole, Q_arch, Q_prime, n_prime_powers) on [-L/2, L/2] (autocorrelation [-L, L])."""
    ks = np.arange(K, dtype=float)
    omegas = (2.0 * ks + 1.0) * math.pi / L
    signs = np.where(np.arange(K) % 2 == 0, 1.0, -1.0)

    # 1. Pole block Q_pole = 2 * v v^T (analytic closed-form)
    v = math.sqrt(2.0 / L) * 2.0 * signs * omegas * math.cosh(L / 4.0) / (omegas ** 2 + 0.25)
    Q_pole = 2.0 * np.outer(v, v)

    # 2. Prime-power subtraction block Q_prime
    pps = prime_powers_up_to(math.exp(L))
    Q_prime = np.zeros((K, K), dtype=float)
    xi64, wi64 = np.polynomial.legendre.leggauss(64)
    for pm, p in pps:
        x = math.log(pm)
        if x >= L:
            continue
        a, b = -L / 2.0, L / 2.0 - x
        u = 0.5 * (b - a) * xi64 + 0.5 * (a + b)
        w = 0.5 * (b - a) * wi64
        # e_j(u + x) and e_k(u)
        ej = math.sqrt(2.0 / L) * np.cos(omegas[:, None] * (u[None, :] + x))
        ek = math.sqrt(2.0 / L) * np.cos(omegas[:, None] * u[None, :])
        g_jk = (ej * w[None, :]) @ ek.T
        w_pm = math.log(p) / math.sqrt(pm)
        # g_jk(x) + g_jk(-x) = g_jk(x) + g_kj(x)
        Q_prime += w_pm * (g_jk + g_jk.T)

    # 3. Archimedean digamma block Q_arch using multi-scale composite 32-pt Gauss-Legendre on [0, 100000]
    #    Kernel: Re psi(1/4 + i t / 2) - ln(pi)
    edges = np.concatenate([np.linspace(0.0, 200.0, 81)[:-1], np.geomspace(200.0, 100000.0, 120)])
    xi32, wi32 = np.polynomial.legendre.leggauss(32)
    t_all = [0.5 * (edges[i + 1] - edges[i]) * xi32 + 0.5 * (edges[i + 1] + edges[i]) for i in range(len(edges) - 1)]
    w_all = [0.5 * (edges[i + 1] - edges[i]) * wi32 for i in range(len(edges) - 1)]
    t_pts = np.concatenate(t_all)
    w_pts = np.concatenate(w_all)

    E_hat = eval_e_hat(L, omegas, t_pts)  # (K, M)
    psi_kernel = np.real(digamma(0.25 + 0.5j * t_pts)) - math.log(math.pi)
    # Factor 2 for [-T_max, T_max] symmetry, divided by 2*pi => 1/pi
    weights = (1.0 / math.pi) * w_pts * psi_kernel
    Q_arch = (E_hat * weights[None, :]) @ E_hat.T

    # Symmetrize to eliminate floating-point asymmetry
    Q_pole = 0.5 * (Q_pole + Q_pole.T)
    Q_arch = 0.5 * (Q_arch + Q_arch.T)
    Q_prime = 0.5 * (Q_prime + Q_prime.T)
    return Q_pole, Q_arch, Q_prime, len(pps)


def main() -> int:
    t0 = time.perf_counter()
    print("=" * 84)
    print("PROBE: TRUE SIGNED SEMILOCAL WEIL FORM & SCHUR COMPLEMENT COERCIVITY (NO SHIFT)")
    print("Methodology note: ai is being used as a tool.")
    print("Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg.")
    print("=" * 84)

    L_list = [0.6, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0]
    K = 16
    n_p = 4  # Low-mode pole/bulk block: 0 <= k < 4; High-oscillation block: 4 <= k < 16

    records = []
    all_pos = True
    for L in L_list:
        Q_pole, Q_arch, Q_prime, n_pps = compute_weil_blocks(L, K=K)
        Q_W = Q_pole + Q_arch - Q_prime

        Q_PP = Q_W[:n_p, :n_p]
        Q_PC = Q_W[:n_p, n_p:]
        Q_CP = Q_W[n_p:, :n_p]
        Q_CC = Q_W[n_p:, n_p:]

        lam_min_QW = float(np.min(np.linalg.eigvalsh(Q_W)))
        lam_min_QPP = float(np.min(np.linalg.eigvalsh(Q_PP)))
        Q_PP_pinv = np.linalg.pinv(Q_PP, rcond=1e-6)
        Sigma_L = Q_CC - Q_CP @ Q_PP_pinv @ Q_PC
        Sigma_L = 0.5 * (Sigma_L + Sigma_L.T)
        lam_min_Sigma = float(np.min(np.linalg.eigvalsh(Sigma_L)))

        tr_QCC = float(np.trace(Q_CC))
        tr_Sigma = float(np.trace(Sigma_L))
        sin2_theta = tr_Sigma / tr_QCC if tr_QCC > 0 else 0.0

        # High-degree Archimedean dominance ratio (Q_arch)_kk / |(Q_prime)_kk| for k = 4..15
        arch_diag = np.diag(Q_arch)[n_p:]
        prime_diag = np.abs(np.diag(Q_prime))[n_p:]
        dom_ratios = arch_diag / np.maximum(prime_diag, 1e-15)
        min_dom_ratio = float(np.min(dom_ratios)) if n_pps > 0 else float("inf")
        k15_dom_ratio = float(dom_ratios[-1]) if n_pps > 0 else float("inf")

        # True PSD within IEEE-754 64-bit precision
        if lam_min_QW < -1e-12 or lam_min_QPP < -1e-12 or lam_min_Sigma < -1e-9:
            all_pos = False

        print(
            f"L={L:3.1f} | p^m={n_pps:2d} | lam_min(Q_W)={lam_min_QW:9.6f} | "
            f"lam_min(Q_PP)={lam_min_QPP:9.6f} | lam_min(Sig_L)={lam_min_Sigma:9.6f} | "
            f"sin2={sin2_theta:.6f} | arch/prime(k=15)={k15_dom_ratio:7.2f}x"
        )

        records.append({
            "L": L,
            "active_prime_powers": n_pps,
            "lambda_min_Q_W": round(lam_min_QW, 8),
            "lambda_min_Q_PP": round(lam_min_QPP, 8),
            "lambda_min_Sigma_L": round(lam_min_Sigma, 8),
            "sin2_theta_L": round(sin2_theta, 8),
            "min_arch_over_prime_k4_to_15": None if math.isinf(min_dom_ratio) else round(min_dom_ratio, 4),
            "arch_over_prime_k15": None if math.isinf(k15_dom_ratio) else round(k15_dom_ratio, 4),
        })

    elapsed = round(time.perf_counter() - t0, 3)
    status = "PASS" if all_pos else "FAIL"
    print(f"Elapsed: {elapsed}s | True Signed Weil Positivity & Schur Coercivity (L<=4.0): {status}")

    receipt = {
        "status": status,
        "epistemic_boundary": "Infinite-horizon L -> infinity coercivity remains strictly OPEN; finite K=16 unshifted signed Weil form verified for L <= 4.0",
        "artificial_diagonal_shift": 0.0,
        "basis": "L^2-orthonormal Dirichlet cosine e_k(u) on [-L/2, L/2], K=16 (Q_PP: 4x4, Q_CC: 12x12)",
        "elapsed_s": elapsed,
        "windows": records,
    }
    out_path = Path(__file__).resolve().parent / "probe_true_signed_weil_schur_coercivity_receipt.json"
    out_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    print(f"Receipt written to: {out_path}")
    return 0 if all_pos else 1


if __name__ == "__main__":
    raise SystemExit(main())
