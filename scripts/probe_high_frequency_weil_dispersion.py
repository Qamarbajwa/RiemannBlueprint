#!/usr/bin/env python3
"""
probe_high_frequency_weil_dispersion.py
Audit Probe 23: High-Frequency Weil Dispersion Kernel and Stirling Dominance.

Evaluates the unshifted high-frequency Weil dispersion kernel:
  W(lambda, L) = Re psi(1/4 + i*lambda/2) + ln(pi) - (tared prime-phase projection)
across L in {1.0, 2.0, 4.0, 6.0} and frequencies lambda in [10.0, 10000.0],
verifying Stirling logarithmic dominance Re psi(1/4 + i*lambda/2) ~ ln(|lambda|/2)
and confirming inf_lambda W_tared(lambda, L) > 0.

Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg
Methodology note: ai is being used as a tool.
Epistemic invariant: all four Clay Millennium Problems remain strictly OPEN (status: verified-finite).
"""

import json
import math
import time
from pathlib import Path
import numpy as np
import scipy.special

def get_prime_powers(max_val: float) -> list[tuple[int, int, float, float]]:
    """Returns list of (p, m, p^m, (ln p)/p^(m/2)) for p^m <= max_val."""
    prime_powers = []
    max_int = int(math.floor(max_val))
    is_p = [True] * (max_int + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, int(math.isqrt(max_int)) + 1):
        if is_p[i]:
            for j in range(i * i, max_int + 1, i):
                is_p[j] = False
                
    for p in range(2, max_int + 1):
        if is_p[p]:
            val = p
            m = 1
            ln_p = math.log(p)
            while val <= max_val:
                weight = ln_p / math.sqrt(val)
                prime_powers.append((p, m, float(val), weight))
                val *= p
                m += 1
    return sorted(prime_powers, key=lambda x: x[2])

def evaluate_weil_kernel(lam_grid: np.ndarray, L: float) -> dict[str, object]:
    exp_L = math.exp(L)
    prime_powers = get_prime_powers(exp_L)
    
    # Archimedean digamma baseline
    z_grid = 0.25 + 0.5j * lam_grid
    psi_real = scipy.special.digamma(z_grid).real
    archimedean = psi_real + math.log(math.pi)
    
    # Stirling approximation: ln(lambda/2) + ln(pi)
    stirling_asymp = np.log(lam_grid / 2.0) + math.log(math.pi)
    stirling_max_diff = float(np.max(np.abs(psi_real - np.log(lam_grid / 2.0))))
    
    # Prime phase sum: sum_{p^m <= e^L} (ln p / p^(m/2)) * cos(lambda * m * ln p)
    prime_sum = np.zeros_like(lam_grid)
    for p, m, val, weight in prime_powers:
        phase = lam_grid * (m * math.log(p))
        prime_sum += weight * np.cos(phase)
        
    # Baseline taring (Schur subtraction of the mean quiescent level)
    mean_prime = np.mean(prime_sum)
    tared_prime = prime_sum - mean_prime
    
    W_raw = archimedean - prime_sum
    W_tared = archimedean - tared_prime
    
    inf_W_tared = float(np.min(W_tared))
    
    return {
        "L": L,
        "exp_L": round(exp_L, 2),
        "prime_power_count": len(prime_powers),
        "stirling_max_abs_diff": round(stirling_max_diff, 6),
        "inf_W_tared": round(inf_W_tared, 4),
        "is_floor_positive": inf_W_tared > 0.0,
        "sample_points": [
            {
                "lambda": float(lam),
                "archimedean": round(float(arch), 4),
                "tared_prime": round(float(tp), 4),
                "W_tared": round(float(wt), 4)
            }
            for lam, arch, tp, wt in zip(lam_grid[::50], archimedean[::50], tared_prime[::50], W_tared[::50])
        ]
    }

def main():
    t0 = time.time()
    lam_grid = np.linspace(10.0, 10000.0, 500)
    L_values = [1.0, 2.0, 4.0, 6.0]
    
    results = []
    all_floors_positive = True
    all_stirling_accurate = True
    
    for L in L_values:
        res = evaluate_weil_kernel(lam_grid, L)
        if not res["is_floor_positive"]:
            all_floors_positive = False
        if res["stirling_max_abs_diff"] > 0.005:
            all_stirling_accurate = False
        results.append(res)
        
    elapsed = round(time.time() - t0, 4)
    overall_ok = all_floors_positive and all_stirling_accurate
    
    receipt = {
        "probe": "probe_high_frequency_weil_dispersion.py",
        "probe_number": 23,
        "author": "Qamar Munawer",
        "affiliation": "Brandenburg University of Technology Cottbus-Senftenberg",
        "methodology_note": "ai is being used as a tool",
        "epistemic_status": "verified-finite",
        "open_horizon_lock": "STRICTLY OPEN",
        "verified": overall_ok,
        "status": "PASS" if overall_ok else "FAIL",
        "elapsed_seconds": elapsed,
        "frequency_range": [10.0, 10000.0],
        "stirling_dominance_holds": all_stirling_accurate,
        "uniform_floor_positive": all_floors_positive,
        "windows_evaluated": results
    }
    
    out_path = Path(__file__).resolve().parent / "probe_high_frequency_weil_dispersion_receipt.json"
    out_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    print(f"[+] Audit Probe 23 completed in {elapsed}s: status={receipt['status']}, verified={receipt['verified']}")
    print(f"[+] Receipt written to {out_path}")
    return 0 if overall_ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
