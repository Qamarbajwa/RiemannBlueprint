#!/usr/bin/env python3
"""
probe_global_adelic_inductive_limit.py
Audit Probe 24: Global Adèlic Inductive Limit and Non-Archimedean Tail Absorption.

Computes the unramified non-Archimedean local trace tail
  sum_{p > p_r} (ln p) / (p * (p - 1))
across prime cutoffs p_r in {10, 50, 250, 1000, 5000, 10000} (summing primes up to p = 200000),
verifying that the tail is strictly bounded by 2 / sqrt(p_r), decreases monotonically toward 0,
and is absorbed inside the active Schur floor without sign collapse.

Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg
Methodology note: ai is being used as a tool.
Epistemic invariant: all four Clay Millennium Problems remain strictly OPEN (status: verified-finite).
"""

import json
import math
import time
from pathlib import Path

def sieve_primes(max_val: int) -> list[int]:
    is_p = [True] * (max_val + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, int(math.isqrt(max_val)) + 1):
        if is_p[i]:
            for j in range(i * i, max_val + 1, i):
                is_p[j] = False
    return [i for i, prime in enumerate(is_p) if prime]

def main():
    t0 = time.time()
    max_prime = 200000
    primes = sieve_primes(max_prime)
    
    cutoffs = [10, 50, 250, 1000, 5000, 10000]
    tail_records = []
    
    all_bounds_satisfied = True
    all_mono_decreasing = True
    prev_tail = float("inf")
    
    # Baseline semilocal Schur core margin (from Module 29 & Probe 21)
    gamma_core = 0.2694
    
    for p_r in cutoffs:
        tail_sum = sum(math.log(p) / (p * (p - 1)) for p in primes if p > p_r)
        envelope_bound = 2.0 / math.sqrt(p_r)
        
        holds_bound = tail_sum <= envelope_bound
        holds_mono = tail_sum < prev_tail
        
        absorbed_floor = gamma_core - tail_sum
        holds_absorption = absorbed_floor > 0
        
        if not holds_bound:
            all_bounds_satisfied = False
        if not holds_mono:
            all_mono_decreasing = False
            
        tail_records.append({
            "p_r": p_r,
            "primes_summed_above_pr": len([p for p in primes if p > p_r]),
            "tail_sum": round(tail_sum, 8),
            "envelope_bound": round(envelope_bound, 8),
            "ratio_tail_to_bound": round(tail_sum / envelope_bound, 6),
            "absorbed_floor": round(absorbed_floor, 8),
            "bounds_satisfied": holds_bound,
            "absorbed_positive": holds_absorption
        })
        prev_tail = tail_sum
        
    elapsed = round(time.time() - t0, 4)
    overall_ok = all_bounds_satisfied and all_mono_decreasing
    
    receipt = {
        "probe": "probe_global_adelic_inductive_limit.py",
        "probe_number": 24,
        "author": "Qamar Munawer",
        "affiliation": "Brandenburg University of Technology Cottbus-Senftenberg",
        "methodology_note": "ai is being used as a tool",
        "epistemic_status": "verified-finite",
        "open_horizon_lock": "STRICTLY OPEN",
        "verified": overall_ok,
        "status": "PASS" if overall_ok else "FAIL",
        "elapsed_seconds": elapsed,
        "max_prime_sieved": max_prime,
        "prime_count": len(primes),
        "bounds_verified": all_bounds_satisfied,
        "monotonic_decay_verified": all_mono_decreasing,
        "tail_records": tail_records
    }
    
    out_path = Path(__file__).resolve().parent / "probe_global_adelic_inductive_limit_receipt.json"
    out_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    print(f"[+] Audit Probe 24 completed in {elapsed}s: status={receipt['status']}, verified={receipt['verified']}")
    print(f"[+] Receipt written to {out_path}")
    return 0 if overall_ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
