#!/usr/bin/env python3
"""
probe_444_branching_k4.py  (#444 SEAM A -- Refuter B, follow-up)

Covers the configs the main branching probe did not reach before timeout:
  larger code degree k=4 (nontrivial child F,G with deg<2) and eta=0.25,
  at n=16,32 (two primes each). Same per-level branching measurement.
Imports the measurement from probe_444_branching_factor.py.
"""
import sys, os
from math import comb
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_444_branching_factor import measure_level, find_window_prime

def run():
    print("="*78)
    print("PER-LEVEL BRANCHING (k=4 and eta=0.25 configs)")
    print("="*78)
    rows = []
    configs = [
        (16, 4, 0.0625),
        (32, 4, 0.0625),
        (16, 4, 0.125),
        (32, 4, 0.125),
        (16, 2, 0.25),
        (32, 2, 0.25),
        (16, 1, 0.0625),
        (32, 1, 0.0625),
        (64, 1, 0.0625),
    ]
    for (n, k, eta) in configs:
        if comb(n, k) > 3_000_000:
            print(f"  SKIP n={n} k={k}: C(n,k)={comb(n,k)} too large"); continue
        primes = [find_window_prime(n, 4.0)]
        p2 = find_window_prime(n, 4.5)
        if p2 != primes[0]:
            primes.append(p2)
        for p in primes:
            try:
                rows.append(measure_level(n, k, eta, p, label=f"k={k},eta={eta}"))
            except Exception as ex:
                print(f"  ERROR n={n} k={k} p={p}: {ex}")
    print("\nSUMMARY_K4 done")

if __name__ == "__main__":
    run()
