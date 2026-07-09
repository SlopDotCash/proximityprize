#!/usr/bin/env python3
"""Q4 deltastar-locate q-TREND (decisive companion to _wf_deltastar-locate_0.py).

The main probe shows the bad-gamma INCIDENCE INTEGERS are ~q-invariant, so eps_mca = const/q.
This file isolates the decisive consequence: as q grows at FIXED (n,k,eps), the measured
crossover delta_x should RISE toward the closed-form delta*(q). We sweep n=8,k=2,rho=1/4 over
8 primes p=1 mod 8 and tabulate the incidence invariance and the delta_x(q) -> delta*(q) trend.
Per-pair counts EXACT; sup over pairs = directed pool (lower bound, so delta_x is an upper bound
on the true crossover). Imports the engine from the main probe.
"""
import importlib.util
import os
import random
import sys
from math import sqrt

_here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    "dsl", os.path.join(_here, "_wf_deltastar-locate_0.py"))
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def main():
    rho, n, k = 0.25, 8, 2
    J, cap = 1 - sqrt(rho), 1 - rho
    m_rows = list(range(k + 1, n + 1))
    primes = mod.primes_1_mod_n(8, 8, 4)   # 41,73,89,97,113,137,193,...
    print("q-TREND, n=8 k=2 rho=1/4   Johnson=%.4f capacity=%.4f" % (J, cap), flush=True)
    print("primes (q):", primes, flush=True)
    profs = {}
    for p in primes:
        random.seed(40413)
        code = mod.Code(p, n, k)
        code.build_codewords()
        profs[p] = mod.measure_eps_exact(code, m_rows, 400)
        print(f"  done q={p}", flush=True)

    print("\nINCIDENCE INTEGERS (badGamma count) vs q  [q-invariance check]:", flush=True)
    print("  " + f"{'m':>3} {'delta':>7}  " + " ".join(f"q={p:<4}" for p in primes), flush=True)
    for m in sorted(m_rows, reverse=True):
        d = 1 - m / n
        print("  " + f"{m:>3} {d:>7.3f}  " + " ".join(f"{profs[p][m]:>5}" for p in primes), flush=True)

    print("\neps_mca = badGamma/q  vs q  [should -> 0 like const/q below+at Johnson]:", flush=True)
    for m in sorted(m_rows, reverse=True):
        d = 1 - m / n
        zone = "[J,cap)" if d >= J - 1e-9 else "<J"
        print("  " + f"{m:>3} {d:>7.3f} {zone:>7}  "
              + " ".join(f"{profs[p][m]/p:>6.3f}" for p in primes), flush=True)

    print("\nMEASURED CROSSOVER delta_x(q) vs closed-form delta*(q), FIXED eps:", flush=True)
    for eps in (0.05, 0.10, 0.15, 0.20):
        print(f"  eps={eps}:", flush=True)
        print(f"    {'q':>5} {'delta_x':>8} {'delta*cf':>9} {'cf-meas':>8}", flush=True)
        for p in primes:
            dx, _ = mod.crossover(profs[p], p, n, eps)
            cf = mod.dstar_closed(rho, n, p, eps)
            print(f"    {p:>5} {dx:>8.4f} {cf:>9.4f} {cf - dx:>8.4f}", flush=True)

    # quantify the trend: does delta_x rise with q toward delta*?  (eps=0.1)
    print("\nTREND VERDICT (eps=0.10): delta_x at smallest vs largest q, and closed-form target:",
          flush=True)
    dx_lo, _ = mod.crossover(profs[primes[0]], primes[0], n, 0.10)
    dx_hi, _ = mod.crossover(profs[primes[-1]], primes[-1], n, 0.10)
    cf_hi = mod.dstar_closed(rho, n, primes[-1], 0.10)
    print(f"   q={primes[0]}: delta_x={dx_lo:.4f}   q={primes[-1]}: delta_x={dx_hi:.4f}   "
          f"delta*(q={primes[-1]})={cf_hi:.4f}", flush=True)
    if dx_hi > dx_lo + 1e-9:
        print("   => delta_x RISES with q toward the closed form (eps_mca=const/q receding): "
              "CONSISTENT with the closed form.", flush=True)
    elif dx_hi >= dx_lo - 1e-9:
        print("   => delta_x flat in q at this eps (already saturated at the const/q ledge).",
              flush=True)
    else:
        print("   => delta_x FALLS with q: would CONTRADICT the const/q reading.", flush=True)


if __name__ == "__main__":
    main()
