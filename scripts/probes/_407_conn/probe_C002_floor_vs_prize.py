#!/usr/bin/env python3
"""
C002 attack probe: does the all-witness ownership floor's combinatorial upper bound
on F3 incidence  I(delta) <= C(n, d+2)/C(w0, d+1)  reach the prize budget?

Brick (AllWitnessOwnershipFloor.lean, axiom-clean):
    #bad * C(w0, d+1) <= C(n, d+2)     at witness threshold w0,
i.e.  #bad <= C(n, d+2)/C(w0, d+1),  and  eps_mca <= (C(n,d+2)/C(w0,d+1))/q.

F1/F3:  delta* = sup{ delta : I(delta) <= q*eps* }.  Bound is a GOOD point iff
    C(n, d+2)/C(w0, d+1) <= q * eps*.
Prize: eps* = 2^-128, q ~ n * 2^128 (so q*eps* ~ n), or q ~ n^beta.  Here d+2 = k+1,
so d = k-1, d+1 = k, d+2 = k+1.  Code dim = d+1 = k => rate rho = k/n.
Witness threshold from radius delta:  w0 = ceil((1-delta)*n) - 1, so
the bound applies for every witness of size >= w0+1 = ceil((1-delta)*n).
We use w0 = floor((1-delta)*n) as the largest usable threshold (conservative, real-aligned).

Prize window for delta:  (1 - sqrt(rho),  1 - rho - Theta(1/log n)).
We test the *interior* of this window for dyadic n at several proper-subgroup-style
rates rho in {1/2,1/4,1/8,1/16} and ask: at delta in the window, is the Fisher cap
ratio  C(n,k+1)/C(w0,k)  <= q*eps*  (~ n at the prize tuning)?

Exact integer arithmetic (math.comb), no floats except the window edges (Decimal/Fraction).
"""
import math
from fractions import Fraction

def comb(a, b):
    if b < 0 or a < 0 or b > a:
        return 0
    return math.comb(a, b)

def isqrt_frac_lower(rho):
    # sqrt(rho) as a Fraction lower/upper bound for window edges; rho is a Fraction
    # use float for the window edge (only to PICK test deltas; the cap is exact integer)
    return math.sqrt(float(rho))

def analyze(n, rho_frac, qeps_target_factor=1):
    """
    rate rho = k/n  => k = rho*n  (must be integer). dim = k, so d = k-1.
    Fisher cap object: C(n, k+1)/C(w0, k)  with d+2=k+1, d+1=k.
    Prize budget q*eps* ~ n (tuning q = n*2^128).  We compare cap vs n (and vs n^2, n^3
    as looser budgets q*eps* for q ~ n^beta * eps* ... but the canonical prize is ~ n).
    """
    k = rho_frac * n
    if k.denominator != 1:
        return None
    k = int(k)
    if k < 1 or k+1 > n:
        return None
    rho = float(rho_frac)
    johnson_edge = 1 - math.sqrt(rho)         # delta > this
    cap_edge     = 1 - rho                     # delta < this - Theta(1/log n)
    eta = 1.0/max(1.0, math.log(n))            # Theta(1/log n) gap from capacity
    lo = johnson_edge
    hi = cap_edge - eta
    rows = []
    if hi <= lo:
        return {"n": n, "rho": str(rho_frac), "k": k, "window_empty": True,
                "johnson_edge": johnson_edge, "cap_edge": cap_edge, "hi": hi}
    # sample deltas across the window interior
    for frac in (0.1, 0.3, 0.5, 0.7, 0.9):
        delta = lo + frac*(hi-lo)
        # witness threshold: every witness has >= ceil((1-delta)*n) points
        wsize = math.ceil((1-delta)*n)        # min witness size
        w0 = wsize - 1                          # threshold (size >= w0+1)
        if w0 < k:                              # need w0 >= d+1 = k for C(w0,k)>0
            cap = None
            log2_cap = None
        else:
            num = comb(n, k+1)
            den = comb(w0, k)
            cap = Fraction(num, den) if den>0 else None
            # log2 of the cap (exact integer log via bit_length on num/den), avoids overflow
            if cap is not None:
                log2_cap = (math.log2(num) - math.log2(den)) if (num>0 and den>0) else None
            else:
                log2_cap = None
        rows.append({
            "delta": round(delta,4), "wsize_min": wsize, "w0": w0,
            "log2_cap": round(log2_cap,2) if log2_cap is not None else None,
            "log2_budget(n)": round(math.log2(n),2),
            "cap_<=_n?": (cap is not None and cap <= n),
        })
    return {"n": n, "rho": str(rho_frac), "k": k,
            "johnson_edge": round(johnson_edge,4),
            "cap_edge_minus_eta": round(hi,4),
            "window": [round(lo,4), round(hi,4)],
            "rows": rows}

if __name__ == "__main__":
    rhos = [Fraction(1,2), Fraction(1,4), Fraction(1,8), Fraction(1,16)]
    ns = [8, 16, 32, 64, 256, 1024, 4096, 1<<16, 1<<20, 1<<24, 1<<30]
    print("="*100)
    print("C002: Fisher/all-witness-floor cap  C(n,k+1)/C(w0,k)  vs prize budget q*eps* (~ n)")
    print("Prize window for delta = (1-sqrt(rho), 1-rho-Theta(1/log n)).  Test interior.")
    print("="*100)
    for rho in rhos:
        for n in ns:
            r = analyze(n, rho)
            if r is None:
                continue
            if r.get("window_empty"):
                continue
            print(f"\n--- n={n}  rho={r['rho']}  k={r['k']}  window={r['window']} (johnson..cap-eta)")
            for row in r["rows"]:
                l2 = row["log2_cap"]
                flag = "GOOD(cap<=n)" if row["cap_<=_n?"] else "FAIL(cap>>n)"
                if l2 is None:
                    print(f"   delta={row['delta']:<7} w0={row['w0']:<6} cap=NA (w0<k)")
                else:
                    print(f"   delta={row['delta']:<7} w0={row['w0']:<9} log2(cap)={l2:<10} log2(budget n)={row['log2_budget(n)']:<7} [{flag}]")
