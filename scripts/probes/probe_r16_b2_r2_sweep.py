#!/usr/bin/env python3
"""R16 B2: sweep/refute the naive corrected r=2 away-Wick rung.

This probe checks the exact FFT inequality

    S2' = sum_{s0 notin ({0} union mu_n)} |I_H(s0)|^4 <= 3 q Sigma^2

for many small/medium proper-subgroup cells with ``mu_n <= H``.  The wider sweep refutes this
naive deletion-set statement, e.g. ``p=7681, n=64, deg=8`` gives ``S2'/Wick2 = 1.00481``.
It also records the failed pointwise shortcut ``sup_{s0 notin D}|I_H(s0)|^2 <= 3 Sigma`` and
the failed ``Q_rest <= q Sigma^2`` shortcut from ``probe_r16_b2_quad.py`` so the next proof
attempt does not chase either false decomposition.

The output is evidence only.  The old Lean implication
``wickForIncidenceAwayAt_two_of_incidenceMoment_le_three_wick_add_diag`` remains useful as a
conditional interface, but the universal analytic premise is false for ``D = {0} union mu_n``.
"""

import argparse
import math
import numpy as np


def factor(x):
    fs, d = set(), 2
    while d * d <= x:
        while x % d == 0:
            fs.add(d)
            x //= d
        d += 1
    if x > 1:
        fs.add(x)
    return fs


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def prim_root(p):
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise ValueError(f"no primitive root found for p={p}")


def primes_one_mod(n, limit, max_count):
    out = []
    p = n + 1
    while p <= limit and len(out) < max_count:
        if p % n == 1 and is_prime(p):
            out.append(p)
        p += n
    return out


def cell(p, n, deg):
    if (p - 1) % n != 0 or (p - 1) % deg != 0:
        return None
    g = prim_root(p)
    gm = pow(g, (p - 1) // n, p)
    mun = []
    x = 1
    for _ in range(n):
        mun.append(x)
        x = x * gm % p
    munset = set(mun)

    gd = pow(g, deg, p)
    Hs = set()
    x = 1
    for _ in range((p - 1) // deg):
        Hs.add(x)
        x = x * gd % p
    if not (munset <= Hs):
        return None

    ind = np.zeros(p, dtype=complex)
    for x in mun:
        ind[x] = 1
    eta = np.fft.ifft(ind) * p
    H = np.array(sorted(Hs))
    w = np.zeros(p, dtype=complex)
    w[H] = np.conj(eta[H])
    I = np.fft.ifft(w) * p
    absI = np.abs(I)
    sig = float(np.sum(np.abs(eta[H]) ** 2))
    s2 = float(np.sum(absI**4))
    diag = [0] + mun
    diag_mask = np.zeros(p, dtype=bool)
    diag_mask[diag] = True
    diag_mass = float(np.sum(absI[diag] ** 4))
    away = s2 - diag_mass
    wick = 3.0 * p * sig**2
    ratio = away / wick
    pointwise_ratio = float(np.max(absI[~diag_mask] ** 2) / (3.0 * sig))

    conv = np.fft.ifft(np.fft.fft(w) ** 2)
    q = float(np.sum(np.abs(conv) ** 2))
    quart = float(np.sum(np.abs(eta[H]) ** 4))
    q_pair = 2 * sig**2 - quart

    abs2 = np.zeros(p)
    abs2[H] = np.abs(eta[H]) ** 2
    q_struct_a = 0.0
    for u in mun:
        if u == 1:
            continue
        for v in mun:
            if v == 1:
                continue
            fac = (1 - u) * pow(v - 1, p - 2, p) % p
            if fac in Hs and fac != 0:
                q_struct_a += float(np.sum(abs2[H] * abs2[(H * fac) % p]))
    q_struct = 2 * q_struct_a
    q_rest_ratio = (q - q_pair - q_struct) / sig**2
    return ratio, q_rest_ratio, pointwise_ratio, len(H), sig


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=20000)
    ap.add_argument("--max-primes", type=int, default=24)
    ap.add_argument("--ns", default="8,16,32")
    ap.add_argument("--degs", default="2,4,8")
    args = ap.parse_args()

    worst = None
    worst_qrest = None
    worst_pointwise = None
    false_shortcuts = 0
    false_pointwise = 0
    cells = 0
    for n in [int(x) for x in args.ns.split(",") if x]:
        ps = primes_one_mod(n, args.limit, args.max_primes)
        for p in ps:
            for deg in [int(x) for x in args.degs.split(",") if x]:
                got = cell(p, n, deg)
                if got is None:
                    continue
                ratio, qrest, pointwise, hcard, sig = got
                cells += 1
                if qrest > 1:
                    false_shortcuts += 1
                if pointwise > 1:
                    false_pointwise += 1
                if worst is None or ratio > worst[0]:
                    worst = (ratio, p, n, deg, qrest, pointwise, hcard, sig)
                if worst_qrest is None or qrest > worst_qrest[0]:
                    worst_qrest = (qrest, p, n, deg)
                if worst_pointwise is None or pointwise > worst_pointwise[0]:
                    worst_pointwise = (pointwise, p, n, deg)
                verdict = "OK" if ratio <= 1 else "FAIL"
                q3 = "Q3_FALSE" if qrest > 1 else "q3_ok"
                pt = "PT_FALSE" if pointwise > 1 else "pt_ok"
                print(
                    f"{verdict} p={p} n={n} deg={deg} |H|={hcard} "
                    f"S2away/Wick2={ratio:.6g} "
                    f"supAway2/(3Sig)={pointwise:.6g} {pt} "
                    f"Qrest/(qSig2)={qrest:.6g} {q3}"
                )
    if worst:
        ratio, p, n, deg, qrest, pointwise, hcard, sig = worst
        max_qrest, qp, qn, qdeg = worst_qrest
        max_pointwise, pp, pn, pdeg = worst_pointwise
        print(
            f"SUMMARY cells={cells} worst_ratio={ratio:.6g} at p={p}, n={n}, deg={deg}, "
            f"|H|={hcard}, Q3_false_cells={false_shortcuts}, "
            f"pointwise_false_cells={false_pointwise}, "
            f"max_pointwise_ratio={max_pointwise:.6g} at p={pp}, n={pn}, deg={pdeg}, "
            f"max_Qrest_ratio={max_qrest:.6g} at p={qp}, n={qn}, deg={qdeg}"
        )
    else:
        print("SUMMARY no valid cells")


if __name__ == "__main__":
    main()
