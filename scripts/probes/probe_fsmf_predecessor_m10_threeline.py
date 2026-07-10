#!/usr/bin/env python3
"""m=10 miniature of the P1 rate-quarter predecessor: THREE one-fresh pencils.

At m=4 the coverage inequality (sum of pairwise core overlaps minus triple
overlap >= 3(t-1) - n = 41 versus a structural maximum of 40) forbids three
cores of size t-1, so the extremal family uses two pencils (badCount
2(n-t+1) = 58).  At m=10 (n=160, k=40, z=87, t=89 over F_641) the fibre
ansatz achieves 3*(3*10+8) - 8 = 106 >= 3*88 - 160 = 104, so THREE cores of
size t-1 = 88 coexist - the same regime as P1 itself, where
3(T-1) - N = 704643071 <= 738197500.

Construction (mirrors the m=4 three-line probe, scaled):
  y = x^10 maps the order-160 domain onto mu_16; potentials differ by
  A_ij = q_ij(y) * g(x), R_ij = q_ij(y) * h(x) with q13 = q12 + q23 cubics
  splitting over mu_16 and g, h of degree 9 sharing 8 domain roots
  (deficiency one).  Pairwise core overlaps: 30 fibre points + 8 shared
  roots = 38 = k-2; triple overlap = 8.  Cores 88/88/88, free coords: 2,
  used to prescribe two fresh gammas each (lines 1 and 2).

Predicted count: every coordinate outside the triple overlap contributes the
single gamma phi(x) = -g(x)/h(x) (a Moebius map after cancelling the shared
roots, hence injective), plus 4 prescribed free gammas:
  (158 covered - 8 triple) + 2*2 = 154 = n - 6 < n = 160.

Census: witness-level census over all 641 scalars is exact FOR THE THREE
PENCILS; completeness against arbitrary explanations is checked by the same
multiplicity-2 GS + Roth-Ruckenstein engine as the m=4 probe on
  (a) every witnessed bad gamma (must be re-found: lower-bound consistency),
  (b) a deterministic sample of non-witness gammas (must be empty).
Pass --full for the complete 641-gamma GS census (slower).

Deterministic; numpy required.
"""

from __future__ import annotations

import json
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])

from probe_fsmf_predecessor_miniature_census import (  # noqa: E402
    Census, build_domain, cubic_splitting_pair, interpolate, padd, pdeg,
    peval, pmul, pscale, psub, trim, vanishing, witness_census)

import random  # noqa: E402

P, N, K, T = 641, 160, 40, 89
Z_CORE = 87
assert 6 * Z_CORE == 53 * 10 - 8 and T == Z_CORE + 2 and N == 16 * 10


def comp10(q, p):
    out = [0]
    for j, c in enumerate(q):
        out = padd(out, pscale(c, [0] * (10 * j) + [1], p), p)
    return out


def build():
    p, n, k, t = P, N, K, T
    xs = build_domain(p, n)
    dom = set(xs)
    mu16 = {pow(x, 10, p) for x in xs}
    assert len(mu16) == 16
    found = cubic_splitting_pair(p, mu16)
    assert found, "no splitting cubic pair over F_641"
    R1, R2, beta, R3 = found
    print(f"[m10] cubic potentials: q12 roots {R1}, q23 roots {R2}, "
          f"beta={beta}, q13 roots {R3}")

    def cubic(roots, scale):
        q = [scale]
        for r in roots:
            q = pmul(q, [(-r) % p, 1], p)
        return q

    q12 = cubic(R1, 1)
    q23 = cubic(R2, beta)
    q13 = padd(q12, q23, p)
    allroots = set(R1) | set(R2) | set(R3)
    wcands = [x for x in xs if pow(x, 10, p) not in allroots]
    ws = wcands[:8]                       # shared g/h roots (triple overlap)
    off = [v for v in range(2, p) if v not in dom][:2]
    g = vanishing(ws + [off[0]], p)       # degree 9
    h = vanishing(ws + [off[1]], p)       # degree 9, shares 8 roots with g
    A12 = pmul(comp10(q12, p), g, p)
    A23 = pmul(comp10(q23, p), g, p)
    A13 = padd(A12, A23, p)
    R12p = pmul(comp10(q12, p), h, p)
    R23p = pmul(comp10(q23, p), h, p)
    R13p = padd(R12p, R23p, p)
    for poly in (A12, A23, A13, R12p, R23p, R13p):
        assert pdeg(poly) <= k - 1
    rng = random.Random(424242)
    a1 = [rng.randrange(p) for _ in range(k)]
    r1 = [rng.randrange(p) for _ in range(k)]
    a2, r2 = psub(a1, A12, p), psub(r1, R12p, p)
    a3, r3 = psub(a1, A13, p), psub(r1, R13p, p)

    def fib(roots):
        return {i for i, x in enumerate(xs) if pow(x, 10, p) in roots}

    iws = {xs.index(w) for w in ws}
    P12 = fib(R1) | iws
    P23 = fib(R2) | iws
    P13 = fib(R3) | iws
    assert len(P12) == 38 and len(P23) == 38 and len(P13) == 38
    used = P12 | P23 | P13
    rest = [i for i in range(n) if i not in used]
    assert len(rest) == 62, len(rest)     # 160 - 90 fibre - 8 shared
    priv1, priv2, priv3 = rest[:20], rest[20:40], rest[40:60]
    free = rest[60:62]
    core1 = P12 | P13 | set(priv1)
    core2 = P12 | P23 | set(priv2)
    core3 = P13 | P23 | set(priv3)
    assert (len(core1), len(core2), len(core3)) == (88, 88, 88)
    u0, u1 = [0] * n, [0] * n
    for i in core1:
        u0[i], u1[i] = peval(a1, xs[i], p), peval(r1, xs[i], p)
    for i in core2 - core1:
        u0[i], u1[i] = peval(a2, xs[i], p), peval(r2, xs[i], p)
    for i in core3 - core1 - core2:
        u0[i], u1[i] = peval(a3, xs[i], p), peval(r3, xs[i], p)
    # free coords prescribe fresh gammas for lines 1 and 2, outside phi range
    phi_all = set()
    for x in xs:
        gv, hv = peval(g, x, p), peval(h, x, p)
        if hv:
            phi_all.add((-gv) * pow(hv, p - 2, p) % p)
    banned = phi_all | {0}
    fresh = [gm for gm in range(1, p) if gm not in banned][:4]
    assert len(fresh) == 4
    for idx, i in enumerate(free):
        g1, g2 = fresh[2 * idx], fresh[2 * idx + 1]
        x = xs[i]
        v1 = (peval(a1, x, p) + g1 * peval(r1, x, p)) % p
        v2 = (peval(a2, x, p) + g2 * peval(r2, x, p)) % p
        inv = pow(g1 - g2, p - 2, p)
        b = (v1 - v2) * inv % p
        u0[i], u1[i] = (v1 - g1 * b) % p, b
    cores = [core1, core2, core3]
    lines = [(a1, r1), (a2, r2), (a3, r3)]
    actual = [{i for i, x in enumerate(xs)
               if peval(a, x, p) == u0[i] and peval(r, x, p) == u1[i]}
              for (a, r) in lines]
    assert actual == cores, [len(c) for c in actual]
    return xs, u0, u1, lines, cores


def main():
    full = "--full" in sys.argv
    xs, u0, u1, lines, cores = build()
    wit, _ = witness_census(P, xs, T, lines, cores, u0, u1)
    print(f"[m10] witness-level badCount = {len(wit)} "
          f"(predicted 154 = n - 6; budget n = {N}; holds = {len(wit) <= N})")
    eng = Census(P, N, K, T, xs)
    if full:
        bad, _ = eng.full_census(u0, u1, "m10:three one-fresh pencils FULL")
        assert wit <= set(bad)
        extra = sorted(set(bad) - wit)
        print(f"[m10] FULL census: badCount = {len(bad)}, "
              f"non-witness extras = {extra}")
        result = len(bad)
    else:
        # (a) witnessed gammas must be re-found by the exact engine
        missing = []
        for gm in sorted(wit):
            rep = eng.gamma_report(u0, u1, gm)
            if not any(sz >= T and not joint for (_, sz, joint) in rep):
                missing.append(gm)
        assert not missing, f"witnessed gammas missed by GS: {missing}"
        print(f"[m10] all {len(wit)} witnessed gammas confirmed by GS engine")
        # (b) sample of non-witness gammas must be clean
        others = [gm for gm in range(P) if gm not in wit]
        sample = others[::13][:40]
        dirty = []
        for gm in sample:
            rep = eng.gamma_report(u0, u1, gm)
            if any(sz >= T and not joint for (_, sz, joint) in rep):
                dirty.append(gm)
        print(f"[m10] sampled {len(sample)} non-witness gammas; "
              f"unexpected bad = {dirty}")
        result = len(wit) + len(dirty)
    print(json.dumps({
        "m": 10, "n": N, "k": K, "z": Z_CORE, "t": T, "field": P,
        "three_one_fresh_pencils_badCount": result,
        "budget_n": N, "holds": result <= N,
    }, indent=2))


if __name__ == "__main__":
    main()
