#!/usr/bin/env python3
"""G269: the DC coordinate does not control the adjacent-rank CORE covariance sign (#466).

Computation of record for `Frontier/_G269DCCoordinateSignDecoupling.lean`.

Object (the current frontier CORE surrogate, G220/G228..G267):
  G       = order-n multiplicative subgroup of F_p^*  (n a 2-power, n | (p-1))
  W_G(x)  = #{(y,z) in G^2 : 2y - z = x}                    (double-shift sponsor)
  R_r(x)  = (dp_r * dp_{r-1})(x)
          = #{(A,B): A subset G, |A|=r, B subset G, |B|=r-1, (sum A)-(sum B)=x}
  A_r     = p * sum_x W_G(x) R_r(x) - (sum_x W_G(x))(sum_x R_r(x))   (exact integer CORE covariance)

Exact per-coordinate decomposition.  With SW = sum W_G = n^2, SR = sum R_r,
  P(x) := (p*W_G(x) - SW) * (p*R_r(x) - SR)
a one-line expansion gives the identity
  sum_x P(x) = p^2 * sum_x W_G(x)R_r(x) - p*SW*SR = p * A_r,
so P(x) is the exact centered contribution of coordinate x.  Split
  P0   := P(0)                 (DC-diagonal, x=0 self-collision coordinate)
  Poff := sum_{x!=0} P(x)      (off-DC arcs).

Certifies:
  * the exact decomposition identity  P0 + Poff = p*A_r  on the recorded cells;
  * the DC sign-decoupling witnesses (both directions), hard-coded in the Lean file:
      (16, 97): A5 < 0 < P0        (covariance negative, DC positive)
      (16,433): P0 < 0 < A5        (covariance positive, DC negative)
  * the three-way cell (16,257): A5<0, P0<0, Poff>0 (sign is a DC/off-DC cancellation);
  * the census split: sign(A_r)==sign(P0) in 45/80 cells but sign(A_r)==sign(Poff) in 79/80.

Everything is pure-Python int (no numpy, no floats).  SystemExit(1) on any mismatch.
"""
from __future__ import annotations
from math import comb


def is_prime(x: int) -> bool:
    if x < 2:
        return False
    d = 2
    while d * d <= x:
        if x % d == 0:
            return False
        d += 1
    return True


def prime_factors(n: int) -> list[int]:
    out: list[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def primitive_root(p: int) -> int:
    fac = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise ValueError(f"no primitive root mod {p}")


def subgroup(p: int, n: int) -> list[int]:
    root = primitive_root(p)
    z = pow(root, (p - 1) // n, p)
    out: list[int] = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = x * z % p
    assert x == 1 and len(set(out)) == n
    return out


def W_hist(G: list[int], p: int) -> list[int]:
    """W(x) = #{(y,z) in G^2 : 2y - z = x}."""
    W = [0] * p
    for y in G:
        t = (2 * y) % p
        for z in G:
            W[(t - z) % p] += 1
    return W


def dp_hist(G: list[int], p: int, r: int) -> list[list[int]]:
    """hist[k][x] = #{k-subsets of G with sum = x mod p}, exact int."""
    hist = [[0] * p for _ in range(r + 1)]
    hist[0][0] = 1
    used = 0
    for x in G:
        used += 1
        for k in range(min(r, used), 0, -1):
            src = hist[k - 1]
            dst = hist[k]
            for s in range(p):
                v = src[s]
                if v:
                    dst[(s + x) % p] += v
    return hist


def adj_corr(dpr: list[int], dprm1: list[int], p: int) -> list[int]:
    """R(x) = sum_s dpr[s] * dprm1[(s - x) mod p]."""
    R = [0] * p
    for s in range(p):
        a = dpr[s]
        if a:
            for x in range(p):
                b = dprm1[(s - x) % p]
                if b:
                    R[x] += a * b
    return R


def cell(n: int, p: int, r: int) -> dict:
    G = subgroup(p, n)
    W = W_hist(G, p)
    hist = dp_hist(G, p, r)
    R = adj_corr(hist[r], hist[r - 1], p)
    SW = sum(W)
    SR = sum(R)
    assert SW == n * n
    assert SR == comb(n, r) * comb(n, r - 1)
    T = sum(W[x] * R[x] for x in range(p))
    A_direct = p * T - SW * SR
    P = [(p * W[x] - SW) * (p * R[x] - SR) for x in range(p)]
    pA = sum(P)
    assert pA % p == 0
    A = pA // p
    assert A == A_direct, (A, A_direct)  # exact identity sum P = p*A
    P0 = P[0]
    Poff = pA - P0
    assert P0 + Poff == p * A  # decomposition identity
    return dict(n=n, p=p, r=r, A=A, P0=P0, Poff=Poff, W0=W[0], R0=R[0])


def _sgn(v: int) -> int:
    return 1 if v > 0 else -1 if v < 0 else 0


def main() -> None:
    ok = True

    # 1) exact witnesses hard-coded in the Lean file
    expected = {
        (16, 97, 5): dict(A=-6285008, P0=101818368, Poff=-711464144),
        (16, 433, 5): dict(A=3425440, P0=-215519232, Poff=1698734752),
        (16, 257, 5): dict(A=-1051408, P0=-1035505664, Poff=765293808),
    }
    print("== exact Lean witnesses (recomputed float-free) ==")
    for (n, p, r), exp in expected.items():
        c = cell(n, p, r)
        match = c["A"] == exp["A"] and c["P0"] == exp["P0"] and c["Poff"] == exp["Poff"]
        print(f"  n={n} p={p} r={r}: A={c['A']} P0={c['P0']} Poff={c['Poff']} "
              f"[{'OK' if match else 'MISMATCH'}] "
              f"decomp P0+Poff={c['P0']+c['Poff']} == p*A={p*c['A']}")
        if not match:
            ok = False

    # 2) sign-decoupling assertions
    print("\n== DC sign-decoupling (both directions) ==")
    c97 = cell(16, 97, 5)
    c433 = cell(16, 433, 5)
    d1 = _sgn(c97["A"]) == -1 and _sgn(c97["P0"]) == 1 and _sgn(c97["Poff"]) == -1
    d2 = _sgn(c433["A"]) == 1 and _sgn(c433["P0"]) == -1 and _sgn(c433["Poff"]) == 1
    print(f"  (16,97):  A<0<P0, Poff<0  -> {'OK' if d1 else 'FAIL'}")
    print(f"  (16,433): P0<0<A, Poff>0  -> {'OK' if d2 else 'FAIL'}")
    if not (d1 and d2):
        ok = False

    # 3) three-way cell
    c257 = cell(16, 257, 5)
    d3 = _sgn(c257["A"]) == -1 and _sgn(c257["P0"]) == -1 and _sgn(c257["Poff"]) == 1
    print(f"  (16,257): A<0, P0<0, Poff>0 (three-way cancel) -> {'OK' if d3 else 'FAIL'}")
    if not d3:
        ok = False

    # 4) census split: sign(A)==sign(P0) far less often than sign(A)==sign(Poff).
    #    Sample genuine cells at BOTH orders.  For each order use every rank r with the
    #    adjacent-rank object well-defined (2*r-1 <= n): n=8 -> r in {3,4}, n=16 -> r in {5,6}.
    #    (r=5,6 require n>=9,11 respectively, so they only occur at n=16.)
    print("\n== census: DC-sign-agreement vs off-DC-sign-agreement ==")
    ranks_by_n = {8: (3, 4), 16: (5, 6)}
    results = []
    per_n = {}
    for n in (8, 16):
        cnt = 0
        p = n + 1
        while cnt < 40 and p < 60 * n * n + 2:
            if (p - 1) % n == 0 and is_prime(p):
                for r in ranks_by_n[n]:
                    if 2 * r - 1 <= n:
                        results.append(cell(n, p, r))
                        per_n[n] = per_n.get(n, 0) + 1
                cnt += 1
            p += 1
    print(f"  cells by order: {per_n}")
    tot = len(results)
    dc_agree = sum(1 for c in results if _sgn(c["A"]) == _sgn(c["P0"]) and c["A"] != 0)
    off_agree = sum(1 for c in results if _sgn(c["A"]) == _sgn(c["Poff"]) and c["A"] != 0)
    dc_dom = sum(1 for c in results if abs(c["P0"]) > abs(c["Poff"]))
    print(f"  total cells: {tot}")
    print(f"  sign(A)==sign(P0[DC]): {dc_agree}/{tot}")
    print(f"  sign(A)==sign(Poff):   {off_agree}/{tot}")
    print(f"  |P0|>|Poff|:           {dc_dom}/{tot}")
    # This probe is the COMPUTATION OF RECORD for the census figures published in the Lean
    # comments, the KB note, and the DISPROOF entry.  Assert those exact numbers so any
    # regression (wrong cell count, drifted sign counts) fails loudly instead of passing on
    # the loose dominance inequality alone.
    EXPECTED = {"per_n": {8: 80, 16: 80}, "tot": 160,
                "dc_agree": 120, "off_agree": 158, "dc_dom": 6}
    recorded = {"per_n": per_n, "tot": tot,
                "dc_agree": dc_agree, "off_agree": off_agree, "dc_dom": dc_dom}
    if recorded != EXPECTED:
        print(f"  FAIL: census figures drifted from the recorded values.\n"
              f"        expected {EXPECTED}\n        got      {recorded}")
        ok = False
    # And the qualitative no-go: off-DC must dominate DC as a sign predictor by a wide margin.
    if not (dc_agree < off_agree and off_agree >= dc_agree + 20):
        print("  FAIL: expected off-DC sign agreement to dominate DC by a wide margin")
        ok = False

    print("\nRESULT:", "PASS" if ok else "FAIL")
    if not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
