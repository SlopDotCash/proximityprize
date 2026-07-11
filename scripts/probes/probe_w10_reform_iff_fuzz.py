#!/usr/bin/env python3
"""
probe_w10_reform_iff_fuzz.py  (#466, thread ll:topfit-witness-successor, lane _W10)

Fabricate-then-refute probe for the GENERAL complement-reformulation iff that
`_W10LineListObligationsReformIff.lean` proposes to prove in Lean:

  THEOREM CANDIDATE (general, any commutative ring; here fuzzed over GF(p) and ZZ):
    Let P, Q be monic with  P * Q = X^N - 1,  dQ = deg Q,  r = X^D rem P.
    Hypotheses:  D < N   and   D <= m + dQ + 1   ("window starts at or after X^D").
    Then:
        deg r <= m   <=>   Q_i = 0  for all i with  m + dQ + 1 <= D + i <= N - 1.

  This is the FULL iff behind the FS1 floor-bad(64) decision
  (kb deltastar-466-floorbad64-decided-2026-07-03.md): the Lean file
  `_FloorComplementReform.lean` proved only the divisibility pivot; the
  degree/coefficient bookkeeping was "verified computationally in the probe
  rather than in Lean".  Before landing it as a Lean theorem we try to REFUTE it:

  PART 1: exhaustive/randomized fuzz over GF(p) monic factor pairs of X^N-1
          (including non-squarefree cases p | N) and over ZZ (cyclotomic subsets).
  PART 2: hypothesis-necessity hunt: drop  D <= m + dQ + 1  and hunt for
          countermodels (expected to exist -> the hypothesis is not decorative).
  PART 3: the FS instantiation check: N = 8u, D = 6u, dQ = 3u, m = 4u gives
          window i in [u+1, 2u-1] (the kb-note window), verified numerically on
          ALL C(16,10) = 8008 complement pairs at n = 16 for p in {17, 97}
          against the scanner-style residual test  deg(X^12 rem P_A) <= 8.

Pure stdlib + sympy. Exact arithmetic throughout. Read-only elsewhere.
"""

import itertools
import random
import sys

from sympy import GF, ZZ, Poly, symbols, prod, gcd

x = symbols("x")
random.seed(466)


def poly_xn_minus_1(N, dom):
    return Poly(x**N - 1, x, domain=dom)


def factor_pairs(N, dom, max_subsets=256):
    """Yield (P, Q) monic with P*Q = X^N - 1 over dom, from irreducible factorization."""
    f = poly_xn_minus_1(N, dom)
    _, facs = f.factor_list()
    # multiset of irreducible monic factors
    atoms = []
    for g, mult in facs:
        atoms.extend([Poly(g, x, domain=dom)] * mult)
    k = len(atoms)
    idxs = list(range(k))
    seen = set()
    subsets = []
    if 2**k <= max_subsets:
        for rmask in range(2**k):
            subsets.append([i for i in idxs if (rmask >> i) & 1])
    else:
        for _ in range(max_subsets):
            subsets.append([i for i in idxs if random.random() < 0.5])
    one = Poly(1, x, domain=dom)
    for sub in subsets:
        key = tuple(sorted(sub))
        if key in seen:
            continue
        seen.add(key)
        P = one
        for i in sub:
            P = P * atoms[i]
        Q = one
        for i in idxs:
            if i not in sub:
                Q = Q * atoms[i]
        yield P, Q


def window_indices(N, D, m, dQ):
    """i such that m + dQ + 1 <= D + i <= N - 1."""
    lo = max(0, m + dQ + 1 - D)
    hi = N - 1 - D
    return range(lo, hi + 1) if lo <= hi else range(0)


def check_iff(N, D, m, P, Q, dom):
    """Return (lhs, rhs) truth values of the candidate iff."""
    dQ = Q.degree()
    r = Poly(x**D, x, domain=dom).rem(P)
    lhs = r.degree() <= m  # sympy: zero poly has degree -oo -> True
    coeffs = Q.all_coeffs()[::-1]  # coeffs[i] = Q_i

    def qc(i):
        return coeffs[i] if i < len(coeffs) else 0

    rhs = all(qc(i) == 0 for i in window_indices(N, D, m, dQ))
    return lhs, rhs


def part1():
    print("== PART 1: fuzz the iff (hypotheses HELD: D < N, D <= m+dQ+1) ==")
    total, bad = 0, []
    doms = [GF(2), GF(3), GF(5), GF(7), GF(13), GF(17), ZZ]
    for dom in doms:
        for N in range(2, 17):
            for P, Q in factor_pairs(N, dom, max_subsets=64):
                dQ = Q.degree()
                for D in range(0, N):
                    for m in range(0, N + 2):
                        if not (D <= m + dQ + 1):
                            continue
                        lhs, rhs = check_iff(N, D, m, P, Q, dom)
                        total += 1
                        if lhs != rhs:
                            bad.append((str(dom), N, D, m, P.all_coeffs(), Q.all_coeffs()))
    print(f"   checks: {total}, MISMATCHES: {len(bad)}")
    for b in bad[:5]:
        print("   COUNTEREXAMPLE:", b)
    return len(bad) == 0


def part2():
    print("== PART 2: hypothesis-necessity hunt (D > m+dQ+1 allowed) ==")
    total, ce = 0, []
    for dom in [GF(5), GF(7), ZZ]:
        for N in range(2, 13):
            for P, Q in factor_pairs(N, dom, max_subsets=32):
                dQ = Q.degree()
                for D in range(0, N):
                    for m in range(0, N):
                        if D <= m + dQ + 1:
                            continue
                        lhs, rhs = check_iff(N, D, m, P, Q, dom)
                        total += 1
                        if lhs != rhs:
                            ce.append((str(dom), N, D, m,
                                       P.all_coeffs(), Q.all_coeffs(), lhs, rhs))
    print(f"   checks (hwin violated): {total}, iff-violations found: {len(ce)}")
    for c in ce[:3]:
        print("   hwin-necessity witness:", c)
    # Expected: ce nonempty -> hwin is load-bearing, not decorative.
    return len(ce) > 0


def part3():
    print("== PART 3: FS instantiation, complete at n = 16 (all C(16,10) complements) ==")
    ok = True
    # window formula check
    for u in (2, 4, 8):
        N, D, m, dQ = 8 * u, 6 * u, 4 * u, 3 * u
        w = list(window_indices(N, D, m, dQ))
        expect = list(range(u + 1, 2 * u))
        stat = "OK" if w == expect else "MISMATCH"
        print(f"   u={u}: window {w[0]}..{w[-1]} vs kb-note [u+1, 2u-1]={expect[0]}..{expect[-1]}: {stat}")
        ok &= (w == expect)
    # complete pattern check at n=16 against the scanner-style residual test
    n, u = 16, 2
    for p in (17, 97):
        dom = GF(p)
        # primitive 16th root of unity in F_p
        om = None
        for g in range(2, p):
            e = [pow(g, j, p) for j in range(1, n + 1)]
            if e[n - 1] == 1 and all(e[j - 1] != 1 for j in range(1, n)):
                om = g
                break
        roots = [pow(om, j, p) for j in range(n)]
        realizable, checks, mism = 0, 0, 0
        for A in itertools.combinations(range(n), 10):
            B = [j for j in range(n) if j not in A]
            P = prod(Poly(x - roots[j], x, domain=dom) for j in A)
            Q = prod(Poly(x - roots[j], x, domain=dom) for j in B)
            # scanner residual test: deg(x^12 rem P_A) <= 8
            lhs = Poly(x**12, x, domain=dom).rem(P).degree() <= 8
            # window test: Q_i = 0 for i in [u+1, 2u-1] = [3,3]
            coeffs = Q.all_coeffs()[::-1]
            rhs = all((coeffs[i] if i < len(coeffs) else 0) == 0
                      for i in range(u + 1, 2 * u))
            checks += 1
            if lhs != rhs:
                mism += 1
            if lhs:
                realizable += 1
        print(f"   n=16 p={p}: {checks} complement pairs, mismatches={mism}, "
              f"residual-realizable count={realizable}")
        ok &= (mism == 0)
        # p=17 must have realizable 10-subsets (17 is floor-bad(16)); note this counts ALL
        # 10-subsets, a superset of the adjacent-7th-type family, so >0 expected at 17.
    return ok


if __name__ == "__main__":
    r1 = part1()
    r2 = part2()
    r3 = part3()
    print()
    print(f"VERDICT: iff-fuzz clean={r1}, hwin load-bearing={r2}, FS window+complete n=16 check={r3}")
    sys.exit(0 if (r1 and r3) else 1)
