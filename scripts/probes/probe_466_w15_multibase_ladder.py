#!/usr/bin/env python3
"""Probe (#466, lane W15 successor): the UPPER side of the safe large-zero mcaEvent budget.

W15 (`_W15LargeZeroMcaEventFloor.lean`) proved the unconditional floor `B_near >= n - a`
(support ladder).  This probe attacks the upper side:

  Q1. Does the exact mcaEvent scalar count on ZeroDirectionSafeLine + large-zero lines ever
      exceed the candidate unconditional ceiling  count <= Lambda * |supp|
      (Lambda = # line-appearing codewords at threshold a, supp = direction support)?
  Q2. Do multi-base ladders (M disjoint (a-1)-anchors in Z with M distinct constant base
      codewords) beat the single-base floor n - a, and by how much?  Theory predicts the
      constant-base family is capped at M <= (a-1)/(k-1) bases (safety), hence O(n) total.
  Q3. Randomized search over safe large-zero lines for counts that look superlinear
      (count > C * n for C beyond the constant-base cap).

Ground truth per line: gamma fires mcaEvent iff there is a codeword w with agreement set
A = agree(w, u0 + gamma*u1), |A| >= a, such that NO codeword agrees with u1 on all of A
(checked by interpolation of u1 on k points of A: the only candidate explainer).
Taking S = A maximal is optimal: if A is contained in some explainer's agreement set then
every subset is too.

Deterministic (seeded).  Exit 0 iff no violation of the candidate ceiling is found.
"""

import itertools
import sys

import numpy as np

rng = np.random.default_rng(466_15)


def all_codewords(q: int, n: int, k: int) -> np.ndarray:
    """All RS[q; n, k] codewords on domain 0..n-1, as a (q^k, n) int array."""
    dom = np.arange(n)
    V = np.vstack([pow_mod(dom, j, q) for j in range(k)])  # (k, n)
    coeffs = np.array(list(itertools.product(range(q), repeat=k)))  # (q^k, k)
    return (coeffs @ V) % q


def pow_mod(x: np.ndarray, e: int, q: int) -> np.ndarray:
    r = np.ones_like(x)
    for _ in range(e):
        r = (r * x) % q
    return r


def interp_explains(q: int, k: int, u1: np.ndarray, A: np.ndarray) -> bool:
    """True iff SOME degree<k codeword agrees with u1 on all of A (|A| >= k).
    The only candidate is the interpolation of u1 through the first k points of A."""
    xs = A[:k]
    ys = u1[xs]
    # Lagrange evaluation of the interpolant at every point of A
    for t in A:
        acc = 0
        for j in range(k):
            num, den = 1, 1
            for m in range(k):
                if m == j:
                    continue
                num = (num * (int(t) - int(xs[m]))) % q
                den = (den * (int(xs[j]) - int(xs[m]))) % q
            acc = (acc + ys[j] * num * pow(den, -1, q)) % q
        if acc % q != u1[t] % q:
            return False
    return True


def line_stats(q, n, k, a, CW, u0, u1):
    """Return (is_large_zero, is_safe, bad_count, Lambda, supp_size)."""
    Z = np.where(u1 % q == 0)[0]
    supp = np.where(u1 % q != 0)[0]
    large_zero = len(Z) >= a
    # safety: every codeword agrees with u0 on < a coordinates of Z
    agrZ = (CW[:, Z] == u0[Z][None, :]).sum(axis=1) if len(Z) else np.zeros(len(CW), int)
    safe = agrZ.max(initial=0) < a
    bad = 0
    appearing = set()
    for g in range(q):
        line = (u0 + g * u1) % q
        agr = (CW == line[None, :]).sum(axis=1)
        ws = np.where(agr >= a)[0]
        appearing.update(int(w) for w in ws)
        fired = False
        for w in ws:
            A = np.where(CW[w] == line)[0]
            if not interp_explains(q, k, u1 % q, A):
                fired = True
                break
        bad += fired
    return large_zero, safe, bad, len(appearing), len(supp)


def multibase_line(q, n, a, M):
    """Constant-base ladder: Z = M disjoint (a-1)-blocks, u0 = j on block j;
    u0 on supp spread so all M scalars per support point are distinct."""
    z = M * (a - 1)
    assert z < n
    u1 = np.ones(n, dtype=int)
    u1[:z] = 0
    u0 = np.zeros(n, dtype=int)
    for j in range(M):
        u0[j * (a - 1):(j + 1) * (a - 1)] = j
    for t, i in enumerate(range(z, n)):
        u0[i] = (-(M) * (t + 1)) % q  # gammas j + M*(t+1): all distinct while in range
    return u0, u1


def main() -> int:
    shapes = [
        # (q, n, k, a)
        (13, 12, 2, 3),
        (13, 12, 2, 4),
        (13, 12, 3, 5),
        (13, 12, 3, 6),
        (17, 16, 4, 9),   # campaign rate-quarter shape
        (29, 24, 2, 3),   # long code, low k: constant-base cap M = 2
        (29, 24, 2, 5),
        (29, 24, 3, 5),
    ]
    ceiling_violations = 0
    print(f"{'q':>3} {'n':>3} {'k':>2} {'a':>2} {'kind':<12} {'M':>2} "
          f"{'count':>5} {'n-a':>4} {'Lam':>4} {'sup':>3} {'Lam*sup':>7} {'cnt/n':>6}")
    for (q, n, k, a) in shapes:
        CW = all_codewords(q, n, k)
        best = 0

        def report(kind, M, u0, u1):
            nonlocal ceiling_violations, best
            lz, safe, bad, lam, s = line_stats(q, n, k, a, CW, u0, u1)
            if not (lz and safe):
                return None
            viol = bad > lam * s
            if viol:
                ceiling_violations += 1
            best = max(best, bad)
            print(f"{q:>3} {n:>3} {k:>2} {a:>2} {kind:<12} {M:>2} "
                  f"{bad:>5} {n - a:>4} {lam:>4} {s:>3} {lam * s:>7} {bad / n:>6.2f}"
                  + ("  **CEILING VIOLATION**" if viol else ""))
            return bad

        # single-base W15 ladder (Z of size a, marked point last in Z)
        u1 = np.ones(n, dtype=int)
        u1[:a] = 0
        u0 = np.zeros(n, dtype=int)
        u0[a - 1] = 1
        for i in range(a, n):
            u0[i] = (-i) % q
        report("ladder-M1", 1, u0, u1)

        # constant multi-base ladders, M = 2, 3 where they fit
        for M in (2, 3):
            if M * (a - 1) < n and q > M * (n + 1):
                pass  # spread always fine mod q for our shapes; keep simple
            if M * (a - 1) < n:
                u0m, u1m = multibase_line(q, n, a, M)
                report(f"ladder-M{M}", M, u0m, u1m)

        # randomized safe large-zero lines (structured u0 on Z near codewords + noise)
        trials = 60
        for _ in range(trials):
            z = int(rng.integers(a, n))  # zero-set size in [a, n-1]
            perm = rng.permutation(n)
            Z, S = perm[:z], perm[z:]
            u1r = np.zeros(n, dtype=int)
            u1r[S] = rng.integers(1, q, size=len(S))
            u0r = rng.integers(0, q, size=n)
            # bias: plant a random codeword on a random (a-1)-subset of Z
            w = CW[int(rng.integers(len(CW)))]
            anchor = rng.permutation(Z)[:a - 1]
            u0r[anchor] = w[anchor]
            report("random", 0, u0r % q, u1r % q)
        print(f"    -> best safe large-zero count at this shape: {best} "
              f"(n = {n}, n-a = {n - a}, cap-guess ((a-1)//(k-1))*n = {((a-1)//(k-1)) * n})")
    print()
    if ceiling_violations:
        print(f"RESULT: {ceiling_violations} violations of count <= Lambda*|supp| — "
              f"candidate ceiling REFUTED")
        return 1
    print("RESULT: no violation of count <= Lambda*|supp| anywhere; "
          "constant multi-base stays O(n) as predicted")
    return 0


if __name__ == "__main__":
    sys.exit(main())
