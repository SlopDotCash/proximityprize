#!/usr/bin/env python3
"""Adversarial exact census of the P1 rate-quarter PREDECESSOR miniature (m=4).

P1 scaling (from _RateQuarterPredecessorFourPencilReduction.lean, namespace P1):
  n = 16m coordinates (smooth multiplicative subgroup), k = 4m (RS dimension),
  amplified core z with 6z = 53m - 8, predecessor threshold t = z + 2.
The open residual claims: every two-row stack has at most n MCA-bad scalars at
agreement threshold t.  (P1: m = 2^26, n = 2^30, t = 592794966.)

Miniature here: m = 4  ->  n = 64, k = 16, z = 34, t = 36 over F_193
(193 = 1 + 3*64, so F_193* contains the order-64 smooth domain and mu_16).
NOTE: the Lean lemma four_two_fresh_cover_card_le assumes 8 <= m; m = 4 is the
smallest arithmetically consistent analogue (6 | 53m-8 and 3 | m-1 need
m == 4 mod 6).  We use it as a structural laboratory, not a literal instance.

Adversarial configurations censused EXACTLY (complete list decoding):
  (B) two "one-fresh" pencils with joint cores of size t-1 = 35, core overlap
      exactly k-2+... = 14 (deficiency one, the maximum that avoids
      proportionality collapse), plus 8 free coordinates each prescribing one
      fresh gamma to each line.  Predicted badCount = 2(n-t+1) = 58 <= 64.
  (C) three pencils with cores 35/35/34 realized through the mu_16 fibre
      ansatz (cubic potentials q12, q23, q13 = q12 + q23 all splitting over
      mu_16) - the maximal 3-core packing; the forced structure collapses the
      coordinate->gamma map to a global Moebius function (injective), predicted
      badCount ~ 50.
  (D) two pencils with core overlap 15 = k-1 (maximal): forces the intercept
      and slope differences to be proportional, i.e. concurrent lines; all
      cross gammas collapse to a single scalar.  Predicted badCount small.
  (E) one-coordinate perturbations of the extremal stack (B).

Census exactness: for each gamma, a multiplicity-2 Guruswami-Sudan
interpolation Q(X,Y) of (1,k-1)-weighted degree D = 2t-1 with
#monomials > 3n constraints guarantees every degree-<k polynomial with
agreement >= t satisfies (Y - q) | Q.  Y-roots are extracted with a
Roth-Ruckenstein search; each candidate is verified by direct agreement
counting, and MCA-badness of gamma is: some candidate q has
|Agree(q, u0+gamma*u1)| >= t whose agreement set admits no joint pair
(u0|S, u1|S both degree < k).  This matches mcaEvent of
ArkLib/Data/CodingTheory/ProximityGap/Errors.lean (subsets S of a full
agreement set only make non-jointness harder, so testing full agreement sets
is complete).

Cross-validation: the known F97 [32,8] smooth stack (m=2 analogue) is run
through the same engine and must reproduce 36 bad at agreement 17 and 0 bad
at agreement 18 (matching probe_rate_quarter_smooth_next_lattice_gs.py).

Deterministic; numpy required; runtime ~ a few minutes.
"""

from __future__ import annotations

import itertools
import json
import random
import sys
from math import comb

import numpy as np


# ----------------------------------------------------------------------
# generic modular polynomial helpers (coefficient lists, low degree first)
# ----------------------------------------------------------------------

def trim(a, p):
    a = [x % p for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def padd(a, b, p):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return trim(out, p)


def pscale(c, a, p):
    return trim([c * x % p for x in a], p)


def psub(a, b, p):
    return padd(a, pscale(-1, b, p), p)


def pmul(a, b, p):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % p
    return trim(out, p)


def peval(a, x, p):
    out = 0
    for c in reversed(a):
        out = (out * x + c) % p
    return out


def pdeg(a):
    return len(trim(a, 10**9)) - 1 if any(a) else -1


def interpolate(points, p):
    out = [0]
    for i, (x, y) in enumerate(points):
        basis = [1]
        den = 1
        for j, (z, _) in enumerate(points):
            if i == j:
                continue
            basis = pmul(basis, [(-z) % p, 1], p)
            den = den * (x - z) % p
        out = padd(out, pscale(y * pow(den, p - 2, p), basis, p), p)
    return trim(out, p)


def vanishing(points, p):
    out = [1]
    for z in points:
        out = pmul(out, [(-z) % p, 1], p)
    return out


# ----------------------------------------------------------------------
# exact complete list decoding census engine
# ----------------------------------------------------------------------

class Census:
    def __init__(self, p, n, k, t, xs):
        self.p, self.n, self.k, self.t = p, n, k, t
        self.xs = xs
        self.D = 2 * t - 1
        self.monomials = [
            (i, j)
            for j in range(self.D // (k - 1) + 1)
            for i in range(self.D - (k - 1) * j + 1)
        ]
        assert len(self.monomials) > 3 * n, "GS mult-2 parameter check failed"
        assert 2 * t > self.D

    def nullspace_vector(self, M):
        p = self.p
        A = M.astype(np.int64) % p
        rows, cols = A.shape
        pivots = []
        r = 0
        for c in range(cols):
            pr = None
            for i in range(r, rows):
                if A[i, c]:
                    pr = i
                    break
            if pr is None:
                continue
            A[[r, pr]] = A[[pr, r]]
            A[r] = A[r] * pow(int(A[r, c]), p - 2, p) % p
            f = A[:, c].copy()
            f[r] = 0
            A = (A - np.outer(f, A[r])) % p
            pivots.append((r, c))
            r += 1
            if r == rows:
                break
        pivot_cols = {c for _, c in pivots}
        free = next(c for c in range(cols) if c not in pivot_cols)
        v = np.zeros(cols, dtype=np.int64)
        v[free] = 1
        for rr, cc in pivots:
            v[cc] = (-A[rr, free]) % p
        assert (M.astype(object) @ v % p == 0).all()
        assert v.any()
        return [int(x) for x in v]

    def interpolation_poly(self, word):
        """Q with multiplicity 2 at all (x_i, w_i); returns list c[j] = X-poly."""
        p = self.p
        rows = []
        for x, w in zip(self.xs, word):
            xa = [pow(x, a, p) for a in range(self.D + 1)]
            wb = [pow(w, b, p) for b in range(self.D // (self.k - 1) + 1)]
            r0, r1, r2 = [], [], []
            for a, b in self.monomials:
                r0.append(xa[a] * wb[b] % p)
                r1.append(a * xa[a - 1] * wb[b] % p if a else 0)
                r2.append(b * xa[a] * wb[b - 1] % p if b else 0)
            rows += [r0, r1, r2]
        v = self.nullspace_vector(np.array(rows, dtype=np.int64))
        jmax = self.D // (self.k - 1)
        c = [[0] * (self.D + 1) for _ in range(jmax + 1)]
        for coeff, (a, b) in zip(v, self.monomials):
            c[b][a] = coeff
        return [trim(cj, p) for cj in c]

    def y_roots(self, c):
        """All q, deg<k, with Q(X,q(X)) == 0 mod X^k (superset of exact roots),
        by Roth-Ruckenstein."""
        p, k = self.p, self.k
        results = []

        def strip(c):
            if all(len(cj) == 1 and cj[0] == 0 for cj in c):
                return None  # identically zero
            v = min(
                next(i for i, x in enumerate(cj) if x)
                for cj in c if any(cj)
            )
            if v:
                c = [cj[v:] if any(cj) else cj for cj in c]
                c = [trim(cj if cj else [0], p) for cj in c]
            return c

        def rec(c, depth, acc):
            c = strip(c)
            if c is None:
                # Q became identically 0: every continuation is a root mod X^k.
                # Complete by taking acc padded with zeros (verification later
                # filters); to stay complete we abort loudly instead.
                raise RuntimeError("degenerate zero interpolation polynomial")
            # roots of R(Y) = sum c_j(0) Y^j
            r = [cj[0] if cj else 0 for cj in c]
            roots = [y0 for y0 in range(p)
                     if sum(rc * pow(y0, j, p) for j, rc in enumerate(r)) % p == 0]
            for y0 in roots:
                if depth == k - 1:
                    results.append(acc + [y0])
                    continue
                # substitute Y -> X*Y + y0
                jmax = len(c) - 1
                newc = [[0] for _ in range(jmax + 1)]
                for i in range(jmax + 1):
                    acc_poly = [0]
                    for j in range(i, jmax + 1):
                        acc_poly = padd(
                            acc_poly,
                            pscale(comb(j, i) * pow(y0, j - i, p), c[j], p), p)
                    # multiply by X^i
                    newc[i] = trim([0] * i + acc_poly, p)
                rec(newc, depth + 1, acc + [y0])

        rec(c, 0, [])
        uniq = []
        seen = set()
        for q in results:
            key = tuple(trim(q, p))
            if key not in seen:
                seen.add(key)
                uniq.append(trim(q, p))
        return uniq

    def row_deg_lt_k(self, row, support):
        if len(support) <= self.k:
            return True
        q = interpolate([(self.xs[i], row[i]) for i in support[:self.k]], self.p)
        return all(peval(q, self.xs[i], self.p) == row[i] for i in support)

    def gamma_report(self, u0, u1, gamma):
        p = self.p
        word = [(a + gamma * b) % p for a, b in zip(u0, u1)]
        c = self.interpolation_poly(word)
        out = []
        for q in self.y_roots(c):
            support = [i for i, x in enumerate(self.xs)
                       if peval(q, x, p) == word[i]]
            if len(support) < self.t:
                continue
            joint = (self.row_deg_lt_k(u0, support)
                     and self.row_deg_lt_k(u1, support))
            out.append((tuple(q), len(support), joint))
        return out

    def full_census(self, u0, u1, label):
        bad = []
        listing = {}
        for gamma in range(self.p):
            rep = self.gamma_report(u0, u1, gamma)
            if rep:
                listing[gamma] = rep
            if any(not joint for (_, _, joint) in rep):
                bad.append(gamma)
        print(f"[{label}] badCount = {len(bad)}  (budget n = {self.n}; "
              f"holds = {len(bad) <= self.n})")
        return bad, listing


# ----------------------------------------------------------------------
# witness-level census (lower bound; used as cross-check)
# ----------------------------------------------------------------------

def witness_census(p, xs, t, lines, cores, u0, u1):
    """lines: list of (a_poly, r_poly); cores: list of index sets."""
    from collections import defaultdict
    per_line_gamma = [defaultdict(list) for _ in lines]
    for li, (a, r) in enumerate(lines):
        for i, x in enumerate(xs):
            if i in cores[li]:
                continue
            da = (u0[i] - peval(a, x, p)) % p
            dr = (peval(r, x, p) - u1[i]) % p
            if dr == 0:
                continue
            per_line_gamma[li][da * pow(dr, p - 2, p) % p].append(i)
    bad = set()
    for li, (a, r) in enumerate(lines):
        for g, fresh in per_line_gamma[li].items():
            if len(cores[li]) + len(fresh) >= t:
                bad.add(g)
    return bad, per_line_gamma


# ----------------------------------------------------------------------
# field / domain setup
# ----------------------------------------------------------------------

def order_element(p, order):
    for g in range(2, p):
        if pow(g, (p - 1) // 2, p) != 1:  # crude primitive-ish search
            h = pow(g, (p - 1) // order, p)
            # check exact order
            ok = pow(h, order, p) == 1
            for d in (2, order // 2):
                if order % 2 == 0 and pow(h, order // 2, p) == 1:
                    ok = False
                break
            if ok:
                return h
    raise RuntimeError("no order element")


def build_domain(p, n):
    h = None
    for g in range(2, p):
        cand = pow(g, (p - 1) // n, p)
        seen = set()
        x = 1
        good = True
        for _ in range(n):
            x = x * cand % p
        pts = []
        x = 1
        for _ in range(n):
            pts.append(x)
            x = x * cand % p
        if len(set(pts)) == n:
            return pts
    raise RuntimeError("no domain")


# ----------------------------------------------------------------------
# Part A: cross-validation on the known F97 [32,8] stack
# ----------------------------------------------------------------------

def part_a():
    P, N, K, OMEGA = 97, 32, 8, 28
    U0 = [0, 0, 77, 0, 0, 0, 0, 0, 0, 59, 53, 54, 54, 26, 84, 45,
          0, 0, 20, 0, 0, 0, 0, 0, 0, 38, 44, 43, 43, 71, 13, 52]
    U1 = [0, 0, 46, 0, 0, 0, 0, 0, 0, 16, 24, 38, 36, 93, 7, 2,
          0, 0, 46, 0, 0, 0, 0, 0, 0, 16, 24, 38, 36, 93, 7, 2]
    xs = [pow(OMEGA, i, P) for i in range(N)]
    for t, expected in ((17, 36), (18, 0)):
        eng = Census(P, N, K, t, xs)
        bad, _ = eng.full_census(U0, U1, f"A:F97 t={t}")
        assert len(bad) == expected, (t, len(bad), expected)
    print("[A] cross-validation PASSED (36 bad @17, 0 bad @18)")


# ----------------------------------------------------------------------
# Part B: two one-fresh pencils, deficiency-one overlap, m=4 / F193
# ----------------------------------------------------------------------

P4, N4, K4, T4 = 193, 64, 16, 36


def build_config_B():
    p, n, k, t = P4, N4, K4, T4
    xs = build_domain(p, n)
    dom = set(xs)
    rng = random.Random(20260710)
    a1 = [rng.randrange(p) for _ in range(k)]
    r1 = [rng.randrange(p) for _ in range(k)]
    P12 = list(range(14))            # core overlap (indices into xs)
    priv1 = list(range(14, 35))      # 21
    priv2 = list(range(35, 56))      # 21
    free = list(range(56, 64))       # 8
    Z = vanishing([xs[i] for i in P12], p)
    s = next(v for v in range(2, p) if v not in dom)
    sp_ = next(v for v in range(s + 1, p) if v not in dom)
    A12 = pmul(Z, [(-s) % p, 1], p)
    R12 = pmul(Z, [(-sp_) % p, 1], p)
    a2 = psub(a1, A12, p)
    r2 = psub(r1, R12, p)
    assert pdeg(a2) < k and pdeg(r2) < k
    u0 = [0] * n
    u1 = [0] * n
    core1 = set(P12) | set(priv1)
    core2 = set(P12) | set(priv2)
    for i in core1:
        u0[i] = peval(a1, xs[i], p)
        u1[i] = peval(r1, xs[i], p)
    for i in set(priv2):
        u0[i] = peval(a2, xs[i], p)
        u1[i] = peval(r2, xs[i], p)
    # Moebius map phi(x) = -(x-s)/(x-s') gives every cross gamma
    phi_all = {(-(x - s) * pow(x - sp_, p - 2, p)) % p for x in xs}
    banned = phi_all | {0}
    fresh_gammas = [g for g in range(1, p) if g not in banned][:16]
    assert len(fresh_gammas) == 16
    for idx, i in enumerate(free):
        g1, g2 = fresh_gammas[2 * idx], fresh_gammas[2 * idx + 1]
        x = xs[i]
        v1 = (peval(a1, x, p) + g1 * peval(r1, x, p)) % p
        v2 = (peval(a2, x, p) + g2 * peval(r2, x, p)) % p
        inv = pow(g1 - g2, p - 2, p)
        b = (v1 - v2) * inv % p          # u1
        a = (v1 - g1 * b) % p            # u0
        u0[i], u1[i] = a, b
    # exact core check
    c1 = {i for i, x in enumerate(xs)
          if peval(a1, x, p) == u0[i] and peval(r1, x, p) == u1[i]}
    c2 = {i for i, x in enumerate(xs)
          if peval(a2, x, p) == u0[i] and peval(r2, x, p) == u1[i]}
    assert c1 == core1 and c2 == core2, (len(c1), len(c2))
    assert len(c1 & c2) == 14
    return xs, u0, u1, [(a1, r1), (a2, r2)], [core1, core2]


def part_b():
    xs, u0, u1, lines, cores = build_config_B()
    eng = Census(P4, N4, K4, T4, xs)
    wit, _ = witness_census(P4, xs, T4, lines, cores, u0, u1)
    print(f"[B] witness-level badCount = {len(wit)} (predicted 58)")
    bad, listing = eng.full_census(u0, u1, "B:two one-fresh pencils m=4")
    assert wit <= set(bad), "census missed a witnessed bad gamma"
    # anatomy
    on_line = {0: 0, 1: 0, "other": 0}
    for g in bad:
        qs = {q for (q, _, joint) in listing[g] if not joint}
        hit = False
        for li, (a, r) in enumerate(lines):
            ql = tuple(trim(padd(a, pscale(g, r, P4), P4), P4))
            if ql in qs:
                on_line[li] += 1
                hit = True
        if not hit:
            on_line["other"] += 1
    print(f"[B] anatomy: bad-gamma explanations per pencil: {on_line}")
    return xs, u0, u1, len(bad)


# ----------------------------------------------------------------------
# Part C: three-line fibre-ansatz config 35/35/34, m=4
# ----------------------------------------------------------------------

def cubic_splitting_pair(p, mu16):
    """find root triples R1,R2 in mu16 (disjoint) and beta with
    q13 = prod(y-R1) + beta*prod(y-R2) splitting over mu16 with 3 fresh roots."""
    mu = sorted(mu16)
    for R1 in itertools.combinations(mu, 3):
        rem1 = [y for y in mu if y not in R1]
        for R2 in itertools.combinations(rem1, 3):
            rem = [y for y in rem1 if y not in R2]
            from collections import defaultdict
            byb = defaultdict(list)
            for y in rem:
                f = 1
                h = 1
                for r in R1:
                    f = f * (y - r) % p
                for r in R2:
                    h = h * (y - r) % p
                if h == 0:
                    continue
                byb[(-f) * pow(h, p - 2, p) % p].append(y)
            for beta, ys in byb.items():
                if len(ys) >= 3 and beta != 0 and (1 + beta) % p != 0:
                    return R1, R2, beta, tuple(ys[:3])
    return None


def build_config_C():
    p, n, k, t = P4, N4, K4, T4
    xs = build_domain(p, n)
    dom = set(xs)
    mu16 = {pow(x, 4, p) for x in xs}
    assert len(mu16) == 16
    found = cubic_splitting_pair(p, mu16)
    assert found, "no splitting cubic pair over this field"
    R1, R2, beta, R3 = found
    print(f"[C] cubic potentials: roots q12={R1} q23={R2} beta={beta} q13roots={R3}")

    def cubic(roots, scale):
        q = [scale]
        for r in roots:
            q = pmul(q, [(-r) % p, 1], p)
        return q

    q12 = cubic(R1, 1)
    q23 = cubic(R2, beta)
    q13 = padd(q12, q23, p)
    for y in R3:
        assert peval(q13, y, p) == 0
    # compose with y = x^4
    def comp4(q):
        out = [0]
        for j, c in enumerate(q):
            out = padd(out, pscale(c, [0] * (4 * j) + [1], p), p)
        return out

    # g, h cubics sharing w1,w2 in domain; third roots off-domain.
    # w1, w2 must avoid all nine fibres.
    allroots = set(R1) | set(R2) | set(R3)
    wcands = [x for x in xs if pow(x, 4, p) not in allroots]
    w1, w2 = wcands[0], wcands[1]
    off = [v for v in range(2, p) if v not in dom][:2]
    g = pmul(pmul([(-w1) % p, 1], [(-w2) % p, 1], p), [(-off[0]) % p, 1], p)
    h = pmul(pmul([(-w1) % p, 1], [(-w2) % p, 1], p), [(-off[1]) % p, 1], p)
    A12 = pmul(comp4(q12), g, p)
    A23 = pmul(comp4(q23), g, p)
    A13 = padd(A12, A23, p)
    R12 = pmul(comp4(q12), h, p)
    R23 = pmul(comp4(q23), h, p)
    R13 = padd(R12, R23, p)
    for poly in (A12, A23, A13, R12, R23, R13):
        assert pdeg(poly) <= k - 1
    rng = random.Random(77)
    a1 = [rng.randrange(p) for _ in range(k)]
    r1 = [rng.randrange(p) for _ in range(k)]
    a2, r2 = psub(a1, A12, p), psub(r1, R12, p)
    a3, r3 = psub(a1, A13, p), psub(r1, R13, p)

    def fib(roots):
        return {i for i, x in enumerate(xs) if pow(x, 4, p) in roots}

    iw1, iw2 = xs.index(w1), xs.index(w2)
    P12 = fib(R1) | {iw1, iw2}
    P23 = fib(R2) | {iw1, iw2}
    P13 = fib(R3) | {iw1, iw2}
    assert len(P12) == 14 and len(P23) == 14 and len(P13) == 14
    used = P12 | P23 | P13
    rest = [i for i in range(n) if i not in used]
    assert len(rest) == 26, len(rest)
    priv1, priv2, priv3 = rest[:9], rest[9:18], rest[18:26]
    core1 = P12 | P13 | set(priv1)
    core2 = P12 | P23 | set(priv2)
    core3 = P13 | P23 | set(priv3)
    assert (len(core1), len(core2), len(core3)) == (35, 35, 34)
    u0, u1 = [0] * n, [0] * n
    for i in core1:
        u0[i], u1[i] = peval(a1, xs[i], p), peval(r1, xs[i], p)
    for i in core2 - core1:
        u0[i], u1[i] = peval(a2, xs[i], p), peval(r2, xs[i], p)
    for i in core3 - core1 - core2:
        u0[i], u1[i] = peval(a3, xs[i], p), peval(r3, xs[i], p)
    c = [{i for i, x in enumerate(xs)
          if peval(a, x, p) == u0[i] and peval(r, x, p) == u1[i]}
         for (a, r) in ((a1, r1), (a2, r2), (a3, r3))]
    assert c[0] == core1 and c[1] == core2 and c[2] == core3, \
        [len(ci) for ci in c]
    return xs, u0, u1, [(a1, r1), (a2, r2), (a3, r3)], [core1, core2, core3]


def part_c():
    xs, u0, u1, lines, cores = build_config_C()
    eng = Census(P4, N4, K4, T4, xs)
    wit, _ = witness_census(P4, xs, T4, lines, cores, u0, u1)
    print(f"[C] witness-level badCount = {len(wit)}")
    bad, listing = eng.full_census(u0, u1, "C:three-line 35/35/34 m=4")
    assert wit <= set(bad)
    return len(bad)


# ----------------------------------------------------------------------
# Part D: maximal overlap 15 -> concurrency collapse
# ----------------------------------------------------------------------

def part_d():
    p, n, k, t = P4, N4, K4, T4
    xs = build_domain(p, n)
    rng = random.Random(99)
    a1 = [rng.randrange(p) for _ in range(k)]
    r1 = [rng.randrange(p) for _ in range(k)]
    P12 = list(range(15))
    Z = vanishing([xs[i] for i in P12], p)
    A12 = pscale(3, Z, p)
    R12 = pscale(5, Z, p)      # proportional -> concurrent lines
    a2, r2 = psub(a1, A12, p), psub(r1, R12, p)
    core1 = set(P12) | set(range(15, 35))
    core2 = set(P12) | set(range(35, 55))
    u0, u1 = [0] * n, [0] * n
    for i in core1:
        u0[i], u1[i] = peval(a1, xs[i], p), peval(r1, xs[i], p)
    for i in core2 - core1:
        u0[i], u1[i] = peval(a2, xs[i], p), peval(r2, xs[i], p)
    for i in range(55, 64):    # free coords: line values of line1 at gamma.. keep neutral
        u0[i], u1[i] = rng.randrange(p), rng.randrange(p)
    eng = Census(p, n, k, t, xs)
    bad, _ = eng.full_census(u0, u1, "D:overlap-15 concurrent pair m=4")
    return len(bad)


# ----------------------------------------------------------------------
# Part E: perturbations of the extremal B stack
# ----------------------------------------------------------------------

def part_e(xs, u0, u1):
    eng = Census(P4, N4, K4, T4, xs)
    results = []
    cases = [("u0", 0, 1), ("u0", 20, 1), ("u0", 40, 1), ("u0", 60, 1),
             ("u1", 5, 1), ("u1", 45, 1), ("u1", 60, 1), ("u0", 13, 7)]
    for row, idx, amt in cases:
        v0, v1 = u0.copy(), u1.copy()
        (v0 if row == "u0" else v1)[idx] = \
            ((v0 if row == "u0" else v1)[idx] + amt) % P4
        bad, _ = eng.full_census(v0, v1, f"E:{row}[{idx}]+={amt}")
        results.append((f"{row}[{idx}]+={amt}", len(bad)))
    return results


def main():
    part_a()
    xs, u0, u1, count_b = part_b()
    count_c = part_c()
    count_d = part_d()
    pert = part_e(xs, u0, u1)
    summary = {
        "miniature": {"m": 4, "n": N4, "k": K4, "z": 34, "t": T4, "field": P4},
        "config_B_two_one_fresh_pencils": count_b,
        "config_C_three_line_35_35_34": count_c,
        "config_D_concurrent_overlap15": count_d,
        "perturbations_of_B": pert,
        "budget_n": N4,
        "over_budget_found": any(
            c > N4 for c in
            [count_b, count_c, count_d] + [c for _, c in pert]),
    }
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
