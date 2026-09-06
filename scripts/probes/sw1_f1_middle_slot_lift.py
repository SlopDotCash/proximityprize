#!/usr/bin/env python3
"""
SW1-F1 -- lift test of the SYZ71 (6,6,6) linear-slot occupant AND of the p-uniform
coset family that refutes `UniformSylvesterInjective` (Frontier/_SW1_F1_UniformSylvesterRefuted).

Deterministic; prints PASS/FAIL and exits nonzero on FAIL.  Exact modular arithmetic only
(Python ints; numpy int64 with an overflow-safe split product for p up to 2^31).

PART A  Replicate the SYZ71 F_41, mu_20 occupant of the first middle slot (6,6,6) at
        product-degree 7 (linear cofactors), verify it exactly, and note that it is itself an
        in-budget syzygy (product 7 <= budget k-1-t = 7): `SylvesterInjective` fails there.
PART B  Exact SYZ32/SYZ53 lift test of that occupant's cores (n=20, k=10, s=14) at p=41:
        max mca-bad scalar count on all-cores-degenerate stacks vs budget n-1=19 and pencil
        ceiling 3(n-s)=18.
PART C  Mandatory p-sweep of the (6,6,6) linear slot at n=20: sampled occupancy count at
        primes p == 1 (mod 20) up to ~2^10 (occupants are accidental level-set coincidences,
        expected ~ N*28/p^3), and the lift test of every occupant found.
PART D  The COSET FAMILY (Lean theorem `coset_family_refutes_F1`): n = 4d, three cosets of mu_d
        as S_AB,S_AC,S_BC, T inside the fourth coset; W_j = X^d - c_j, constant syzygy
        (c1-c2)W_0 - (c0-c2)W_1 + (c0-c1)W_2 = 0 at EVERY prime.  Verify exactly at n=16
        (d=4,t=3) and n=20 (d=5,t=4) for primes from the small-field regime to ~2^31, and run
        the exact lift test: is the p-uniform SylvesterInjective failure stack-harmless?

Exactness tool (SYZ53): a line word u0+z*u1 is s-close iff for some s-subset S the RS_k|S
parity checks H_S (GRS dual, dim s-k) satisfy H_S(u0)+z*H_S(u1)=0 -- affine in z, so each S
contributes at most one candidate z (or all of F when both vanish: common agreement set,
mca-correlated, filtered per SYZ32).  For n<=20, all C(n,s) subsets are enumerated: the bad-z
set of every stack is EXACT at any prime.
"""
from __future__ import annotations

import itertools
import os
import random
import sys
import time

import numpy as np

# ----------------------------------------------------------------------------- primes
def is_prime(m: int) -> bool:
    if m < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % q == 0:
            return m == q
    d = m - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(r - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def next_prime_1modn(target: int, n: int) -> int:
    p = target + ((1 - target) % n)
    if p < target:
        p += n
    while not is_prime(p):
        p += n
    return p


def prime_factors(m: int) -> set[int]:
    fs: set[int] = set()
    d = 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d)
            m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs


def primitive_root(p: int) -> int:
    fs = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise RuntimeError("no primitive root")


def mu_domain(n: int, p: int) -> list[int]:
    assert (p - 1) % n == 0
    w = pow(primitive_root(p), (p - 1) // n, p)
    pts = [pow(w, i, p) for i in range(n)]
    assert len(set(pts)) == n
    return pts


# ----------------------------------------------------------------------------- F_p linear algebra
def rref_null(rows: list[list[int]], ncols: int, p: int) -> tuple[int, list[list[int]]]:
    """Rank and a basis of the right null space {v : rows . v = 0} over F_p."""
    M = [[x % p for x in r] for r in rows]
    piv: dict[int, int] = {}
    r = 0
    for c in range(ncols):
        pr = next((i for i in range(r, len(M)) if M[i][c]), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        piv[c] = r
        r += 1
        if r == len(M):
            break
    free = [c for c in range(ncols) if c not in piv]
    null = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for c, rr in piv.items():
            v[c] = (-M[rr][fc]) % p
        null.append(v)
    return r, null


def gf_rank(rows: list[list[int]], p: int) -> int:
    return rref_null(rows, len(rows[0]), p)[0]


# ----------------------------------------------------------------------------- polynomials
def poly_from_roots(roots: list[int], p: int) -> list[int]:
    c = [1]
    for r in roots:
        nc = [0] * (len(c) + 1)
        for i, ci in enumerate(c):
            nc[i] = (nc[i] - r * ci) % p
            nc[i + 1] = (nc[i + 1] + ci) % p
        c = nc
    return c


def poly_mul(a: list[int], b: list[int], p: int) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                out[i + j] = (out[i + j] + ai * bj) % p
    return out


def poly_add(a: list[int], b: list[int], p: int) -> list[int]:
    n = max(len(a), len(b))
    return [((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % p for i in range(n)]


def poly_scale(a: list[int], c: int, p: int) -> list[int]:
    return [(x * c) % p for x in a]


def poly_deg(a: list[int]) -> int:
    d = len(a) - 1
    while d > 0 and a[d] == 0:
        d -= 1
    return d if any(a) else -1


def poly_eval(a: list[int], x: int, p: int) -> int:
    acc = 0
    for c in reversed(a):
        acc = (acc * x + c) % p
    return acc


def vanishing_eval(omega: int, support: list[int], p: int) -> int:
    acc = 1
    for s in support:
        acc = acc * ((omega - s) % p) % p
    return acc


# ----------------------------------------------------------------------------- exact bad-z engine
def matvec_mod(H: np.ndarray, u: np.ndarray, p: int) -> np.ndarray:
    """(H @ u) mod p for H (..., m) int64 entries in [0,p), u (m,) in [0,p); overflow-safe for
    p < 2^31 and m <= 32 by splitting u into 15-bit halves."""
    if p < (1 << 24):
        return np.einsum("...j,j->...", H, u) % p
    lo = u & 0x7FFF
    hi = u >> 15
    s_lo = np.einsum("...j,j->...", H, lo) % p
    s_hi = np.einsum("...j,j->...", H, hi) % p
    return (s_hi * (1 << 15) + s_lo) % p


class ExactCloseness:
    """All s-subsets of range(n) with GRS parity checks of RS_k on alpha|S (dim s-k)."""

    def __init__(self, alpha: list[int], k: int, s: int, p: int):
        self.alpha, self.k, self.s, self.p = alpha, k, s, p
        n = len(alpha)
        self.n = n
        subs = list(itertools.combinations(range(n), s))
        self.subs = np.array(subs, dtype=np.int64)           # (m, s)
        m = len(subs)
        r = s - k
        H = np.zeros((m, r, s), dtype=np.int64)
        for mi, S in enumerate(subs):
            a = [alpha[j] for j in S]
            for j in range(s):
                den = 1
                aj = a[j]
                for l in range(s):
                    if l != j:
                        den = den * ((aj - a[l]) % p) % p
                cj = pow(den, p - 2, p)
                pw = cj
                for i in range(r):
                    H[mi, i, j] = pw
                    pw = pw * aj % p
        self.H = H
        # sanity: parity checks annihilate the k monomial codewords on a few subsets
        for mi in (0, m // 2, m - 1):
            S = subs[mi]
            for e in range(k):
                v = np.array([pow(alpha[j], e, p) for j in S], dtype=np.int64)
                assert not np.any(matvec_mod(H[mi], v, p)), "GRS parity construction broken"

    def bad_z(self, u0: list[int], u1: list[int]):
        """Return (bad_set, inf_close, mca)."""
        p = self.p
        U0 = np.array(u0, dtype=np.int64) % p
        U1 = np.array(u1, dtype=np.int64) % p
        g0 = U0[self.subs]                                  # (m, s)
        g1 = U1[self.subs]
        a0 = np.einsum("mrs,ms->mr", self.H, g0) % p if p < (1 << 24) else \
            (np.einsum("mrs,ms->mr", self.H, (g0 >> 15)) % p * (1 << 15)
             + np.einsum("mrs,ms->mr", self.H, (g0 & 0x7FFF)) % p) % p
        a1 = np.einsum("mrs,ms->mr", self.H, g1) % p if p < (1 << 24) else \
            (np.einsum("mrs,ms->mr", self.H, (g1 >> 15)) % p * (1 << 15)
             + np.einsum("mrs,ms->mr", self.H, (g1 & 0x7FFF)) % p) % p
        a1zero = ~np.any(a1, axis=1)
        a0zero = ~np.any(a0, axis=1)
        inf = bool(a1zero.any())
        mca = bool((a1zero & a0zero).any())
        # parallel test on rows with a1 != 0: all 2x2 minors vanish
        rows = np.nonzero(~a1zero)[0]
        A0 = a0[rows]
        A1 = a1[rows]
        r = A0.shape[1]
        par = np.ones(len(rows), dtype=bool)
        for i in range(r):
            for j in range(i + 1, r):
                par &= ((A0[:, i] * A1[:, j] - A0[:, j] * A1[:, i]) % p) == 0
        bad = set()
        for idx in np.nonzero(par)[0]:
            row0 = A0[idx]
            row1 = A1[idx]
            c = int(np.nonzero(row1)[0][0])
            z = (-int(row0[c]) * pow(int(row1[c]), p - 2, p)) % p
            bad.add(z)
        return bad, inf, mca


def core_parity_rows(alpha: list[int], k: int, core: list[int], p: int) -> list[list[int]]:
    """RS_k parity checks on the core (dim |core|-k), embedded in F^n."""
    n = len(alpha)
    s = len(core)
    a = [alpha[j] for j in core]
    out = []
    for i in range(s - k):
        h = [0] * n
        for jj, j in enumerate(core):
            den = 1
            for l in range(s):
                if l != jj:
                    den = den * ((a[jj] - a[l]) % p) % p
            h[j] = pow(den, p - 2, p) * pow(a[jj], i, p) % p
        out.append(h)
    return out


def lift_test(alpha: list[int], k: int, s: int, p: int, cores: list[list[int]],
              engine: ExactCloseness, seed: int, trials: int) -> dict:
    """SYZ32/SYZ53 exact lift test: max mca-bad count over all-cores-degenerate stacks."""
    n = len(alpha)
    rng = random.Random(seed)
    par = [core_parity_rows(alpha, k, C, p) for C in cores]
    maxbad = 0
    maxraw = 0
    stacks = 0
    mcas = 0
    dist: dict[int, int] = {}
    for _ in range(trials):
        zs = rng.sample(range(1, p), 3)
        rows = []
        for i in range(3):
            for h in par[i]:
                rows.append(h + [(zs[i] * x) % p for x in h])
        _, null = rref_null(rows, 2 * n, p)
        if not null:
            continue
        u = [0] * (2 * n)
        for b in null:
            c = rng.randrange(p)
            if c:
                for j in range(2 * n):
                    u[j] = (u[j] + c * b[j]) % p
        u0, u1 = u[:n], u[n:]
        if not any(u1):
            continue
        bad, inf, mca = engine.bad_z(u0, u1)
        raw = len(bad) + (1 if inf else 0)
        maxraw = max(maxraw, raw)
        if mca:
            mcas += 1
            continue
        stacks += 1
        maxbad = max(maxbad, raw)
        dist[raw] = dist.get(raw, 0) + 1
    return dict(maxbad=maxbad, maxraw=maxraw, stacks=stacks, mca=mcas, dist=dist)


def cores_of(S_AB, S_AC, S_BC, T):
    A = sorted(set(S_AB) | set(S_AC) | set(T))
    B = sorted(set(S_AB) | set(S_BC) | set(T))
    C = sorted(set(S_AC) | set(S_BC) | set(T))
    return [A, B, C]


# ----------------------------------------------------------------------------- linear-slot search
def linear_slot_rows(pts, S_AC, S_BC, p):
    excl = set(S_AC) | set(S_BC)
    omegas, rows = [], []
    for om in pts:
        if om in excl:
            continue
        wac = vanishing_eval(om, S_AC, p)
        wbc = vanishing_eval(om, S_BC, p)
        rows.append([wac, om * wac % p, wbc, om * wbc % p])
        omegas.append(om)
    return omegas, rows


def find_linear_occupant(pts, S_AC, S_BC, p, d):
    omegas, rows = linear_slot_rows(pts, S_AC, S_BC, p)
    for idxs in itertools.combinations(range(len(omegas)), d):
        block = [rows[i] for i in idxs]
        if gf_rank(block, p) < 4:
            return [omegas[i] for i in idxs], block
    return None, None


def verify_linear_occupant(pts, S_AC, S_BC, S_AB, p, d):
    """Exact verification: kernel (u0,u1,v0,v1) with s_AC=u0+u1X, s_BC=v0+v1X, not both constant,
    P = s_AC W_AC + s_BC W_BC vanishes on S_AB, deg P = d+1, product degrees all d+1."""
    omegas, rows = linear_slot_rows(pts, S_AC, S_BC, p)
    block = [rows[omegas.index(x)] for x in S_AB]
    r, null = rref_null(block, 4, p)
    assert r < 4 and null, "occupant has full rank"
    u0, u1, v0, v1 = null[0]
    assert u1 or v1, "kernel is a constant pair (floor class), not a linear slot"
    WAC = poly_from_roots(S_AC, p)
    WBC = poly_from_roots(S_BC, p)
    WAB = poly_from_roots(S_AB, p)
    P = poly_add(poly_mul([u0, u1], WAC, p), poly_mul([v0, v1], WBC, p), p)
    assert all(poly_eval(P, x, p) == 0 for x in S_AB), "P does not vanish on S_AB"
    assert poly_deg(P) == d + 1, f"deg P = {poly_deg(P)} != {d+1}"
    # P = s_AB * W_AB with s_AB linear: divide exactly
    # synthetic: since W_AB monic of degree d and P vanishes on its d distinct roots, W_AB | P
    T = [x for x in omegas if x not in S_AB]
    assert all(poly_eval(P, x, p) != 0 for x in T), "P vanishes on a T point (bigger level set)"
    return (u0, u1, v0, v1), T


# ----------------------------------------------------------------------------- coset family
def coset_witness(pts, n, d, t, assign=(0, 1, 2, 3), tsel="first"):
    """Cosets C_j = {pts[j + 4i]}; S_AB=C_a, S_AC=C_b, S_BC=C_c, T subset of C_e (|T|=t)."""
    assert n == 4 * d
    cos = [[pts[(j + 4 * i) % n] for i in range(d)] for j in range(4)]
    a, b, c, e = assign
    Tc = cos[e]
    T = Tc[:t] if tsel == "first" else Tc[-t:]
    return cos[a], cos[b], cos[c], T


def verify_coset_syzygy(pts, S_AB, S_AC, S_BC, d, p):
    """Exact: W_j = X^d - c_j (binomials), and (c1-c2)W0 - (c0-c2)W1 + (c0-c1)W2 = 0, with
    c_j^4 = 1 pairwise distinct; also the SYZ38 window form W1*rAC - W2*rBC = W0*rAB."""
    W = [poly_from_roots(S, p) for S in (S_AB, S_AC, S_BC)]
    cs = []
    for w in W:
        assert len(w) == d + 1 and w[d] == 1 and all(x == 0 for x in w[1:d]), "not a binomial"
        c = (-w[0]) % p
        assert pow(c, 4, p) == 1, "constant not a 4th root of unity"
        cs.append(c)
    c0, c1, c2 = cs
    assert len({c0, c1, c2}) == 3, "cosets not distinct"
    syz = poly_add(poly_add(poly_scale(W[0], (c1 - c2) % p, p),
                            poly_scale(W[1], (-(c0 - c2)) % p, p), p),
                   poly_scale(W[2], (c0 - c1) % p, p), p)
    assert not any(syz), "binomial identity failed"
    rAC, rBC, rAB = (c0 - c2) % p, (c0 - c1) % p, (c1 - c2) % p
    lhs = poly_add(poly_scale(W[1], rAC, p), poly_scale(W[2], (-rBC) % p, p), p)
    rhs = poly_scale(W[0], rAB, p)
    assert poly_add(lhs, poly_scale(rhs, p - 1, p), p) == [0] * len(lhs) or \
        all(x == 0 for x in poly_add(lhs, poly_scale(rhs, p - 1, p), p)), "window form failed"
    assert rAC and rBC and rAB, "a cofactor vanished"
    return cs


# ----------------------------------------------------------------------------- main
def main() -> int:
    t0 = time.time()
    fails = 0
    print("=" * 96)
    print("SW1-F1: lift test of the SYZ71 (6,6,6) linear-slot occupant and of the p-uniform coset")
    print("        family refuting UniformSylvesterInjective (exact SYZ53 bad-z engine)")
    print("=" * 96)

    # ------------------------------------------------------------------ PART A
    print("\n[A] SYZ71 occupant, F_41, mu_20, (6,6,6), t=2 (k=10, budget k-1-t=7)")
    p, n, d, k = 41, 20, 6, 10
    pts = mu_domain(n, p)
    S_AC = [2, 25, 37, 23, 39, 1]
    S_BC = [8, 18, 16, 10, 5, 36]
    S_AB = [4, 21, 33, 40, 31, 9]
    try:
        mu = set(pts)
        assert set(S_AC + S_BC + S_AB) <= mu
        assert not (set(S_AC) & set(S_BC) or set(S_AC) & set(S_AB) or set(S_BC) & set(S_AB))
        ker, T = verify_linear_occupant(pts, S_AC, S_BC, S_AB, p, d)
        print(f"    kernel (u0,u1,v0,v1)={ker}  T={sorted(T)}  deg P = 7 = product-degree")
        print("    -> cofactor degrees (1,1,1) <= window k-1-m = 10-1-8 = 1: in-budget syzygy,")
        print("       SylvesterInjective FAILS on this triple at its SYZ38 window (middle-band class).")
        print("    [A] exact verification: OK")
    except AssertionError as e:
        print(f"    [A] FAIL: {e}")
        fails += 1
        T = []

    # ------------------------------------------------------------------ PART B
    print("\n[B] exact lift test of the occupant cores at p=41: n=20 k=10 s=14, budget 19, ceiling 18")
    s = 2 * d + 2
    eng20_41 = ExactCloseness(pts, k, s, p)
    cores = cores_of(S_AB, S_AC, S_BC, T)
    assert all(len(C) == s for C in cores)
    resB = lift_test(pts, k, s, p, cores, eng20_41, seed=101, trials=int(os.environ.get("SW1_B_TRIALS", "800")))
    print(f"    stacks(noncorr)={resB['stacks']} mca-filtered={resB['mca']}  max mca-bad={resB['maxbad']}  "
          f"max raw={resB['maxraw']}  dist(top)={sorted(resB['dist'].items())[-6:]}")
    print(f"    EXCESS vs ceiling 18: {resB['maxbad'] - 18:+d}   vs budget 19: {resB['maxbad'] - 19:+d}")

    # ------------------------------------------------------------------ PART C
    print("\n[C] p-sweep of the (6,6,6) linear slot at n=20 (sampled occupancy + lift of occupants)")
    primes20 = []
    for tgt in (41, 61, 101, 181, 241, 401, 601, 1021):
        q = next_prime_1modn(tgt, 20)
        if q not in primes20:
            primes20.append(q)
    NPAIRS = int(os.environ.get("SW1_C_PAIRS", "12000"))
    print(f"    primes == 1 mod 20: {primes20}; {NPAIRS} random disjoint (S_AC,S_BC) pairs each")
    print(f"    heuristic expectation ~ N*C(8,6)/p^3 = {NPAIRS}*28/p^3 (accidental Moebius level sets)")
    rowsC = []
    for q in primes20:
        ptsq = mu_domain(n, q)
        rng = random.Random(7_000 + q)
        hits = []
        for _ in range(NPAIRS):
            bag = ptsq[:]
            rng.shuffle(bag)
            SAC, SBC = bag[:d], bag[d:2 * d]
            SAB, _ = find_linear_occupant(ptsq, SAC, SBC, q, d)
            if SAB is not None:
                hits.append((SAC, SBC, SAB))
        exp = NPAIRS * 28 / q ** 3
        # lift-test up to 3 occupants
        lifted = []
        if hits:
            eng = eng20_41 if q == 41 else ExactCloseness(ptsq, k, s, q)
            for (SAC, SBC, SAB) in hits[:3]:
                try:
                    _, Tq = verify_linear_occupant(ptsq, SAC, SBC, SAB, q, d)
                except AssertionError as e:
                    print(f"    p={q}: occupant verification FAIL: {e}")
                    fails += 1
                    continue
                r = lift_test(ptsq, k, s, q, cores_of(SAB, SAC, SBC, Tq), eng, seed=11 + q,
                              trials=int(os.environ.get("SW1_C_TRIALS", "300")))
                lifted.append(r["maxbad"])
        rowsC.append((q, len(hits), exp, lifted))
        print(f"    p={q:<6} occupants={len(hits):<3} (expected~{exp:6.2f})  "
              f"lift max mca-bad over {len(lifted)} occupant(s): {lifted}   [ceiling 18, budget 19]")

    # ------------------------------------------------------------------ PART D
    print("\n[D] COSET FAMILY (p-uniform SylvesterInjective failure): n=4d, three cosets of mu_d + T in the 4th")
    configs = [(16, 4, 3), (20, 5, 4)]
    if os.environ.get("SW1_D_N24", "0") == "1":
        configs.append((24, 6, 5))
    rowsD = []
    for (nn, dd, tt) in configs:
        kk = nn // 2
        ss = 2 * dd + tt
        budget = nn - 1
        ceiling = 3 * (nn - ss)
        win = kk - 1 - (dd + tt)
        assert 3 * ss >= 2 * nn + 1 and dd + 1 + tt <= kk, "profile not interior/realizable"
        targets = [nn + 1, 97, 193, 1009, 10007, 1000003, 2 ** 31]
        primes = []
        for tg in targets:
            q = next_prime_1modn(tg, nn)
            if q not in primes:
                primes.append(q)
        if os.environ.get("SW1_QUICK", "0") == "1":
            primes = primes[:4]
        print(f"\n    config n={nn} d={dd} t={tt}: k={kk} s={ss} window k-1-m={win} (constant syzygy in-budget iff >=0)"
              f"  budget n-1={budget}  ceiling 3(n-s)={ceiling}")
        print(f"    primes == 1 mod {nn}: {primes}")
        trials = int(os.environ.get("SW1_D_TRIALS", "300" if nn <= 20 else "60"))
        for q in primes:
            ptsq = mu_domain(nn, q)
            eng = None
            tq = time.time()
            gmax = 0
            graw = 0
            gst = 0
            gmca = 0
            agg: dict[int, int] = {}
            variants = [((0, 1, 2, 3), "first"), ((1, 2, 3, 0), "last")]
            for vi, (assign, tsel) in enumerate(variants):
                SAB, SAC, SBC, T = coset_witness(ptsq, nn, dd, tt, assign, tsel)
                try:
                    cs = verify_coset_syzygy(ptsq, SAB, SAC, SBC, dd, q)
                except AssertionError as e:
                    print(f"      p={q} variant {vi}: coset syzygy verification FAIL: {e}")
                    fails += 1
                    continue
                if eng is None:
                    eng = ExactCloseness(ptsq, kk, ss, q)
                r = lift_test(ptsq, kk, ss, q, cores_of(SAB, SAC, SBC, T), eng, seed=31 + q + vi,
                              trials=trials)
                gmax = max(gmax, r["maxbad"])
                graw = max(graw, r["maxraw"])
                gst += r["stacks"]
                gmca += r["mca"]
                for kk2, v in r["dist"].items():
                    agg[kk2] = agg.get(kk2, 0) + v
            rowsD.append((nn, q, gmax, ceiling, budget))
            print(f"      p={q:<11} (log2={np.log2(q):5.2f})  binomial syzygy exact: OK  "
                  f"max mca-bad={gmax:<3} raw={graw:<3} EXCESS vs ceiling={gmax - ceiling:+d} "
                  f"vs budget={gmax - budget:+d}  stacks={gst} mca-filtered={gmca}  "
                  f"tail={sorted(agg.items())[-5:]}  [{time.time() - tq:.0f}s]")

    # ------------------------------------------------------------------ summary
    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print(f"  [A] SYZ71 occupant replicated and exactly verified: {'yes' if fails == 0 else 'see FAIL'}")
    print(f"  [B] occupant lift at p=41: max mca-bad {resB['maxbad']} (ceiling 18, budget 19)")
    print("  [C] linear-slot occupancy p-law (n=20):")
    for q, h, exp, lifted in rowsC:
        print(f"        p={q:<6} occupants={h:<3} expected~{exp:6.2f}  lifts={lifted}")
    print("  [D] coset family p-law (exact constant syzygy at every p; lift max mca-bad):")
    for nn, q, gmax, ceiling, budget in rowsD:
        print(f"        n={nn} p={q:<11} maxbad={gmax:<3} excess vs ceiling {gmax - ceiling:+d} vs budget {gmax - budget:+d}")
    print(f"\n  elapsed {time.time() - t0:.0f}s")
    print("  Lift counts are COMPUTATIONAL EVIDENCE (sampled stacks, exact per stack), not theorems.")
    if fails:
        print(f"\nFAIL ({fails} exact verification(s) failed)")
        return 1
    print("\nPASS (all exact verifications hold: occupant kernel, binomial syzygies, GRS parity checks)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
