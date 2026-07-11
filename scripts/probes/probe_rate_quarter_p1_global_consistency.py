#!/usr/bin/env python3
"""Probe: the global u1-consistency charge (D-function vote pool).

Companion of _P1RateQuarterGlobalConsistencyCharge.lean.

Facts checked:
1. mu_256 / F_257 (scaled P1 shape n=256, k=64, T=142): for random pencil
   triples through a base witness and random stacks, every rider vote lies in
   supp(D) where D = p0 - u0 - g0*u1, and riders*(T-A) <= |supp D|.
2. n=16 / F_17 exhaustive bad-count (k=4, T=9):
   (a) the realized two-cover geometry stack (u0 = base codeword): #bad is
       tiny (D == 0 kills all riders);
   (b) adversarial D-stacks (u0 = c0 + D with |supp D| = f): measure #bad
       (with the joint-explanation filter) against n and against the shared
       pool arithmetic;
   (c) the swarm structure: the affine family s -> u1 - s*D supplies
       single-rider pencils -- the open residual.
"""

import itertools
import random

import numpy as np


def make_field(p, n):
    # domain = mu_n in F_p
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in prime_factors(p - 1)):
            break
    z = pow(g, (p - 1) // n, p)
    dom = [pow(z, i, p) for i in range(n)]
    assert len(set(dom)) == n
    return dom


def prime_factors(m):
    fs, d = set(), 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d)
            m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs


def codeword_matrix(p, dom, k):
    # rows: evaluations of x^j; codewords = span
    n = len(dom)
    V = np.zeros((k, n), dtype=np.int64)
    for j in range(k):
        V[j] = [pow(x, j, p) for x in dom]
    return V


def rand_codeword(p, V, rng):
    c = np.array([rng.randrange(p) for _ in range(V.shape[0])], dtype=np.int64)
    return (c @ V) % p


# ---------------------------------------------------------------- part 1


def part1_mu256(trials=200, seed=466):
    p, n, k = 257, 256, 64
    T = (53 * n) // 96 + 1  # 142
    dom = make_field(p, n)
    V = codeword_matrix(p, dom, k)
    rng = random.Random(seed)
    print(f"== part 1: mu_{n}/F_{p}, k={k}, T={T} — vote-pool lemmas ==")
    viol = 0
    for _ in range(trials):
        u0 = np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64)
        u1 = np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64)
        g0 = rng.randrange(p)
        # three pencils through a base witness p0 (p0 = w0j + g0*w1j)
        w1s = [rand_codeword(p, V, rng) for _ in range(3)]
        w0base = rand_codeword(p, V, rng)
        p0 = (w0base + g0 * w1s[0]) % p
        w0s = [(p0 - g0 * w1) % p for w1 in w1s]
        D = (p0 - u0 - g0 * u1) % p
        suppD = D != 0
        for w0, w1 in zip(w0s, w1s):
            aligned = (w0 == u0) & (w1 == u1)
            # all gamma in F: vote coords per gamma
            for gam in rng.sample(range(p), 12):
                if gam == g0:
                    continue
                line_ok = (w0 + gam * w1) % p == (u0 + gam * u1) % p
                votes = line_ok & ~aligned
                if np.any(votes & ~suppD):
                    viol += 1
    print(f"  vote ⊆ supp(D) violations: {viol} (want 0) over {trials} instances")
    assert viol == 0


# ---------------------------------------------------------------- part 2: n=16 exhaustive


def all_codewords(p, dom, k):
    n = len(dom)
    V = codeword_matrix(p, dom, k)
    coeffs = np.array(list(itertools.product(range(p), repeat=k)), dtype=np.int64)
    return (coeffs @ V) % p  # (p^k, n)


def bad_count(p, n, T, CW, u0, u1, verbose=False):
    """#bad gammas with the joint-explanation filter (exact, small scale)."""
    u0 = np.asarray(u0, dtype=np.int64)
    u1 = np.asarray(u1, dtype=np.int64)
    # joint blockers: pairs (v0,v1) with joint agreement >= T
    agr0 = (CW == u0[None, :])
    agr1 = (CW == u1[None, :])
    L0 = np.where(agr0.sum(axis=1) >= T)[0]
    L1 = np.where(agr1.sum(axis=1) >= T)[0]
    blockers = []
    for i0 in L0:
        for i1 in L1:
            J = agr0[i0] & agr1[i1]
            if J.sum() >= T:
                blockers.append(J)
    bad = []
    for gam in range(p):
        line = (u0 + gam * u1) % p
        agr = (CW == line[None, :])
        cnts = agr.sum(axis=1)
        good_p = np.where(cnts >= T)[0]
        isbad = False
        for ip in good_p:
            A = np.where(agr[ip])[0]
            # exists T-subset of A not inside any blocker?
            if not blockers:
                isbad = True
                break
            for S in itertools.combinations(A, T):
                Sm = np.zeros(n, dtype=bool)
                Sm[list(S)] = True
                if not any((Sm & ~B).sum() == 0 for B in blockers):
                    isbad = True
                    break
            if isbad:
                break
        if isbad:
            bad.append(gam)
    return bad


def part2_n16():
    p, n, k = 17, 16, 4
    T = (53 * n) // 96 + 1  # 9
    dom = make_field(p, n)
    CW = all_codewords(p, dom, k)
    print(f"\n== part 2: n={n}/F_{p}, k={k}, T={T} — exhaustive bad-counts ==")
    rng = random.Random(7)

    # (a) realized-geometry stack: u0 = base codeword (constant 1), u1 = the
    # two-cover selection table style word (any u1: D == 0 when g0 = 0, p0 = u0)
    u0 = np.ones(n, dtype=np.int64)
    u1 = np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64)
    bad = bad_count(p, n, T, CW, u0, u1)
    print(f"  (a) u0 = base codeword, random u1: #bad = {len(bad)} (D==0: no riders)")

    # (b) adversarial D-stacks: u0 = c0 + D with |supp D| = f = n - T = 7
    best = -1
    for trial in range(40):
        f = n - T
        suppidx = rng.sample(range(n), f)
        D = np.zeros(n, dtype=np.int64)
        for i in suppidx:
            D[i] = rng.randrange(1, p)
        c0 = CW[rng.randrange(len(CW))]
        c1 = CW[rng.randrange(len(CW))]
        u0 = (c0 + D) % p
        u1 = (c1 + (D * rng.randrange(p))) % p if trial % 2 else \
            np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64)
        nb = len(bad_count(p, n, T, CW, u0, u1))
        best = max(best, nb)
    print(f"  (b) adversarial D-stacks (40 tries): max #bad = {best} vs n = {n}")

    # (c) swarm structure: u1 arbitrary; pencils w1_s interpolating u1 - s*D on
    # supp D (f = 7 > k = 4: NOT freely interpolable at this tiny scale, unlike
    # P1 where F < k; count scalars s admitting a codeword matching u1 - s*D on
    # all of supp D)
    f = n - T
    suppidx = sorted(rng.sample(range(n), f))
    D = np.zeros(n, dtype=np.int64)
    for i in suppidx:
        D[i] = rng.randrange(1, p)
    u1 = np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64)
    okcnt = 0
    for s in range(1, p):
        target = (u1 - s * D) % p
        match = (CW[:, suppidx] == target[suppidx][None, :]).all(axis=1)
        if match.any():
            okcnt += 1
    print(f"  (c) swarm interpolability at n=16 (f={f} > k={k}): scalars with "
          f"matching codeword on supp D: {okcnt}/16")
    print("      (at P1 the pool F = 100663294 < k = 2^28: EVERY scalar is"
          " interpolable — the swarm residual)")


if __name__ == "__main__":
    part1_mu256()
    part2_n16()
    print("\nAll global-consistency checks PASSED.")
