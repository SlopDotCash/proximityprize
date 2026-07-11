#!/usr/bin/env python3
"""Probe (#466, lane W15 part 6): close the width-k trichotomy gap 2n < 3a < 2n+k.

Strip shapes: n=16,k=4 => a=11 (32 < 33 < 36); n=12,k=4 => a=9 (24 < 27 < 28).

The SECANT-PAIR construction (candidate strip refuter of L_near = 1):
  e = (x-r1)(x-r2)(x-r3) monic cubic with roots R; support votes shared on W where e is
  CONSTANT c* != 0 -- possible iff e1(R)=e1(W), e2(R)=e2(W) (then e - prod(x-w) = const).
  Layout (16,4,11): Z-indices = R(3) + D0(4) + D1(4), support = W(3) + {i0} + {i1}.
  u1 = 1 on support; u0 = 0 on R+D0, = e on D1, = 0 on W and i0, = e(i1)-c* at i1.
  Then codeword 0 appears at gamma=0 (agreement R+D0+W+i0 = 11) and codeword e appears
  at gamma=c* (agreement R (e=0=u0) + D1 (e=u0) + W (e=c*=u0+c*) + i1 = 11).
  Safety: 0 scores |R+D0| = 7 < 11; e scores |R|+|D1| = 7; generic <= 2(k-1) = 6.

Tasks:
  Q1. Find (R, W) symmetric coincidences over the 16-point domain in F17; assemble and
      verify the line exactly (Lambda, safety, large-zero); print the certificate data
      for the Lean instantiation.
  Q2. Hill-climb max Lambda at strip shapes (is Lambda >= 3 reachable?).
Deterministic.  Exit 0 iff the secant pair verifies at (17,16,4,11).
"""

import itertools
import sys

import numpy as np

rng = np.random.default_rng(466_156)


def all_codewords(q, n, k, dompts):
    V = np.vstack([np.array([pow(int(x), j, q) for x in dompts]) for j in range(k)])
    coeffs = np.array(list(itertools.product(range(q), repeat=k)))
    return (coeffs @ V) % q


def stats(q, n, k, a, CW, u0, u1):
    Z = np.where(u1 % q == 0)[0]
    agrZ = (CW[:, Z] == u0[Z][None, :]).sum(axis=1) if len(Z) else np.zeros(len(CW), int)
    safe = bool(agrZ.max(initial=0) < a)
    lz = bool(len(Z) >= a)
    appearing = set()
    for g in range(q):
        line = (u0 + g * u1) % q
        agr = (CW == line[None, :]).sum(axis=1)
        appearing.update(np.where(agr >= a)[0].tolist())
    return lz, safe, len(appearing)


def esym(pts, q):
    r1, r2, r3 = pts
    return ((r1 + r2 + r3) % q, (r1 * r2 + r1 * r3 + r2 * r3) % q,
            (r1 * r2 * r3) % q)


def main():
    q, n, k, a = 17, 16, 4, 11
    dompts = list(range(16))
    CW = all_codewords(q, n, k, dompts)

    # Q1: search symmetric coincidences
    found = None
    for R in itertools.combinations(dompts, 3):
        e1r, e2r, e3r = esym(R, q)
        for W in itertools.combinations([p for p in dompts if p not in R], 3):
            e1w, e2w, e3w = esym(W, q)
            if e1r == e1w and e2r == e2w and e3r != e3w:
                found = (R, W)
                break
        if found:
            break
    if not found:
        print("no symmetric coincidence found")
        return 1
    R, W = found
    rest = [p for p in dompts if p not in R and p not in W]
    D0, D1, i0, i1 = rest[:4], rest[4:8], rest[8], rest[9]
    ev = lambda x: ((x - R[0]) * (x - R[1]) * (x - R[2])) % q
    cstar = ev(W[0])
    assert all(ev(w) == cstar for w in W) and cstar != 0
    # assemble (indices == domain points here)
    u0 = np.zeros(n, dtype=int)
    u1 = np.zeros(n, dtype=int)
    for p in list(W) + [i0, i1]:
        u1[p] = 1
    for p in D1:
        u0[p] = ev(p)
    u0[i1] = (ev(i1) - cstar) % q
    lz, safe, lam = stats(q, n, k, a, CW, u0, u1)
    print(f"secant pair (17,16,4,11): R={R} W={W} D0={D0} D1={D1} i0={i0} i1={i1} "
          f"c*={cstar}")
    print(f"  e-values on D1: {[ev(p) for p in D1]}, e(i1)={ev(i1)}, "
          f"u0(i1)={u0[i1]}")
    print(f"  large_zero={lz} safe={safe} Lambda={lam}")
    ok = lz and safe and lam >= 2
    print(f"  u0 = {u0.tolist()}")
    print(f"  u1 = {u1.tolist()}")

    # Q2: hill-climbs at strip shapes
    for (qq, nn, kk, aa) in [(17, 16, 4, 11), (13, 12, 4, 9)]:
        CWs = all_codewords(qq, nn, kk, list(range(nn)))
        bestL = 0
        for z in (aa, aa + 1, min(nn - 1, aa + 3)):
            u1h = np.zeros(nn, dtype=int)
            u1h[z:] = 1
            cur = rng.integers(0, qq, size=nn)
            curL = -1
            for _ in range(250):
                cand = cur.copy()
                for _ in range(int(rng.integers(1, 3))):
                    cand[int(rng.integers(nn))] = int(rng.integers(qq))
                lzc, sc, lc = stats(qq, nn, kk, aa, CWs, cand, u1h)
                if lzc and sc and lc >= curL:
                    cur, curL = cand, lc
            bestL = max(bestL, curL)
        print(f"({qq},{nn},{kk},{aa}) strip hill-climb: best Lambda={bestL}")

    print()
    if ok:
        print("RESULT: strip secant-pair refuter VERIFIED at (17,16,4,11) — "
              "L_near = 1 is FALSE inside the width-k gap; trichotomy -> dichotomy")
        return 0
    print("RESULT: secant pair failed verification")
    return 1


if __name__ == "__main__":
    sys.exit(main())
