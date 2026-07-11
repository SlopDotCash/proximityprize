#!/usr/bin/env python3
"""Probe (#466, lane W15 part 4): the Johnson-to-doubled-Johnson window via two references.

Questions:
  Q1. Per-codeword appearance-multiplicity census at the campaign shape (17,16,4,9):
      how many scalars does each appearing codeword use on safe large-zero lines?
      (Secant prediction: multiplicity >= 2 forces agreement >= 2a-n with u0.)
  Q2. The TWO-BLOCK refuter: Z = B0 (n-a pts, u0=0) + B1 (n-a pts, u0=1), S = 2a-n
      support points with u0=0, u1=1_S.  Prediction: codewords 0 and 1 BOTH appear
      (at gamma=0 and gamma=1) => Lambda >= 2 => LargeZeroSafeLineListBudgeted(a, L=1)
      is FALSE at the campaign shape, where the part-2 probe's random lines showed
      Lambda = 1.  Verify safety + large-zero + exact Lambda and mcaEvent count.
  Q3. Singleton-block scaling: M singleton blocks with distinct constants (s = a-1
      shared support votes): how large can Lambda get in the window? (informs the
      residual's true value; the M=2 refuter alone kills L=1).

Deterministic.  Exit 0 iff Q2's construction verifies (Lambda >= 2, safe, large-zero).
"""

import itertools
import sys

import numpy as np

rng = np.random.default_rng(466_154)


def all_codewords(q, n, k):
    dom = np.arange(n)
    V = np.vstack([np.array([pow(int(x), j, q) for x in dom]) for j in range(k)])
    coeffs = np.array(list(itertools.product(range(q), repeat=k)))
    return (coeffs @ V) % q


def interp_explains(q, k, u1, A):
    xs = A[:k]
    ys = u1[xs]
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


def analyze(q, n, k, a, CW, u0, u1, label):
    Z = np.where(u1 % q == 0)[0]
    agrZ = (CW[:, Z] == u0[Z][None, :]).sum(axis=1) if len(Z) else np.zeros(len(CW), int)
    safe = agrZ.max(initial=0) < a
    large_zero = len(Z) >= a
    appearing = {}
    bad = 0
    for g in range(q):
        line = (u0 + g * u1) % q
        agr = (CW == line[None, :]).sum(axis=1)
        ws = np.where(agr >= a)[0]
        for w in ws:
            appearing.setdefault(int(w), []).append(g)
        fired = False
        for w in ws:
            A = np.where(CW[w] == line)[0]
            if not interp_explains(q, k, u1 % q, A):
                fired = True
                break
        bad += fired
    lam = len(appearing)
    mults = sorted(len(v) for v in appearing.values()) if appearing else []
    print(f"{label}: large_zero={large_zero} safe={safe} Lambda={lam} "
          f"multiplicities={mults} mcaEvent_count={bad} (n-a={n - a})")
    return large_zero, safe, lam, bad


def main():
    q, n, k, a = 17, 16, 4, 9
    CW = all_codewords(q, n, k)

    # Q2: the two-block refuter.  s = 2a-n = 2, blocks size n-a = 7.
    s = 2 * a - n
    B0 = np.arange(0, n - a)
    B1 = np.arange(n - a, 2 * (n - a))
    S = np.arange(2 * (n - a), n)
    assert len(S) == s
    u1 = np.zeros(n, dtype=int)
    u1[S] = 1
    u0 = np.zeros(n, dtype=int)
    u0[B1] = 1
    lz, safe, lam, bad = analyze(q, n, k, a, CW, u0, u1, "two-block refuter (17,16,4,9)")
    ok = lz and safe and lam >= 2

    # Q1: multiplicity census on random safe large-zero lines at the campaign shape
    print("\nmultiplicity census (random safe large-zero lines):")
    for _ in range(25):
        z = int(rng.integers(a, n))
        perm = rng.permutation(n)
        Zr, Sr = perm[:z], perm[z:]
        u1r = np.zeros(n, dtype=int)
        u1r[Sr] = rng.integers(1, q, size=len(Sr))
        u0r = rng.integers(0, q, size=n)
        w = CW[int(rng.integers(len(CW)))]
        anchor = rng.permutation(Zr)[:a - 1]
        u0r[anchor] = w[anchor]
        Zc = np.where(u1r % q == 0)[0]
        agrZ = (CW[:, Zc] == u0r[Zc][None, :]).sum(axis=1)
        if agrZ.max(initial=0) >= a or len(Zc) < a:
            continue
        analyze(q, n, k, a, CW, u0r % q, u1r % q, "  random")

    # Q3: singleton-block scaling — M singleton blocks, distinct random constants,
    # s = a-1 shared support votes at gamma = 0 for each constant c_j: c_j needs
    # c_j = u0 + gamma_j on S i.e. gamma_j = c_j - u0(i); set u0 = 0 on S so
    # gamma_j = c_j.  Block point i_j has u0 = c_j so constant c_j agrees there at
    # any gamma (u1=0), total agreement 1 + (a-1) = a.
    print("\nsingleton-block scaling (M blocks, s = a-1 support):")
    best = 0
    for M in range(a, n - (a - 1) + 1):  # need z = M >= a and M + (a-1) <= n
        consts = rng.permutation(q)[:M]
        u1m = np.zeros(n, dtype=int)
        u1m[M:M + a - 1] = 1
        u0m = np.zeros(n, dtype=int)
        u0m[:M] = consts
        # leftover coordinates beyond M+(a-1): direction zero, offset random-safe
        if M + a - 1 < n:
            u0m[M + a - 1:] = rng.integers(0, q, size=n - M - a + 1)
        lzm, safem, lamm, badm = analyze(q, n, k, a, CW, u0m, u1m, f"  M={M}")
        if lzm and safem:
            best = max(best, lamm)
    print(f"\nbest safe large-zero Lambda seen in window constructions: {best}")

    if ok:
        print("\nRESULT: two-block refuter VERIFIED — L_near = 1 is FALSE at the "
              "campaign shape (16,4,9); the part-2 probe's Lambda=1 was not worst-case")
        return 0
    print("\nRESULT: construction FAILED verification")
    return 1


if __name__ == "__main__":
    sys.exit(main())
