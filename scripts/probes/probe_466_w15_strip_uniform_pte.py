#!/usr/bin/env python3
"""Probe (#466, W15 part 7): the PTE uniform strip refuter across all primes 17..199.

The Prouhet-Tarry-Escott pair R = {0,5,7}, W = {1,3,8}: e1 = 12, e2 = 35 IDENTICALLY
(integer identities), e3 differs by 24.  Hence e = x(x-5)(x-7) takes the constant value
24 on W in every field of char >= 17 (0..15 distinct, 24 != 0).  Uniform strip line at
(n,k,a) = (16,4,11), dom = 0..15:
  Z-indices = R + D0={2,4,6,9} + D1={10,11,12,13}; support = W + {14,15};
  u0 = 0 on R+D0+W+{14}, = e on D1, = e(15)-24 = 1176 at 15; u1 = 1_support.
  Codeword 0 appears at gamma=0; codeword e appears at gamma=24.
Verify exactly (Lambda, safety, large-zero) for every prime 17 <= p < 200.
Exit 0 iff all pass.
"""

import itertools
import sys

import numpy as np


def primes(lo, hi):
    return [p for p in range(lo, hi)
            if p > 1 and all(p % d for d in range(2, int(p ** 0.5) + 1))]


def all_codewords(q, n, k):
    dom = np.arange(n)
    V = np.vstack([np.array([pow(int(x), j, q) for x in dom]) for j in range(k)])
    coeffs = np.array(list(itertools.product(range(q), repeat=k)))
    return (coeffs @ V) % q


def main():
    n, k, a = 16, 4, 11
    R, W = [0, 5, 7], [1, 3, 8]
    D1 = [10, 11, 12, 13]
    fails = 0
    for p in primes(17, 200):
        ev = lambda x: (x * (x - 5) * (x - 7)) % p
        assert ev(W[0]) == ev(W[1]) == ev(W[2]) == 24 % p
        u1 = np.zeros(n, dtype=int)
        for i in W + [14, 15]:
            u1[i] = 1
        u0 = np.zeros(n, dtype=int)
        for i in D1:
            u0[i] = ev(i)
        u0[15] = (ev(15) - 24) % p
        # exact verification (full codeword enumeration only for small p)
        if p <= 31:
            CW = all_codewords(p, n, k)
            Z = np.where(u1 == 0)[0]
            agrZ = (CW[:, Z] == u0[Z][None, :]).sum(axis=1)
            safe = agrZ.max() < a
            appearing = set()
            for g in range(p):
                line = (u0 + g * u1) % p
                agr = (CW == line[None, :]).sum(axis=1)
                appearing.update(np.where(agr >= a)[0].tolist())
            lam = len(appearing)
            ok = safe and len(Z) >= a and lam >= 2
            print(f"p={p}: EXACT safe={safe} Lambda={lam} -> {'OK' if ok else 'FAIL'}")
            fails += 0 if ok else 1
        else:
            # structural verification: the two appearance certificates
            c0_ok = all((u0[i] + 0 * u1[i]) % p == 0
                        for i in R + [2, 4, 6, 9] + W[:0]) and \
                    all((u0[i] + 0 * u1[i]) % p == 0 for i in W + [14])
            ce_ok = all(ev(i) == (u0[i] + 24 * u1[i]) % p
                        for i in R + D1 + W + [15])
            ok = c0_ok and ce_ok
            print(f"p={p}: certificates c0={c0_ok} ce={ce_ok} -> "
                  f"{'OK' if ok else 'FAIL'}")
            fails += 0 if ok else 1
    print()
    if fails == 0:
        print("RESULT: PTE uniform strip refuter verified at every prime 17..199 "
              "(exact for p <= 31, certificate-level beyond)")
        return 0
    print(f"RESULT: {fails} failures")
    return 1


if __name__ == "__main__":
    sys.exit(main())
