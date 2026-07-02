#!/usr/bin/env python3
"""
probe_466_deployment_s3_exact.py -- Lane L6 companion: EXACT integer anchor for the
deployment-prime certificates.

S3 = sum_j c_j^3 over the f dilation-coset values is a rational integer with an
O(n)-computable EXACT value:
    sum_{b in F_p} eta_b^3 = p * N3,  N3 = #{(x,y,z) in mu_n^3 : x+y+z = 0},
so  sum_{b != 0} eta_b^3 = p*N3 - n^3 = n * S3  and, normalizing x+y+z=0 by x
(dilation invariance of mu_n),  N3 = n * T  with
    T = #{a in mu_n : -1-a in mu_n}   =>   S3 = p*T - n^2.
Membership test: w in mu_n  <=>  w^n = 1 (n = 2^k, so k pure squarings, vectorized
uint64; products < p^2 < 2^62 for p < 2^31).

This turns the float64 S3 from the main certificate run into an EXACT cross-check:
|S3_float - (p*T - n^2)| measures the TRUE aggregate error of the c_j pipeline at
production scale (S3 ~ 1e13, so agreement to O(1) = 1e-13 relative).

Self-test: p = 61441 = 15*2^12+1 (T by brute force pow() vs vectorized) and p = 641.
"""
import math
import sys
import time

import numpy as np

from probe_466_deployment_certificates import (
    P_BB, P_KB, is_prime, primitive_root, power_table, coset_values)


def count_T(p: int, n: int, g: int, chunk: int = 1 << 22) -> int:
    """T = #{a in mu_n : (-1-a) mod p in mu_n}, mu_n = <g^f>, f = (p-1)/n."""
    f = (p - 1) // n
    h = pow(g, f, p)
    k2 = n.bit_length() - 1
    assert n == 1 << k2
    L = min(chunk, n)
    nch = n // L
    assert nch * L == n
    Tbl = power_table(h, p, L)
    pp = np.uint64(p)
    pm1 = np.uint64(p - 1)
    T = 0
    for t in range(nch):
        s = pow(h, t * L, p)
        a = (Tbl * np.uint64(s)) % pp
        # (-1 - a) mod p = p-1-a for a in [1, p-1] (values land in [0, p-2])
        w = pm1 - a
        # w == 0 <=> a == p-1 == -1: then -1-a = 0 not in mu_n; exclude via test w^n != 1
        for _ in range(k2):  # w^(2^k2) by squaring
            w = (w * w) % pp
        T += int(np.count_nonzero(w == np.uint64(1)))
    return T


def brute_T(p: int, n: int, g: int) -> int:
    f = (p - 1) // n
    h = pow(g, f, p)
    mu = set()
    x = 1
    for _ in range(n):
        mu.add(x)
        x = x * h % p
    return sum(1 for a in mu if (-1 - a) % p in mu)


def main():
    print("probe_466_deployment_s3_exact.py -- exact S3 = p*T - n^2 anchor", flush=True)
    # self-tests
    for p, n in ((641, 128), (61441, 1 << 12)):
        g = primitive_root(p)
        tb, tv = brute_T(p, n, g), count_T(p, n, g)
        c = coset_values(p, n, g, verbose=False)
        s3f = math.fsum((c ** 3).tolist())
        s3e = p * tv - n * n
        print(f"  [self] p={p}: T brute={tb} vect={tv} match={tb == tv}; "
              f"S3 float={s3f:.6f} exact={s3e} |dev|={abs(s3f - s3e):.2e}")
        assert tb == tv and abs(s3f - s3e) < 1e-6
    # production
    for name, p, n in (("BabyBear", P_BB, 1 << 27), ("KoalaBear", P_KB, 1 << 24)):
        assert is_prime(p)
        g = primitive_root(p)
        t0 = time.time()
        T = count_T(p, n, g)
        s3e = p * T - n * n
        print(f"  {name}: T = {T}   S3_exact = p*T - n^2 = {s3e}   "
              f"[{time.time() - t0:.0f}s]", flush=True)
    print("done")
    return 0


if __name__ == "__main__":
    sys.exit(main())
