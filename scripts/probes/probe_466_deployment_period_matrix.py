#!/usr/bin/env python3
"""
probe_466_deployment_period_matrix.py -- Lane L6 companion #2: the EXACT integer
f x f cyclotomic-period-matrix certificate at the deployment primes (the dossier
Tier-3 formulation: "M = spectral radius of an f x f cyclotomic-period matrix").

THEORY (classical Gaussian-period ring, verified in self-tests below):
  Cosets C_j = g^j mu_n (j = 0..f-1), periods c_j = eta_{g^j} = sum_{x in C_j} e_p(x)
  ... wait, c_j = sum_{x in mu_n} e_p(g^j x) = sum_{y in C_j} e_p(y).  For the integer
  matrix  M_{jk} = #{t in C_j : 1 + t in C_k}  (t = -1 excluded; -1 in C_0 since n even):

      c_0 * c_j = sum_k M_{jk} c_k + n * [j = 0]
        (proof: c_0 c_j = sum_{x in mu_n, t in C_j} e_p(x(1+t)) after y = x t reindex;
         1 + t lands in C_k with multiplicity M_{jk}, or is 0 for t = -1, j = 0)

  Substituting  n*[j=0] = -n*[j=0] * sum_k c_k  (mass balance sum_k c_k = -1) gives the
  EIGENVALUE equation   P c = c_0 c   with   P = M - n e_0 1^T  (subtract n from row 0).
  Galois conjugation (zeta -> zeta^g) cyclically shifts the period vector, and P is
  rational-integer hence Galois-stable, so ALL f periods are eigenvalues of the SAME P:
      spectrum(P) = {c_0, ..., c_{f-1}}   and   M_wall = max |eig(P)| = spectral radius.

  EXACT INTEGER SELF-CHECKS of the counting:
      row sums:  sum_k M_{jk} = n - [j = 0]
      col sums:  sum_j M_{jk} = n - [k = 0]
      tr P      = sum c_j   = -1
      tr P^2    = sum c_j^2 = p - n
      tr P^3    = sum c_j^3 = p*T - n^2   (T from probe_466_deployment_s3_exact.py,
                                           computed INDEPENDENTLY there)

  So the certificate is: an exact integer matrix (O(p) exact uint64 arithmetic to
  build), whose spectrum is provably the period multiset, PINNED by four integer
  identities, with eigenvalues then computed at float64 + mpmath Rayleigh refinement
  (dps 40) -- and cross-checked against the wholly independent float64 cos-sum
  pipeline of probe_466_deployment_certificates.py.

COST: one pass over F_p^* (p-1 elements): k2 = log2(n) vectorized uint64 squarings
per element to get the coset index of 1+t.  ~5.4e10 uint64 modmuls per prime.
"""
import math
import os
import sys
import time

import numpy as np
import mpmath as mp

from probe_466_deployment_certificates import (
    P_BB, P_KB, is_prime, primitive_root, power_table, coset_values)

CHUNK = 1 << 22
CKPT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "_ckpt_466_deploy")


def period_matrix(p: int, n: int, g: int, verbose: bool = True) -> np.ndarray:
    """Exact integer M_{jk} = #{t in C_j : 1+t in C_k} via one chunked pass over
    t = g^i, i = 0..p-2 (coset(t) = i mod f); coset(w) from w^n in <g^n> (order f)."""
    f = (p - 1) // n
    k2 = n.bit_length() - 1
    assert n == 1 << k2
    # lookup table for the order-f subgroup: (g^n)^j -> j
    gn = pow(g, n, p)
    sub = np.empty(f, dtype=np.uint64)
    x = 1
    for j in range(f):
        sub[j] = x
        x = (x * gn) % p
    order = np.argsort(sub)
    sub_sorted = sub[order]
    inv_order = order.astype(np.int64)   # sub_sorted[i] = sub[inv_order[i]]
    L = CHUNK
    total = p - 1
    counts = np.zeros(f * f, dtype=np.int64)
    T = power_table(g, p, min(L, total))
    up = np.uint64(p)
    t0 = time.time()
    done = 0
    i0 = 0
    while i0 < total:
        take = min(L, total - i0)
        s = pow(g, i0, p)
        tvals = (T[:take] * np.uint64(s)) % up
        w = (tvals + np.uint64(1)) % up
        jj = (i0 + np.arange(take, dtype=np.int64)) % f
        keep = w != 0                      # t = -1 -> w = 0: excluded (one element)
        w = w[keep]
        jj = jj[keep]
        for _ in range(k2):                # w^n by k2 squarings
            w = (w * w) % up
        pos = np.searchsorted(sub_sorted, w)
        pos = np.clip(pos, 0, f - 1)
        assert np.all(sub_sorted[pos] == w), "coset lookup failure (w^n not in <g^n>)"
        kk = inv_order[pos]
        counts += np.bincount(jj * f + kk, minlength=f * f)
        i0 += take
        done += take
        if verbose and (i0 // L) % max(1, (total // L) // 4) == 0:
            el = time.time() - t0
            print(f"      pm pass {done/total*100:5.1f}%  ({el:.0f}s elapsed, "
                  f"{el / done * total:.0f}s est total)", flush=True)
    return counts.reshape(f, f)


def brute_period_matrix(p: int, n: int, g: int) -> np.ndarray:
    f = (p - 1) // n
    coset = {}
    x = 1
    for i in range(p - 1):
        coset[x] = i % f
        x = (x * g) % p
    M = np.zeros((f, f), dtype=np.int64)
    for t, j in coset.items():
        w = (1 + t) % p
        if w != 0:
            M[j, coset[w]] += 1
    return M


def rayleigh_refine(P: np.ndarray, lam0: float, v0: np.ndarray, dps: int = 40,
                    iters: int = 4):
    """Rayleigh-quotient inverse iteration in mpmath from a float64 seed."""
    f = P.shape[0]
    with mp.workdps(dps):
        A = mp.matrix(f, f)
        for i in range(f):
            for j in range(f):
                A[i, j] = int(P[i, j])
        lam = mp.mpf(lam0)
        v = mp.matrix([mp.mpf(float(t)) for t in v0])
        for _ in range(iters):
            B = A.copy()
            for i in range(f):
                B[i, i] -= lam
            try:
                v = mp.lu_solve(B, v)
            except ZeroDivisionError:
                break  # exactly converged
            nv = mp.sqrt(mp.fsum(t * t for t in v))
            v = v / nv
            Av = A * v
            lam = mp.fsum(v[i] * Av[i] for i in range(f))
        return lam


def analyze(name: str, p: int, n: int, s3_exact=None):
    f = (p - 1) // n
    g = primitive_root(p)
    print(f"\n-- {name}: p = {p}, n = 2^{n.bit_length()-1}, f = {f}, g = {g}",
          flush=True)
    t0 = time.time()
    os.makedirs(CKPT_DIR, exist_ok=True)
    ck = os.path.join(CKPT_DIR, f"pm_{name}.npy")
    if os.path.exists(ck):
        Mm = np.load(ck)
        assert Mm.shape == (f, f)
        print(f"    [checkpoint] loaded period matrix from {os.path.basename(ck)}",
              flush=True)
    else:
        Mm = period_matrix(p, n, g)
        np.save(ck, Mm)
    tbuild = time.time() - t0
    # exact integer checks
    rows_ok = all(int(Mm[j].sum()) == n - (1 if j == 0 else 0) for j in range(f))
    cols_ok = all(int(Mm[:, k].sum()) == n - (1 if k == 0 else 0) for k in range(f))
    P = Mm.copy()
    P[0, :] -= n
    tr1 = int(np.trace(P))
    tr2 = int(np.trace(P @ P))
    print(f"    build {tbuild:.0f}s;  row-sum check: {rows_ok}   col-sum check: {cols_ok}")
    print(f"    tr P   = {tr1}   (want -1: {'OK' if tr1 == -1 else '*** FAIL ***'})")
    print(f"    tr P^2 = {tr2}   (want p-n = {p - n}: "
          f"{'OK' if tr2 == p - n else '*** FAIL ***'})")
    # tr P^3 with exact python ints (avoid int64 overflow)
    Pobj = P.astype(object)
    tr3 = int(np.trace(Pobj @ Pobj @ Pobj))
    s3s = f"{tr3}"
    if s3_exact is not None:
        s3s += f"   (want p*T-n^2 = {s3_exact}: {'OK' if tr3 == s3_exact else '*** FAIL ***'})"
    print(f"    tr P^3 = {s3s}", flush=True)
    # eigenvalues
    ev = np.linalg.eigvals(P.astype(np.float64))
    maximag = float(np.abs(ev.imag).max())
    ev = np.sort(ev.real)
    jmax = int(np.argmax(np.abs(ev)))
    lam = ev[jmax]
    # refine spectral radius in mpmath (Rayleigh iteration, exact integer matrix)
    w2, V2 = np.linalg.eig(P.astype(np.float64))
    i2 = int(np.argmax(np.abs(w2)))
    lam_ref = rayleigh_refine(P, float(w2[i2].real), V2[:, i2].real, dps=40)
    print(f"    eig: max|imag| = {maximag:.2e} (want ~0; spectrum provably real)")
    print(f"    spectral radius (float64 eig) = {lam:.6f}")
    with mp.workdps(40):
        print(f"    spectral radius (mpmath Rayleigh, dps=40, EXACT integer matrix):")
        print(f"      M = {mp.nstr(abs(lam_ref), 30)}")
    return dict(name=name, p=p, n=n, f=f, P=P, ev=ev, lam=lam, lam_ref=lam_ref,
                tr_ok=(tr1 == -1 and tr2 == p - n), rows_ok=rows_ok, cols_ok=cols_ok)


def main():
    print("probe_466_deployment_period_matrix.py -- exact integer period-matrix "
          "certificate", flush=True)

    # ---- self-tests: brute force + float64 cos-sum cross-check
    print("\n== SELF-TESTS ==", flush=True)
    ok = True
    for p, n in ((641, 128), (61441, 1 << 12)):
        g = primitive_root(p)
        Mb = brute_period_matrix(p, n, g)
        Mv = period_matrix(p, n, g, verbose=False)
        same = bool(np.array_equal(Mb, Mv))
        P = Mv.copy()
        P[0, :] -= n
        ev = np.sort(np.linalg.eigvals(P.astype(np.float64)).real)
        c = np.sort(coset_values(p, n, g, verbose=False))
        dev = float(np.abs(ev - c).max())
        tr1, tr2 = int(np.trace(P)), int(np.trace(P @ P))
        print(f"  p={p} n={n} f={(p-1)//n}: brute==vectorized: {same};  "
              f"max|eig(P) - c_j| = {dev:.2e};  trP={tr1} trP^2={tr2} "
              f"(want -1, {p-n})")
        ok &= same and dev < 1e-8 and tr1 == -1 and tr2 == p - n
    print(f"  SELF-TESTS {'ALL PASS' if ok else '*** FAILURE ***'}", flush=True)
    if not ok:
        return 1

    # ---- read exact S3 from the companion probe output if available
    s3 = {}
    try:
        import re
        with open("_out_466_deployment_s3_exact.txt") as fh:
            for line in fh:
                m = re.search(r"(BabyBear|KoalaBear): T = \d+\s+S3_exact = "
                              r"p\*T - n\^2 = (-?\d+)", line)
                if m:
                    s3[m.group(1)] = int(m.group(2))
    except OSError:
        pass
    print(f"\n  exact S3 anchors loaded: {s3}", flush=True)

    res = []
    res.append(analyze("KoalaBear", P_KB, 1 << 24, s3.get("KoalaBear")))
    res.append(analyze("BabyBear", P_BB, 1 << 27, s3.get("BabyBear")))

    print("\n== EXACT-CERTIFICATE SUMMARY ==")
    for r in res:
        n, f, p = r['n'], r['f'], r['p']
        lam = abs(float(r['lam_ref']))
        C = lam / math.sqrt(n * math.log(p / n))
        print(f"  {r['name']}: integer checks "
              f"{'ALL OK' if r['tr_ok'] and r['rows_ok'] and r['cols_ok'] else 'FAIL'};"
              f"  M = {lam:.10f}  C = {C:.8f}  M/(2 sqrt n) = {lam/2/math.sqrt(n):.8f}")
        print(f"    full spectrum (sorted): "
              + " ".join(f"{v:.2f}" for v in r['ev'][:min(f, 16)])
              + (" ..." if f > 16 else ""))
    print("\ndone", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
