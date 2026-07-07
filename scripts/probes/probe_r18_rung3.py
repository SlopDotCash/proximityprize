#!/usr/bin/env python3
"""R18 RUNG3 probe: rung-3 (sixth moment) of the diagonal-subtracted incidence tower.

S_3^D = sum_{s0 notin D} |I_H(s0)|^6,  D = {0} u mu_n.
Wick target: S_3^D <= q * 15 * Sigma^3, Sigma = sum_{b in H} |eta_b|^2.

Also computes:
 - exact identity check: sum_{s0 in F_p} |I|^6 = p * E3eta(H)  (via direct FFT both sides is
   circular; instead we check the DIAGONAL sextuple closed form and diag exactness)
 - diagonal (matched-multiset) sextuple mass: p*(6 Sigma^3 - 9 Sigma Q2 + 4 Q3),
   Q_k = sum_{b in H} |eta_b|^{2k}  -> fraction of Wick (predicted -> 6/15 = 2/5)
 - all-equal-coset slice: p * E3(mu_n) * sum_{cosets t} |eta_t|^6
 - deleted credit and residual non-matched mass fractions relative to Wick
 - I_H(s0 in mu_n) = Sigma/n exact check; I_H(0) = conj(sum eta) check
 - deficit: needed extra saving factor n^3/sqrt(p)
"""
import numpy as np
from sympy import isprime, primitive_root

def cells():
    # (n, m=deg, beta targets) choose p = 1 mod lcm stuff with m | (p-1)/n
    for n in (8, 16, 32):
        for m in (2, 4):
            for beta in (2.0, 2.5, 3.0, 3.5, 4.0):
                target = int(round(n ** beta))
                # p ≡ 1 mod n*m ensures mu_n subset H=index-m subgroup? need m | (p-1)/n
                mod = n * m
                p = target - (target % mod) + 1
                while not (isprime(p) and (p - 1) % (n * m) == 0):
                    p += mod
                if p < 2 * n * m + 1:
                    continue
                yield n, m, beta, p

def run_cell(n, m, beta, p):
    g = primitive_root(p)
    # mu_n
    gn = pow(g, (p - 1) // n, p)
    mu = np.array(sorted({pow(gn, k, p) for k in range(n)}), dtype=np.int64)
    assert len(mu) == n
    # H = index-m subgroup
    gm = pow(g, m, p)
    H = set()
    x = 1
    for _ in range((p - 1) // m):
        H.add(x); x = x * gm % p
    H = np.array(sorted(H), dtype=np.int64)
    assert len(H) == (p - 1) // m
    assert set(mu).issubset(set(H.tolist()))
    # eta_b for all b via FFT: eta = FFT of indicator of mu with e^{+2pi i b x/p}
    ind = np.zeros(p)
    ind[mu] = 1.0
    # sum_x ind[x] e^{2pi i b x / p} = p * ifft(ind)[b]
    eta = np.fft.ifft(ind) * p
    # I_H(s0) = sum_{b in H} conj(eta_b) e^{2pi i b s0/p}
    f = np.zeros(p, dtype=complex)
    f[H] = np.conj(eta[H])
    I = np.fft.ifft(f) * p
    Sigma = float(np.sum(np.abs(eta[H]) ** 2))
    Q2 = float(np.sum(np.abs(eta[H]) ** 4))
    Q3 = float(np.sum(np.abs(eta[H]) ** 6))
    # checks
    diag_err = max(abs(I[s] - Sigma / n) for s in mu.tolist())
    zero_err = abs(I[0] - np.conj(np.sum(eta[H])))
    A6 = np.abs(I) ** 6
    S3_full = float(np.sum(A6))
    deleted = float(A6[0]) + float(np.sum(A6[mu]))
    S3_D = S3_full - deleted
    wick = p * 15.0 * Sigma ** 3
    ratio = S3_D / wick
    # diagonal sextuple closed form (matched b-multisets)
    diag_sext = p * (6 * Sigma ** 3 - 9 * Sigma * Q2 + 4 * Q3)
    # all-equal-coset slice: cosets of mu_n in H
    # coset reps: H/mu_n; eta constant on cosets
    coset_reps = []
    seen = set()
    for b in H.tolist():
        if b not in seen:
            coset_reps.append(b)
            for u in mu.tolist():
                seen.add(b * u % p)
    E3mu = E3_mu(mu, p)
    allequal = p * E3mu * float(sum(abs(eta[t]) ** 6 for t in coset_reps))
    fullfrac = S3_full / wick
    deletedfrac = deleted / wick
    crossfrac = (S3_full - diag_sext) / wick
    cross_deletedfrac = (S3_D - diag_sext) / wick
    M = float(np.max(np.abs(eta[1:])))
    deficit = n ** 3 / np.sqrt(p)
    return dict(ratio=ratio, diagfrac=diag_sext / wick, allequalfrac=allequal / wick,
                fullfrac=fullfrac, deletedfrac=deletedfrac, crossfrac=crossfrac,
                cross_deletedfrac=cross_deletedfrac,
                S3D=S3_D, wick=wick, diag_err=diag_err, zero_err=zero_err,
                E3mu=E3mu, E3wick=E3mu / (6 * n ** 3), M=M, deficit=deficit,
                ncoset=len(coset_reps))

def E3_mu(mu, p):
    # E3(mu_n) = #{x in mu^6 : x1+x2+x3 = x4+x5+x6} via convolution counts
    from collections import Counter
    c2 = Counter()
    for a in mu.tolist():
        for b in mu.tolist():
            c2[(a + b) % p] += 1
    c3 = Counter()
    for s, cnt in c2.items():
        for a in mu.tolist():
            c3[(s + a) % p] += cnt
    return sum(v * v for v in c3.values())

if __name__ == "__main__":
    print(f"{'n':>3} {'m':>2} {'beta':>4} {'p':>9} {'S3D/W':>8} {'full/W':>8} "
          f"{'diag/W':>8} {'cross/W':>8} {'crossD/W':>9} {'del/W':>8} {'alleq/W':>9} "
          f"{'E3/6n^3':>8} {'n^3/sqrtp':>10} {'diagerr':>8} {'zeroerr':>8}")
    for n, m, beta, p in cells():
        if p > 2_500_000:
            print(f"{n:>3} {m:>2} {beta:>4} {p:>9}  SKIP(large)")
            continue
        r = run_cell(n, m, beta, p)
        print(f"{n:>3} {m:>2} {beta:>4} {p:>9} {r['ratio']:>8.4f} {r['fullfrac']:>8.4f} "
              f"{r['diagfrac']:>8.4f} {r['crossfrac']:>8.4f} {r['cross_deletedfrac']:>9.4f} "
              f"{r['deletedfrac']:>8.2e} "
              f"{r['allequalfrac']:>9.2e} {r['E3wick']:>8.4f} {r['deficit']:>10.2f} "
              f"{r['diag_err']:>8.1e} {r['zero_err']:>8.1e}")
