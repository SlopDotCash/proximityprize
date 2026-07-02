#!/usr/bin/env python3
"""probe_466_tsang_levels.py -- LANE L4(A) (#466): Tsang/Selberg level-splitting.

QUESTION.  Does prime-power "level-splitting" of the wraparound term capture any
structure past the diagonal?  D3 (arXiv:2606.10242, Frontier/_D3TsangHighMomentRangeGate.lean)
is range-gated: its diagonal-dominant hypothesis n^(2r) <= q is exactly 2r <= beta at
q = n^beta, i.e. constant depth.  The pre-registered KILL: level-splitting's hypothesis is
the already-closed diagonal regime; past it, the wraparound tail is level-SMOOTH and
splitting is vacuous.

SETUP.  mu_n subset F_p^*, |mu_n| = n, p == 1 mod n, p >= n^4 (beta = 4), lifts in [1, p-1].
For (x_1..x_r, y_1..y_r) in mu_n^(2r) with sum_i x_i == sum_i y_i (mod p), the LEVEL is the
integer k = (sum_Z x - sum_Z y)/p.  Level 0 = the relation holds over Z (contains the
diagonal D_r = permutation pairs, plus genuine Z-relations among the lifts); |k| >= 1 =
genuine wraparound.  By symmetry N_{-k} = N_k; we report k >= 0 (doubled where relevant).

EXACT ENERGY DECOMPOSITION BY LEVEL (the probe's engine).  Let f_r(s) = #{x in mu_n^r :
sum_Z x = s} (r-fold integer convolution), g(d) = sum_s f_r(s) f_r(s-d) (autocorrelation;
sum_d g(d) = n^(2r)).  Then N_k = g(kp), T_r = sum_k N_k = #solutions over F_p, and
   sum_{b in F_p} |eta_b|^(2r) = p * T_r   (verified against a direct eta computation).
Partition Z into windows W_k = [kp-(p-1)/2, kp+(p-1)/2] (length p each).  With the smooth
(equidistribution null) level mass ghat_k = (1/p) sum_{d in W_k} g(d), the EXACT identity
   E_r := sum_{b != 0} |eta_b|^(2r)  =  sum_k e_k,   e_k := p*N_k - sum_{d in W_k} g(d),
holds by construction (sum_k window sums = n^(2r) = DC term).  So:
  * ghat_k = the DC/smooth share of level k  (sum_k ghat_k = n^(2r)/p exactly);
  * rho_k  = N_k / ghat_k = per-level structure ratio (1 = pseudorandom level);
  * e_k    = the exact energy excess carried at level k  (sum = E_r).
"Level-1 dominance = the DC term" from the lane brief is exactly: N_k ~ ghat_k for k != 0,
i.e. the wraparound levels carry only their smooth/DC share and ALL genuine excess sits at
level 0 (the Z/diagonal regime).

MEASUREMENTS per (n, p, r), r in {2..6}  (2r <= beta=4 iff r <= 2: r=2 is the D3-admissible
diagonal depth, r=3..6 are past the gate; r=5,6 locate the wraparound onset):
  1. exact N_k, ghat_k, rho_k, e_k, level shares of T_r and of E_r;
  2. diagonal split at level 0: D_r (permutation pairs, exact multiset count) vs
     Z-nondiagonal N_0 - D_r;
  3. local anomaly z-score of g at d = kp vs neighbors g(kp+j), 1<=|j|<=200 (is the
     solution point special inside its own window?);
  4. cross-check: sum_b |eta_b|^(2r) (direct complex sum) == p*T_r, and
     sum_{b!=0}|eta_b|^2 == n(p-n) at r=1.

PRIMES (regime discipline): >= 2 primes per n, p >= n^4, proper subgroup (m = (p-1)/n > 1),
different v2(p-1) classes where cheap; the generalized-Fermat prime 65537 = 2^16+1 (known
resonant family) is included as a FLAGGED third data point at n=16, not as evidence.

DECISION RULE (pre-registered):
  * KILL (splitting vacuous): for all k != 0, rho_k ~ 1 (say within a few % and |z| <~ 3)
    and sum_{k!=0} |e_k| << E_r  ==> the wraparound tail is level-smooth, its aggregate is
    the DC term, any level-local bound = smooth counting = the aggregate W_r; the only
    structured level is 0 = the diagonal regime D3 already owns (2r <= beta).
  * LIVE: some k != 0 carries rho_k substantially > 1 / a large e_k share => level-local
    structure the aggregate hides; report it.

Output: scripts/probes/_out_466_tsang_levels.txt
"""
import math
import sys
import time
from collections import Counter
from itertools import combinations_with_replacement

import numpy as np


# ----------------------------------------------------------------------------- utilities
def is_prime(x: int) -> bool:
    if x < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if x % q == 0:
            return x == q
    d, s = x - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        v = pow(a, d, x)
        if v in (1, x - 1):
            continue
        for _ in range(s - 1):
            v = v * v % x
            if v == x - 1:
                break
        else:
            return False
    return True


def v2(x: int) -> int:
    v = 0
    while x % 2 == 0:
        x //= 2
        v += 1
    return v


def is_generalized_fermat(p: int) -> bool:
    """p = b^(2^s) + 1 for some b >= 2, s >= 1 (flagged resonant family)."""
    for s in range(1, 20):
        e = 1 << s
        b = round((p - 1) ** (1.0 / e))
        for bb in (b - 1, b, b + 1):
            if bb >= 2 and bb ** e + 1 == p:
                return True
    return False


def find_primes(n: int, count: int, skip_gf: bool = True):
    """Primes p == 1 mod n, p >= n^4, preferring distinct v2(p-1) classes."""
    out, seen_v2 = [], set()
    p = n ** 4 + 1
    p += (-(p - 1)) % n
    pool = []
    while len(pool) < 40:
        if is_prime(p) and (p - 1) // n > 1:
            if not (skip_gf and is_generalized_fermat(p)):
                pool.append(p)
        p += n
    for q in pool:  # prefer fresh v2 classes
        if v2(q - 1) not in seen_v2:
            out.append(q)
            seen_v2.add(v2(q - 1))
        if len(out) == count:
            return out
    for q in pool:
        if q not in out:
            out.append(q)
        if len(out) == count:
            return out
    return out


def subgroup_lifts(p: int, n: int):
    """Sorted integer lifts in [1, p-1] of the order-n subgroup of F_p^*."""
    assert (p - 1) % n == 0
    m = (p - 1) // n
    for a in range(2, p):
        b = pow(a, m, p)
        if b == 1:
            continue
        # order divides n = 2^mu here in all our cases; check order exactly n
        ok = True
        nn = n
        for q in set(_factor(n)):
            if pow(b, n // q, p) == 1:
                ok = False
                break
        if ok:
            elems = sorted(pow(b, j, p) for j in range(n))
            assert len(set(elems)) == n
            return elems
    raise RuntimeError("no order-n element found")


def _factor(n: int):
    fs, d = [], 2
    while n > 1:
        while n % d == 0:
            fs.append(d)
            n //= d
        d += 1
    return fs


def fft_convolve_int(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Exact integer convolution via FFT (values must stay << 2^53); verified integral."""
    L = len(a) + len(b) - 1
    N = 1 << (L - 1).bit_length()
    fa = np.fft.rfft(a.astype(np.float64), N)
    fb = np.fft.rfft(b.astype(np.float64), N)
    c = np.fft.irfft(fa * fb, N)[:L]
    ci = np.rint(c)
    err = float(np.max(np.abs(c - ci)))
    assert err < 1e-3, f"FFT convolution not integral: max dev {err}"
    return ci.astype(np.int64)


def diagonal_count(n: int, r: int) -> int:
    """D_r = #{(x,y) in mu^r x mu^r : y is a permutation of x} = sum_multiset perms^2."""
    tot = 0
    for ms in combinations_with_replacement(range(n), r):
        c = Counter(ms)
        perms = math.factorial(r)
        for v in c.values():
            perms //= math.factorial(v)
        tot += perms * perms
    return tot


# ----------------------------------------------------------------------------- per-run engine
def run(n: int, p: int, rmax: int, out):
    t0 = time.time()
    lifts = subgroup_lifts(p, n)
    m = (p - 1) // n
    gf = is_generalized_fermat(p)
    print(f"\n{'='*100}", file=out)
    print(f"n={n}  p={p}  m=(p-1)/n={m}  v2(p-1)={v2(p-1)}  beta=log_n p={math.log(p, n):.3f}"
          f"  {'** GENERALIZED-FERMAT (resonant family, FLAGGED) **' if gf else ''}", file=out)

    # eta_b for all b (float check channel)
    bs = np.arange(p, dtype=np.float64)
    ang = 2.0 * math.pi / p
    eta = np.zeros(p, dtype=np.complex128)
    for x in lifts:
        eta += np.exp(1j * ang * ((bs * x) % p))
    absq = np.abs(eta) ** 2
    par = float(np.sum(absq[1:]))
    print(f"  Parseval check: sum_(b!=0)|eta|^2 = {par:.6f}  vs n(p-n) = {n*(p-n)}"
          f"  (rel err {abs(par - n*(p-n))/(n*(p-n)):.2e})", file=out)
    M = float(np.sqrt(np.max(absq[1:])))
    print(f"  M = max|eta_b| = {M:.4f}   sqrt(n)= {math.sqrt(n):.3f}"
          f"   sqrt(n log(p/n)) = {math.sqrt(n*math.log(p/n)):.3f}", file=out)

    # r-fold integer convolutions of the lift indicator
    base = np.zeros(p, dtype=np.int64)
    for x in lifts:
        base[x] = 1
    f = {1: base}
    for r in range(2, rmax + 1):
        f[r] = fft_convolve_int(f[r - 1], base)

    half = (p - 1) // 2
    for r in range(2, rmax + 1):
        fr = f[r]
        assert int(fr.sum()) == n ** r
        L = len(fr)
        C = np.zeros(L + 1, dtype=np.int64)  # C[i] = sum fr[:i]
        np.cumsum(fr, out=C[1:])

        def g_at(d: int) -> int:
            d = abs(d)
            if d >= L:
                return 0
            return int(np.dot(fr[d:], fr[:L - d]))

        def window_sum(k: int) -> int:
            # sum_{d in [k*p-half, k*p+half]} g(d), g(d)=sum_t fr[t]*fr[t-d]
            a, b = k * p - half, k * p + half
            lo = np.clip(np.arange(L) - b, 0, L)      # index of first term t-d, d<=b -> u>=t-b
            hi = np.clip(np.arange(L) - a + 1, 0, L)  # u <= t-a
            return int(np.dot(fr, (C[hi] - C[lo])))

        D_r = diagonal_count(n, r)
        rows, Nk, WS = [], {}, {}
        for k in range(0, r + 1):
            Nk[k] = g_at(k * p)
            WS[k] = window_sum(k)
        T_r = Nk[0] + 2 * sum(Nk[k] for k in range(1, r + 1))
        total_win = WS[0] + 2 * sum(WS[k] for k in range(1, r + 1))
        assert total_win == n ** (2 * r), (total_win, n ** (2 * r))
        E_r_exact = p * T_r - n ** (2 * r)
        E_r_float = float(np.sum(absq[1:] ** r))
        relerr = abs(E_r_float - E_r_exact) / max(E_r_exact, 1)
        wick = math.factorial(r) * (n ** r) * (p - 1)  # (p-1) * r! * sigma^(2r), sigma^2 ~ n

        print(f"\n  --- r = {r}   (2r <= beta={math.log(p,n):.2f}? "
              f"{'YES - D3 diagonal-admissible depth' if 2*r <= math.log(p,n)+1e-9 else 'NO - past the D3 gate'})",
              file=out)
        print(f"  T_r = {T_r}  (solutions over F_p);  D_r (diagonal) = {D_r};"
              f"  level-0 Z-nondiagonal = {Nk[0] - D_r}", file=out)
        print(f"  E_r = sum_(b!=0)|eta|^(2r) = {E_r_exact}  (float check rel err {relerr:.2e});"
              f"  Wick ref (p-1)r!n^r = {wick:.3e};  E_r/Wick = {E_r_exact/wick:.4f}", file=out)
        print(f"  {'k':>2} {'N_k':>14} {'shareT':>8} {'ghat_k':>14} {'rho_k=N/ghat':>12} "
              f"{'e_k=pN-WS':>16} {'e_k/E_r':>9} {'z(g@kp)':>8}", file=out)
        e_sum = 0
        for k in range(0, r + 1):
            mult = 1 if k == 0 else 2
            ghat = WS[k] / p
            e_k = p * Nk[k] - WS[k]
            e_sum += mult * e_k
            # local z-score of g at kp among neighbors
            rad = min(200, half - 1)
            nb = np.array([g_at(k * p + j) for j in range(-rad, rad + 1) if j != 0], dtype=np.float64)
            mu_nb, sd_nb = float(nb.mean()), float(nb.std())
            z = (Nk[k] - mu_nb) / sd_nb if sd_nb > 0 else float('inf') if Nk[k] != mu_nb else 0.0
            rho = Nk[k] / ghat if ghat > 0 else float('nan')
            print(f"  {k:>2} {Nk[k]:>14} {mult*Nk[k]/T_r:>8.4f} {ghat:>14.2f} {rho:>12.4f} "
                  f"{e_k:>16} {mult*e_k/E_r_exact:>9.4f} {z:>8.2f}", file=out)
        assert e_sum == E_r_exact, (e_sum, E_r_exact)
        share_k0 = (p * Nk[0] - WS[0]) / E_r_exact
        share_wrap = 1.0 - share_k0
        rho_max = max(abs(Nk[k] / (WS[k] / p) - 1.0) for k in range(1, r + 1) if WS[k] > 0)
        print(f"  LEVEL VERDICT r={r}: level-0 excess share = {share_k0:+.4f}; "
              f"all wraparound levels combined = {share_wrap:+.4f} of E_r; "
              f"max_k!=0 |rho_k - 1| = {rho_max:.4f}", file=out)
    print(f"  [runtime {time.time()-t0:.1f}s]", file=out)


def main():
    with open("scripts/probes/_out_466_tsang_levels.txt", "w") as out:
        print("LANE L4(A) #466 -- Tsang/Selberg level-splitting of the wraparound term", file=out)
        print(f"numpy {np.__version__}; deterministic (no RNG). Levels: k=(sum_Z x - sum_Z y)/p;"
              " N_-k = N_k (symmetry), k>=1 rows doubled in shares.", file=out)
        runs = []
        for p in find_primes(8, 2):
            runs.append((8, p))
        gen16 = find_primes(16, 2)
        for p in gen16:
            runs.append((16, p))
        if is_prime(65537):
            runs.append((16, 65537))  # flagged generalized-Fermat contrast point
        for n, p in runs:
            # rmax=6: n^(2r) <= 16^12 = 2.8e14 keeps every exact int64 dot safe;
            # r=5,6 locate the wraparound ONSET past the empty r<=4 range.
            run(n, p, rmax=6, out=out)
        print(f"\n{'='*100}\nSee LEVEL VERDICT lines per (p, r). Aggregate verdict in kb note.", file=out)
    print("done -> scripts/probes/_out_466_tsang_levels.txt")


if __name__ == "__main__":
    main()
